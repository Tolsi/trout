use core::{marker::PhantomData, ops::Deref};
use std::{
  sync::Arc,
  collections::{HashSet, HashMap},
};

use zeroize::Zeroizing;
use rand_core::{RngCore, CryptoRng};

use group::ff::{Field, PrimeField, PrimeFieldBits};
use class_groups::{Element, Table, ClassGroup};

use dkg::Participant;

use crate::{UnsignedInteger, Evrf, Parameters, SetupView, Setup};

/// The 2-round signing protocol.
pub struct SigningProtocol<P: Parameters, CG: Element>(PhantomData<(P, CG)>);

/// A view of someone observing the signing protocol.
pub struct Observing<P: Parameters, CG: Element> {
  setup: Arc<SetupView<P, CG>>,
  session_id: [u8; 32],
  nonce_commitment: Option<P::E>,
  K_tilde: Option<(CG, CG)>,
  U: Option<CG>,
  accumulated: HashSet<Participant>,
  faulty: HashSet<Participant>,
  pending: HashMap<Participant, Vec<u8>>,
}

/// A view of someone participating in the signing protocol.
pub struct Participating<P: Parameters, CG: Element> {
  setup: Arc<Setup<P, CG>>,
  alpha_i: Zeroizing<UnsignedInteger>,
  beta_i: Zeroizing<UnsignedInteger>,
  u_i: Zeroizing<<P as Parameters>::F>,
  observing: Observing<P, CG>,
}

/// A view of the first round of the signing protocol.
impl<P: Parameters, CG: Element> SigningProtocol<P, CG> {
  /// Participate in the 2-round signing protocol.
  ///
  /// Returns the participant's message and the view necessary to further participate.
  ///
  /// `session_id` must be carefully chosen. The simplest choice is the hash of the view of the
  /// setup, the signing set, and the message. This is a secure choice of `session_id`. Reuse of
  /// `session_id` across setups/signing sets/messages will leak the private key.
  ///
  /// If delayed specification of signing set is desired, then `session_id` should be some
  /// derivative of `(setup view, message, attempt number)` where only a single signing set will be
  /// specified and moved forward with per attempt.
  ///
  /// If delayed specification of the message is desired (and optionally also the signing set),
  /// then this should be some derivative of a global index for the setup where each index will
  /// only be used for a single message (and signing set).
  ///
  /// Delayed specification of the signing set/message was not proven secure in the paper.
  /// Post-specification of the signing set allows an adversary to bias the nonce via choice of
  /// set (as different sets will produce distinct nonces). Post-specification of the message is
  /// known to enable attacks on certain multisignature scheme (https://eprint.iacr.org/2024/437),
  /// even with simulatable nonces.
  ///
  /// There is supporting evidence that the ROS problem is hard for ECDSA in
  /// https://eprint.iacr.org/2021/1449. That would imply post-specification of signing set/message
  /// may be without issue, so long as a session ID is never reused.
  ///
  /// This code defers the derivation of session ID, and specification timeline, to the caller in
  /// order to enable these features if proven secure. The caller is trusted with the important,
  /// critical, and difficult responsibility of handling this securely. The only endorsed solution
  /// is the hash of the view of the setup, the signing set, and the message.
  #[must_use]
  pub fn participate(
    rng: &mut (impl RngCore + CryptoRng),
    setup: Arc<Setup<P, CG>>,
    session_id: [u8; 32],
  ) -> (Participating<P, CG>, Vec<u8>) {
    let mut message = Vec::with_capacity(32 + 768 + (3 * 384));

    let (alpha_i, beta_i, u_i) = {
      let nonce_i =
        P::Evrf::prove(&mut *rng, setup.evrf_setup(), session_id, &mut message).unwrap();

      let alpha_i = Zeroizing::new(UnsignedInteger::random(
        setup.view().class_group().unknown_order_bound() + 128,
        &mut *rng,
      ));
      let alpha_i_bytes = Zeroizing::new(alpha_i.to_be_bytes());
      let K_tilde_i = (
        CG::mul(setup.view().G(), &alpha_i_bytes),
        CG::mul(setup.view().Y(), &alpha_i_bytes).add(&CG::mul(
          setup.view().class_group().f(),
          &Zeroizing::new(crate::be_bytes(nonce_i.deref())),
        )),
      );

      let beta_i = Zeroizing::new(UnsignedInteger::random(
        setup.view().class_group().unknown_order_bound() + 128,
        &mut *rng,
      ));
      let beta_i_bytes = Zeroizing::new(beta_i.to_be_bytes());
      let u_i = Zeroizing::new(<P as Parameters>::F::random(&mut *rng));
      let U_i = CG::mul(setup.view().G(), &beta_i_bytes)
        .add(&CG::mul(setup.view().Y(), &Zeroizing::new(crate::be_bytes(u_i.deref()))));

      K_tilde_i.0.compress(&mut message).unwrap();
      K_tilde_i.1.compress(&mut message).unwrap();

      U_i.compress(&mut message).unwrap();

      (alpha_i, beta_i, u_i)
    };

    // Create the view of the protocol
    let mut observing = Self::observe(setup.view().clone(), session_id);
    // Because this is the view if we're participating, accumulate our own participation
    match observing.accumulate(setup.i(), message.clone()) {
      Ready::Ready(_) => unreachable!("t == 1 barred at setup"),
      Ready::NotReady((observing_, error)) => {
        observing = observing_;
        assert!(error.is_none());
      }
    }

    (Participating { setup, alpha_i, beta_i, u_i, observing }, message)
  }
  /// Observe the execution of the 2-round signing protocol.
  #[must_use]
  pub fn observe(setup: Arc<SetupView<P, CG>>, session_id: [u8; 32]) -> Observing<P, CG> {
    Observing {
      setup,
      session_id,
      nonce_commitment: None,
      K_tilde: None,
      U: None,
      accumulated: HashSet::new(),
      faulty: HashSet::new(),
      pending: HashMap::new(),
    }
  }
}

/// An error from the first round of the signing protocol.
pub enum RoundOneError {
  /// The participant index was invalid.
  InvalidParticipant,
  /// This participant has already participated.
  AlreadyParticipated,
  /// The following participants were faulty.
  Faults(Vec<Participant>),
}

/// An enum representing an object not ready or now ready.
#[must_use]
pub enum Ready<NotReady, Ready> {
  /// Not ready.
  NotReady(NotReady),
  /// Ready.
  Ready(Ready),
}

/// The view of someone who has observed the first round and can observe signature shares once the
/// message is specified.
// "signature shares" is loosely defined here as the round two messages.
pub struct ObservingSigning<P: Parameters, CG: Element> {
  setup: Arc<SetupView<P, CG>>,
  nonce_commitment: P::E,
  K_tilde: (CG, CG),
  U: CG,
  // Map from Participant index to their lagrange interpolation factor
  signing_set: HashMap<Participant, P::F>,
}

/// The view of someone who has observed the first round and can now produce a signature share.
pub struct Signing<P: Parameters, CG: Element> {
  setup: Arc<Setup<P, CG>>,
  alpha_i: Zeroizing<UnsignedInteger>,
  beta_i: Zeroizing<UnsignedInteger>,
  u_i: Zeroizing<<P as Parameters>::F>,
  observing_signing: ObservingSigning<P, CG>,
}

impl<P: Parameters, CG: Element> Observing<P, CG> {
  /// Accumulate a message from a participant.
  ///
  /// Please see `Participating::accumulate` for more information. This method matches its
  /// behavior.
  pub fn accumulate(
    mut self,
    participant: Participant,
    message: Vec<u8>,
  ) -> Ready<(Self, Option<RoundOneError>), ObservingSigning<P, CG>> {
    // Verify the participant index
    if usize::from(u16::from(participant)) > self.setup.n() {
      return Ready::NotReady((self, Some(RoundOneError::InvalidParticipant)));
    }
    // Verify they haven't already participated
    if self.accumulated.contains(&participant) ||
      self.faulty.contains(&participant) ||
      self.pending.contains_key(&participant)
    {
      return Ready::NotReady((self, Some(RoundOneError::AlreadyParticipated)));
    }
    // Mark their message as pending
    self.pending.insert(participant, message);

    // If we're now at the threshold, batch verify the pending messages and move them to
    // accumulated
    let mut faulty = HashSet::new();
    if (self.accumulated.len() + self.pending.len()) == usize::from(self.setup.t()) {
      let mut messages = HashMap::with_capacity(self.pending.len());

      // Prepare the batch verifications
      let mut evrf_batch_verifier = P::Evrf::batch_verifier();
      for (participant, message) in self.pending.drain() {
        let mut message = message.as_slice();
        let Ok(nonce_commitment) = P::Evrf::queue_verification(
          &mut evrf_batch_verifier,
          participant,
          self.setup.evrf_setup(&participant).unwrap(),
          self.session_id,
          &mut message,
        ) else {
          faulty.insert(participant);
          continue;
        };
        let Ok(K_tilde_i_0) = self.setup.class_group().decompress_p(&mut message) else {
          faulty.insert(participant);
          continue;
        };
        let Ok(K_tilde_i_1) = self.setup.class_group().decompress_p(&mut message) else {
          faulty.insert(participant);
          continue;
        };
        let Ok(U_i) = self.setup.class_group().decompress_p(&mut message) else {
          faulty.insert(participant);
          continue;
        };
        messages.insert(participant, (nonce_commitment, K_tilde_i_0, K_tilde_i_1, U_i));
      }

      // Perform the batch verifications
      match P::Evrf::verify(evrf_batch_verifier) {
        Ok(()) => {}
        Err(faults) => {
          for fault in faults {
            faulty.insert(fault);
          }
        }
      }

      // Move forward with the valid messages
      for (participant, (nonce_commitment, K_tilde_i_0, K_tilde_i_1, U_i)) in messages {
        if faulty.contains(&participant) {
          continue;
        }

        self.nonce_commitment = self
          .nonce_commitment
          .map(|existing| existing + nonce_commitment)
          .or(Some(nonce_commitment));
        self.K_tilde = self
          .K_tilde
          .map(|K_tilde| (K_tilde.0.add(&K_tilde_i_0), K_tilde.1.add(&K_tilde_i_1)))
          .or(Some((K_tilde_i_0, K_tilde_i_1)));
        self.U = self.U.map(|existing| existing.add(&U_i)).or(Some(U_i));
        self.accumulated.insert(participant);
      }
    }

    // Fold the faulty participants from this verification run into our state
    for faulty in &faulty {
      self.faulty.insert(*faulty);
    }

    // If we've accumulated `t` messages, move to round two
    if self.accumulated.len() == usize::from(self.setup.t()) {
      // Since we run upon `t` potentially valid messages, `t` valid should mean none were invalid
      debug_assert!(faulty.is_empty());
      let signing_set = self.accumulated.into_iter().collect::<Vec<_>>();
      return Ready::Ready(ObservingSigning {
        setup: self.setup,
        nonce_commitment: self.nonce_commitment.unwrap(),
        K_tilde: self.K_tilde.unwrap(),
        U: self.U.unwrap(),
        signing_set: signing_set
          .iter()
          .map(|participant| (*participant, dkg::lagrange::<P::F>(*participant, &signing_set)))
          .collect(),
      });
    }

    Ready::NotReady((
      self,
      if faulty.is_empty() {
        None
      } else {
        Some(RoundOneError::Faults(faulty.into_iter().collect()))
      },
    ))
  }
}

impl<P: Parameters, CG: Element> Participating<P, CG> {
  /// Accumulate a message from a participant.
  ///
  /// This message is expected to be authenticated as originating from the sender by the caller.
  ///
  /// The signing set is considered the first `t` signers who provide valid messages. If the
  /// signing set was determined before any participation, the caller is expected to only
  /// accumulate messages from participants within the signing set.
  ///
  /// This will return itself and still be usable to perform accumulation even if the message is
  /// invalid. This flow enables determining the signing set to be the first `t` signers who
  /// publish valid messages. Such determination would be delayed specification of the signing set
  /// and is accordingly subject to the long commentary present on `SigningProtocol::participate`.
  pub fn accumulate(
    mut self,
    participant: Participant,
    message: Vec<u8>,
  ) -> Ready<(Self, Option<RoundOneError>), Signing<P, CG>> {
    match self.observing.accumulate(participant, message) {
      Ready::Ready(observing_signing) => Ready::Ready(Signing {
        setup: self.setup,
        alpha_i: self.alpha_i,
        beta_i: self.beta_i,
        u_i: self.u_i,
        observing_signing,
      }),
      Ready::NotReady((observing, error)) => {
        self.observing = observing;
        Ready::NotReady((self, error))
      }
    }
  }
}

/// The view of someone aggregating signature shares to obtain the resulting signature.
pub struct Aggregating<P: Parameters, CG: Element> {
  observing_signing: ObservingSigning<P, CG>,
  x_coordinate: <P as Parameters>::F,
  message_hash: <P as Parameters>::F,
  Z_tilde: (CG, CG),

  accumulated: HashSet<Participant>,
  faulty: HashSet<Participant>,
  pending: HashMap<Participant, Vec<u8>>,

  ZU: Option<CG>,
  KU: Option<CG>,
}

impl<P: Parameters, CG: Element> ObservingSigning<P, CG> {
  /// Observe the signing of the following message.
  #[must_use]
  pub fn message(self, message: &[u8]) -> Aggregating<P, CG> {
    let x_coordinate = P::x_coordinate(&self.nonce_commitment);
    let message_hash = P::hash_message(message);

    let mut C_tilde: Option<(CG, CG)> = None;
    for (participant, lagrange) in &self.signing_set {
      let share_ciphertext = self
        .setup
        .share_ciphertext(participant)
        .expect("didn't have the share ciphertext for a participant");
      let lagrange_bytes = crate::be_bytes(lagrange);
      let share_ciphertext = (
        CG::mul(&share_ciphertext.0, &lagrange_bytes),
        CG::mul(&share_ciphertext.1, &lagrange_bytes),
      );
      C_tilde = C_tilde
        .map(|existing| (existing.0.add(&share_ciphertext.0), existing.1.add(&share_ciphertext.1)))
        .or_else(|| Some(share_ciphertext.clone()));
    }
    let C_tilde = C_tilde.unwrap();

    let x_coordinate_bytes = crate::be_bytes(&x_coordinate);
    let r_C_tilde = (
      CG::mul(
        &Table::new_for_scalar_bits(
          <P as Parameters>::F::NUM_BITS.try_into().unwrap(),
          self.setup.class_group().identity_p().clone(),
          C_tilde.0,
        ),
        &x_coordinate_bytes,
      ),
      // This table is only used once and SHOULD use `new_for_scalar_bits`
      // TODO: Add `message_hash * r**-1` so we can build *and reuse* this table? The ECDSA scalar
      // inversion is likely cheaper than this ad-hoc table which is the most efficient way to do
      // any scaling of a class-group element
      CG::mul(
        &Table::new_for_scalar_bits(
          <P as Parameters>::F::NUM_BITS.try_into().unwrap(),
          self.setup.class_group().identity_p().clone(),
          C_tilde.1,
        ),
        &x_coordinate_bytes,
      ),
    );
    let Z_tilde = (
      r_C_tilde.0,
      CG::mul(&self.setup.class_group().f(), &crate::be_bytes(&message_hash)).add(&r_C_tilde.1),
    );

    Aggregating {
      observing_signing: self,
      x_coordinate,
      message_hash,
      Z_tilde,
      accumulated: HashSet::new(),
      faulty: HashSet::new(),
      pending: HashMap::new(),
      ZU: None,
      KU: None,
    }
  }
}

impl<P: Parameters, CG: Element> Signing<P, CG> {
  /// Participate in signing the following message.
  ///
  /// Returns the participant's message and the view necessary to obtain the resulting signature.
  ///
  /// Please see `SigningProtocol::participate` for the long commentary on when this must be
  /// determined.
  #[must_use]
  pub fn sign(self, message: &[u8]) -> (Aggregating<P, CG>, Vec<u8>) {
    let mut aggregating = self.observing_signing.message(message);

    fn scaled_decryption<P: Parameters, CG: Element>(
      class_group: &ClassGroup<CG>,
      A_tilde: (CG, CG),
      B: CG,
      alpha_i: &UnsignedInteger,
      beta_i: &UnsignedInteger,
      b_i: &<P as Parameters>::F,
    ) -> CG {
      // TODO: Cache/reuse these tables
      let A_tilde_0 = Table::new_for_scalar_bits(
        (class_group.unknown_order_bound() + 128).try_into().unwrap(),
        class_group.identity_p().clone(),
        A_tilde.0,
      );
      let A_tilde_1 = Table::new_for_scalar_bits(
        <P as Parameters>::F::NUM_BITS.try_into().unwrap(),
        class_group.identity_p().clone(),
        A_tilde.1,
      );
      let B = Table::new_for_scalar_bits(
        (class_group.unknown_order_bound() + 128).try_into().unwrap(),
        class_group.identity_p().clone(),
        B,
      );
      // We don't calculate C_tilde_0 as it isn't actually used by the rest of this protocol
      // TODO: Calculate this with a multiexp
      let C_tilde_i_1 = CG::mul(&A_tilde_1, &Zeroizing::new(crate::be_bytes(b_i)));
      let F_i = CG::mul(&B, &Zeroizing::new(alpha_i.to_be_bytes()))
        .sub(CG::mul(&A_tilde_0, &Zeroizing::new(beta_i.to_be_bytes())));
      C_tilde_i_1.sub(F_i)
    }

    let mut message = Vec::with_capacity(2 * 384);
    // (H(m) + rx) * u
    scaled_decryption::<P, CG>(
      self.setup.view().class_group(),
      aggregating.Z_tilde.clone(),
      aggregating.observing_signing.U.clone(),
      &Zeroizing::new(
        self.setup.share_ciphertext_opening() *
          &(&UnsignedInteger::from_be_slice(&crate::be_bytes(&aggregating.x_coordinate)) *
            &UnsignedInteger::from_be_slice(&crate::be_bytes(
              &aggregating.observing_signing.signing_set[&self.setup.i()],
            ))),
      ),
      &self.beta_i,
      &self.u_i,
    )
    .compress(&mut message)
    .unwrap();
    // k * u
    scaled_decryption::<P, CG>(
      self.setup.view().class_group(),
      aggregating.observing_signing.K_tilde.clone(),
      aggregating.observing_signing.U.clone(),
      &self.alpha_i,
      &self.beta_i,
      &self.u_i,
    )
    .compress(&mut message)
    .unwrap();

    // Because this is the view if we're participating, accumulate our own signature share
    match aggregating.aggregate(self.setup.i(), message.clone()) {
      Ready::Ready(_) => unreachable!("t == 1 barred at setup"),
      Ready::NotReady((aggregating_, error)) => {
        aggregating = aggregating_;
        assert!(error.is_none());
      }
    }

    (aggregating, message)
  }
}

/// An error from the second round of the signing protocol.
pub enum RoundTwoError {
  /// This participant has already participated.
  AlreadyParticipated,
  /// The signature share was not from someone participating in this signing protocol.
  NotAParticipant,
  /// The following participants were faulty.
  Faults(Vec<Participant>),
}

/// An ECDSA signature.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Signature<F: PrimeFieldBits> {
  r: F,
  s: F,
}

impl<F: PrimeFieldBits> Signature<F> {
  /// The x-coordinate of the nonce commitment, reduced into the scalar field.
  pub fn r(&self) -> F {
    self.r
  }
  /// The response to the challenge.
  pub fn s(&self) -> F {
    self.s
  }
}

impl<P: Parameters, CG: Element> Aggregating<P, CG> {
  /// Aggregate a signature share from a participant.
  ///
  /// This message is expected to be authenticated as originating from the sender by the caller.
  ///
  /// If any faults are returned, this will never produce a signature. `self` isn't consumed even
  /// if faults are returned so that other messages may still be checked for if they're faulty or
  /// not.
  ///
  /// If a signature is returned, no messages were faulty.
  pub fn aggregate(
    mut self,
    participant: Participant,
    message: Vec<u8>,
  ) -> Ready<(Self, Option<RoundTwoError>), Signature<<P as Parameters>::F>> {
    // Verify they haven't already participated
    if self.accumulated.contains(&participant) ||
      self.faulty.contains(&participant) ||
      self.pending.contains_key(&participant)
    {
      return Ready::NotReady((self, Some(RoundTwoError::AlreadyParticipated)));
    }
    // Verify they were in the signing set
    if !self.observing_signing.signing_set.contains_key(&participant) {
      return Ready::NotReady((self, Some(RoundTwoError::NotAParticipant)));
    }
    // Mark their message as pending
    self.pending.insert(participant, message);

    // If we're now at the threshold, batch verify the pending messages and move them to
    // accumulated
    let setup = &self.observing_signing.setup;
    let mut faulty = vec![];
    if (self.accumulated.len() + self.pending.len()) == usize::from(setup.t()) {
      for (participant, message) in self.pending.drain() {
        let mut message = message.as_slice();
        let Ok(ZU_i) = setup.class_group().decompress_p(&mut message) else {
          faulty.push(participant);
          continue;
        };
        let Ok(KU_i) = setup.class_group().decompress_p(&mut message) else {
          faulty.push(participant);
          continue;
        };

        self.ZU = self.ZU.map(|ZU| ZU.add(&ZU_i)).or(Some(ZU_i));
        self.KU = self.KU.map(|KU| KU.add(&KU_i)).or(Some(KU_i));
        self.accumulated.insert(participant);
      }
    }
    for faulty in &faulty {
      self.faulty.insert(*faulty);
    }

    // If we've accumulated `t` messages, output the signature
    if self.accumulated.len() == usize::from(setup.t()) {
      // Since we run upon `t` potentially valid messages, `t` valid should mean none were invalid
      debug_assert!(faulty.is_empty());

      let be_bytes_to_scalar = |bytes| {
        let mut res = P::F::ZERO;
        for b in bytes {
          for _ in 0 .. 8 {
            res = res.double();
          }
          res += P::F::from(u64::from(b));
        }
        res
      };

      let checked_discrete_logarithm = |element: CG| {
        let log = setup.class_group().discrete_logarithm(&element).unwrap();
        assert_eq!(CG::mul(setup.class_group().f(), &log), element);
        be_bytes_to_scalar(log)
      };

      let numerator = checked_discrete_logarithm(self.ZU.unwrap());
      let denominator = checked_discrete_logarithm(self.KU.unwrap());

      let r = self.x_coordinate;
      let s = numerator * denominator.invert().unwrap();

      return Ready::Ready(Signature { r, s });
    }

    Ready::NotReady((
      self,
      if faulty.is_empty() { None } else { Some(RoundTwoError::Faults(faulty)) },
    ))
  }
}
