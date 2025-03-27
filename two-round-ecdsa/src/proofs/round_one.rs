use core::{marker::PhantomData, ops::Deref};
use std::io::{self, Read, Write};

use zeroize::Zeroizing;
use rand_core::{RngCore, CryptoRng};

use group::{
  ff::{Field, PrimeField},
  Group, GroupEncoding,
};
use class_groups::{Element, Table, ClassGroup};

use crate::{UnsignedInteger, DigestReader, DigestWriter, Primes, Parameters};

/// The proofs for the first round.
///
/// These proofs need to prove
/// `R_i = E \cdot nonce_i \and K_tilde_i = (\alpha_i \cdot G, \alpha_i \cdot Y + nonce_i \cdot H)`
/// and `U_i = \beta_i \cdot G + u_i \cdot Y`: that `K_tilde_i` is the ciphertext of the nonce and
/// `U_i` has a known opening.
pub trait RoundOneProofs<CG: Element, P: Parameters<CG>> {
  /// The batch verifier for the round one proofs.
  type BatchVerifier;

  /// Prove the round one statements.
  ///
  /// This uses `P::E::generator()`, where `E` is the generic type parameter, for `E`, the elliptic
  /// curve generator from the academic notation. This also uses `ClassGroup::f()` for `H`.
  ///
  /// The provided transcript MUST already be binding to `E, G, Y, H, R_i, K_tilde_i, U_i`. This
  /// allows the proofs to not transcript these.
  ///
  /// If an error is returned, the state of `transcript` is undefined.
  fn prove<W: io::Write>(
    rng: &mut (impl RngCore + CryptoRng),
    class_group: &ClassGroup<CG>,
    G: &Table<CG>,
    Y: &Table<CG>,
    alpha_i: &UnsignedInteger,
    nonce_i: &P::F,
    beta_i: &UnsignedInteger,
    u_i: &P::F,
    transcript: &mut DigestWriter<W>,
  ) -> io::Result<()>;

  /// Create a batch verifier of round one proofs.
  fn batch_verifier() -> Self::BatchVerifier;

  /// Queue verification of someone's round one proofs.
  ///
  /// This transcript must be the exact same as the prover used, causing the same bounds on what
  /// has already been transcripted.
  ///
  /// If an error is returned, `transcript` is left in an undefined state. The batch verifier is
  /// guaranteed to not be mutated however, meaning a proof which raises an error while being
  /// queued will not corrupt the batch verifier and will leave it eligible to verify other proofs.
  fn queue_verification<R: io::Read>(
    batch_verifier: &mut Self::BatchVerifier,
    participant: dkg::Participant,
    class_group: &ClassGroup<CG>,
    G: &Table<CG>,
    Y: &Table<CG>,
    R_i: P::E,
    K_tilde_i: &(CG, CG),
    U_i: &CG,
    transcript: &mut DigestReader<R>,
  ) -> io::Result<()>;

  /// Verify all proofs within the batch verifier.
  ///
  /// Returns `Ok(())` or a list of *all* of the *faulty* participants.
  fn verify(batch_verifier: Self::BatchVerifier) -> Result<(), Vec<dkg::Participant>>;
}

/// Proofs from Cui, Chan, Yuen, Kang, and Chu's Bandwidth-Efficient Zero-Knowledge Proofs for
/// Threshold ECDSA (2023).
pub struct Ccykc2023RoundOne<Pr: Primes>(PhantomData<Pr>);
impl<CG: Element, P: Parameters<CG>, Pr: Primes> RoundOneProofs<CG, P> for Ccykc2023RoundOne<Pr> {
  type BatchVerifier = ();

  fn prove<W: io::Write>(
    rng: &mut (impl RngCore + CryptoRng),
    class_group: &ClassGroup<CG>,
    G: &Table<CG>,
    Y: &Table<CG>,
    alpha_i: &UnsignedInteger,
    nonce_i: &P::F,
    beta_i: &UnsignedInteger,
    u_i: &P::F,
    transcript: &mut DigestWriter<W>,
  ) -> io::Result<()> {
    let B = crate::ccykc::B::<P::F, _>(class_group);

    // Algorithm 6 ZKPoKLog, to prove the integrity of `R_i, K_tilde_i`
    // `s_p` according to the paper
    let r_randomness = Zeroizing::new(UnsignedInteger::random(B, &mut *rng));
    // `s_m` according to the paper
    let r_message = Zeroizing::new(P::F::random(&mut *rng));
    // Write $\hat{S}$ from the paper
    transcript.write_all((P::E::generator() * r_message.deref()).to_bytes().as_ref())?;
    // Write `S_2` from the paper
    CG::mul(G, &Zeroizing::new(r_randomness.to_be_bytes())).compress(&mut *transcript)?;
    // Write `S_1` from the paper
    CG::mul(Y, &Zeroizing::new(r_randomness.to_be_bytes()))
      .add(&CG::mul(class_group.f(), &Zeroizing::new(crate::be_bytes(r_message.deref()))))
      .compress(&mut *transcript)?;

    // Algorithm 1 ZKPoKRepS to prove the integrity of `U_i`
    // `k_0` according to the paper
    let k_beta_i = Zeroizing::new(UnsignedInteger::random(B, &mut *rng));
    // `k_1` according to the paper
    let k_u_i = Zeroizing::new(UnsignedInteger::random(B, &mut *rng));
    // Write `R` from the paper
    CG::mul(G, &Zeroizing::new(k_beta_i.to_be_bytes()))
      .add(&CG::mul(Y, &Zeroizing::new(k_u_i.to_be_bytes())))
      .compress(&mut *transcript)?;

    // Sample a challenge for both proofs
    // This is done as sampling the prime is presumed expensive, so reducing samples is appreciated
    let c = P::from_xof(transcript.0.finalize_xof());
    transcript.0.update(&[0]);
    let prime = Pr::prime(crate::ccykc::LAMBDA, transcript.0.finalize_xof());

    let c_uint = UnsignedInteger::from_be_slice(&crate::be_bytes(&c));
    let modulus =
      crypto_bigint::NonZero::new((&prime * &UnsignedInteger::from_be_slice(class_group.p())).0)
        .unwrap();

    // ZKPoKLog response
    {
      {
        // `u_m` from the paper
        let s_message = *r_message + Zeroizing::new(c * nonce_i).deref();
        transcript.write_all(s_message.to_repr().as_ref())?;
      }

      // `u_p` from the paper
      let s_randomness =
        Zeroizing::new(r_randomness.deref() + Zeroizing::new(&c_uint * alpha_i).deref());
      // `(d_p, e_p)` from the paper
      let (d_randomness, e_randomness) = s_randomness.div_rem(&modulus);
      // Write `D_2` from the paper
      CG::mul(G, &d_randomness).compress(&mut *transcript)?;
      // Write `D_1` from the paper
      CG::mul(Y, &d_randomness).compress(&mut *transcript)?;
      // Write `e_p` from the paper
      crate::ccykc::write_e(&mut *transcript, &modulus, e_randomness)?;
    }

    // ZKPoKRepS response
    {
      // `s_0` from the paper
      let s_beta_i = Zeroizing::new(k_beta_i.deref() + Zeroizing::new(&c_uint * beta_i).deref());
      // `s_1` from the paper
      let u_i = Zeroizing::new(UnsignedInteger::from_be_slice(
        Zeroizing::new(crate::be_bytes(u_i)).deref(),
      ));
      let s_u_i = Zeroizing::new(k_u_i.deref() + Zeroizing::new(&c_uint * u_i.deref()).deref());
      let (d_beta_i, e_beta_i) = s_beta_i.div_rem(&modulus);
      let (d_u_i, e_u_i) = s_u_i.div_rem(&modulus);
      // Write `D` from the paper
      CG::mul(G, &d_beta_i).add(&CG::mul(Y, &d_u_i)).compress(&mut *transcript)?;
      // Write `e_0` from the paper
      crate::ccykc::write_e(&mut *transcript, &modulus, e_beta_i)?;
      // Write `e_1` from the paper
      crate::ccykc::write_e(&mut *transcript, &modulus, e_u_i)?;
    }

    Ok(())
  }

  fn batch_verifier() -> Self::BatchVerifier {
    ()
  }

  fn queue_verification<R: io::Read>(
    _batch_verifier: &mut Self::BatchVerifier,
    _participant: dkg::Participant,
    class_group: &ClassGroup<CG>,
    G: &Table<CG>,
    Y: &Table<CG>,
    R_i: P::E,
    K_tilde_i: &(CG, CG),
    U_i: &CG,
    transcript: &mut DigestReader<R>,
  ) -> io::Result<()> {
    // ZKPoKLog commitment
    let R_message = P::read_canonical_E(&mut *transcript)?;
    let R_randomness_commitment = class_group.decompress_p(&mut *transcript)?;
    let R_ciphertext = class_group.decompress_p(&mut *transcript)?;

    // ZKPoKRepS commitment
    let R_U = class_group.decompress_p(&mut *transcript)?;

    let c = P::from_xof(transcript.0.finalize_xof());
    transcript.0.update(&[0]);
    let prime = Pr::prime(crate::ccykc::LAMBDA, transcript.0.finalize_xof());

    let c_uint = UnsignedInteger::from_be_slice(&crate::be_bytes(&c));
    let modulus = (&prime * &UnsignedInteger::from_be_slice(class_group.p())).0;
    let modulus_bytes = modulus.to_be_bytes();
    let modulus = crypto_bigint::NonZero::new(modulus).unwrap();

    // ZKPoKLog response
    {
      let mut s_message = <P::F as PrimeField>::Repr::default();
      transcript.read_exact(s_message.as_mut())?;
      let s_message = Option::<P::F>::from(P::F::from_repr(s_message))
        .ok_or_else(|| io::Error::other("invalid s_message"))?;

      if (P::E::generator() * s_message) != (R_message + (R_i * c)) {
        Err(io::Error::other("R_i PoK was invalid"))?;
      }

      let D_randomness_commitment = class_group.decompress_p(&mut *transcript)?;
      let D_ciphertext = class_group.decompress_p(&mut *transcript)?;
      let e_randomness = crate::ccykc::read_e(&mut *transcript, &modulus)?;

      {
        let lhs =
          CG::mul_once(class_group.identity_p().clone(), D_randomness_commitment, &modulus_bytes);
        let lhs = lhs.add(&CG::mul(G, &e_randomness));

        let rhs = CG::mul_once(
          class_group.identity_p().clone(),
          K_tilde_i.0.clone(),
          &c_uint.to_be_bytes(),
        );
        let rhs = R_randomness_commitment.add(&rhs);

        if lhs != rhs {
          Err(io::Error::other("K_tilde_i.0 PoK was invalid"))?;
        }
      }

      {
        let lhs = CG::mul_once(class_group.identity_p().clone(), D_ciphertext, &modulus_bytes);
        let lhs = lhs
          .add(&CG::mul(Y, &e_randomness))
          .add(&CG::mul(class_group.f(), &crate::be_bytes(&s_message)));

        let rhs = CG::mul_once(
          class_group.identity_p().clone(),
          K_tilde_i.1.clone(),
          &c_uint.to_be_bytes(),
        );
        let rhs = R_ciphertext.add(&rhs);

        if lhs != rhs {
          Err(io::Error::other("K_tilde_i.1 PoK was invalid"))?;
        }
      }
    }

    // ZKPoKRepS response
    {
      let D_U = class_group.decompress_p(&mut *transcript)?;
      let e_beta_i = crate::ccykc::read_e(&mut *transcript, &modulus)?;
      let e_u_i = crate::ccykc::read_e(&mut *transcript, &modulus)?;

      let lhs = CG::mul_once(class_group.identity_p().clone(), D_U, &modulus_bytes);
      let lhs = lhs.add(&CG::mul(G, &e_beta_i)).add(&CG::mul(Y, &e_u_i));

      let rhs = CG::mul_once(class_group.identity_p().clone(), U_i.clone(), &c_uint.to_be_bytes());
      let rhs = R_U.add(&rhs);

      if lhs != rhs {
        Err(io::Error::other("U_i PoK was invalid"))?;
      }
    }

    Ok(())
  }

  fn verify(_batch_verifier: Self::BatchVerifier) -> Result<(), Vec<dkg::Participant>> {
    Ok(())
  }
}
