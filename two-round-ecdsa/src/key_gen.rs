use std::{sync::Arc, collections::HashMap};

use zeroize::{Zeroize, Zeroizing};
use rand_core::{RngCore, CryptoRng, SeedableRng};
use rand_chacha::ChaCha20Rng;

use group::{
  ff::{Field, PrimeField, PrimeFieldBits},
  prime::PrimeGroup,
};
use class_groups::{Element, Table, ClassGroup};

use dkg::Participant;

use crate::UnsignedInteger;

/// The security level to target with the setup.
///
/// These are defined per https://eprint.iacr.org/2020/196. Please note a rebuttal of this paper's
/// definition exists in https://eprint.iacr.org/2021/291, as its Remark 1.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SecurityLevel {
  /// A trivial class group which is insecure and MUST only be used for testing purposes.
  Insecure,
  /// An 1827-bit discriminant with 128-bits of security per popular convention.
  ///
  /// This has a 2**-14.3 chance of being weaker than the targetted 128-bit security level.
  OneHundredTwentyEightBit,
  /// A 2048-bit discriminant which should have 128-bits of security even with marginally improved
  /// attacks against class-groups.
  ConservativeOneHundredTwentyEightBit,
  /// A 4096-bit discriminant which only has 128-bits of security in a (2**-64)-case event.
  VeryConservativeOneHundredTwentyEightBit,
  /// A 6784-bit discriminant which only has 128-bits of security in a (2**-128)-case event.
  ExtremelyConservativeOneHundredTwentyEightBit,
}

/// A view of the setup for a multisig.
#[derive(Clone)]
pub struct SetupView<E: PrimeGroup, CG: Element> {
  t: u16,
  class_group_seed: [u8; 32],
  class_group: ClassGroup<CG>,
  G: Table<CG>,
  Y: Table<CG>,
  verification_key: E,
  // verification_shares: HashMap<Participant, E>,
  share_ciphertexts: HashMap<Participant, (Table<CG>, Table<CG>)>,
}

impl<E: PrimeGroup, CG: Element> SetupView<E, CG> {
  pub(crate) fn t(&self) -> u16 {
    self.t
  }
  pub(crate) fn n(&self) -> usize {
    self.share_ciphertexts.len()
  }
  pub(crate) fn class_group(&self) -> &ClassGroup<CG> {
    &self.class_group
  }
  pub(crate) fn G(&self) -> &Table<CG> {
    &self.G
  }
  pub(crate) fn Y(&self) -> &Table<CG> {
    &self.Y
  }
  /// The ECDSA verification key.
  pub fn verification_key(&self) -> E {
    self.verification_key
  }
  pub(crate) fn share_ciphertext(
    &self,
    participant: &Participant,
  ) -> Option<&(Table<CG>, Table<CG>)> {
    self.share_ciphertexts.get(participant)
  }
}

/// The result of the setup for a participant.
pub struct Setup<E: PrimeGroup<Scalar: Zeroize + PrimeFieldBits>, CG: Element> {
  view: Arc<SetupView<E, CG>>,
  i: Participant,
  share_ciphertext_opening: Zeroizing<(UnsignedInteger, E::Scalar)>,
}

fn class_group<E: PrimeGroup<Scalar: Zeroize + PrimeFieldBits>, CG: Element>(
  seed: [u8; 32],
  security_level: SecurityLevel,
) -> (ClassGroup<CG>, Table<CG>, Table<CG>) {
  let mut class_group_rng = ChaCha20Rng::from_seed(seed);

  // The security level is converted to the lambda parameter of which the fundamental
  // discriminant is twice as large
  let lambda = match security_level {
    SecurityLevel::Insecure => 300,
    SecurityLevel::OneHundredTwentyEightBit => 914,
    SecurityLevel::ConservativeOneHundredTwentyEightBit => 1024,
    SecurityLevel::VeryConservativeOneHundredTwentyEightBit => 2048,
    SecurityLevel::ExtremelyConservativeOneHundredTwentyEightBit => 3392,
  };

  let p_bytes = {
    let mut p_bytes = crate::be_bytes(&-E::Scalar::ONE);
    // `p_bytes` has `p - 1` where `p` is prime, so set back the last bit
    const {
      // Handle the edge case of 2 which isn't supported by our class group construction and adding
      // 1 is not the following binary OR operation
      assert!(E::Scalar::NUM_BITS > 1, "prime order was <= 2 when an odd prime is required");
    }
    *p_bytes.last_mut().unwrap() |= 1;
    p_bytes
  };

  let class_group = ClassGroup::<CG>::setup(&mut class_group_rng, lambda, &p_bytes).unwrap();
  let G =
    Table::new(10, class_group.identity_p().clone(), class_group.generator_p(&mut class_group_rng));
  let Y =
    Table::new(10, class_group.identity_p().clone(), class_group.generator_p(&mut class_group_rng));
  (class_group, G, Y)
}

impl<E: PrimeGroup<Scalar: Zeroize + PrimeFieldBits>, CG: Element> Setup<E, CG> {
  /// The public view of the setup.
  pub fn view(&self) -> &Arc<SetupView<E, CG>> {
    &self.view
  }

  /// Our participant index.
  pub(crate) fn i(&self) -> Participant {
    self.i
  }

  /// The opening of our share's ciphertext.
  pub(crate) fn share_ciphertext_opening(&self) -> &UnsignedInteger {
    &self.share_ciphertext_opening.0
  }

  /// Perform the setup with a dealer key-generation.
  ///
  /// This is not a distributed setup but a trusted setup. The dealer learns the secret key. This
  /// generally should not be used.
  ///
  /// Returns `None` upon invalid parameters.
  #[must_use]
  pub fn dealer(
    rng: &mut (impl RngCore + CryptoRng),
    security_level: SecurityLevel,
    t: u16,
    n: u16,
  ) -> Option<HashMap<Participant, Arc<Setup<E, CG>>>> {
    {
      let valid_t_n = (t <= n) && (1 < t);
      if !valid_t_n {
        None?;
      }
    }

    let mut class_group_seed = [0; 32];
    rng.fill_bytes(&mut class_group_seed);
    let (class_group, G, Y) = class_group::<E, CG>(class_group_seed, security_level);

    // Generate `t` coefficients
    let mut coeffs = Zeroizing::new(vec![E::Scalar::ZERO; usize::from(t)]);
    for coeff in coeffs.as_mut_slice() {
      *coeff = E::Scalar::random(&mut *rng);
    }

    // Set the verification key
    let verification_key = E::generator() * coeffs[0];

    // Create the shares for each participant
    let mut share_ciphertext_openings = HashMap::new();
    for participant in (1 ..= n).map(|i| Participant::new(i).unwrap()) {
      fn polynomial<F: PrimeField + Zeroize>(coefficients: &[F], l: Participant) -> Zeroizing<F> {
        let l = F::from(u64::from(u16::from(l)));
        // This should never be reached since Participant is explicitly non-zero
        assert!(l != F::ZERO, "zero participant passed to polynomial");
        let mut share = Zeroizing::new(F::ZERO);
        for (idx, coefficient) in coefficients.iter().rev().enumerate() {
          *share += coefficient;
          if idx != (coefficients.len() - 1) {
            *share *= l;
          }
        }
        share
      }

      share_ciphertext_openings.insert(
        participant,
        Zeroizing::new((
          UnsignedInteger::random(class_group.unknown_order_bound() + 128, &mut *rng),
          *polynomial(&coeffs, participant),
        )),
      );
    }

    // Calculate the share ciphertexts
    let share_ciphertexts = share_ciphertext_openings
      .iter()
      .map(|(participant, mask_and_scalar)| {
        let (mask, scalar) = &**mask_and_scalar;
        (*participant, {
          let mask = Zeroizing::new(mask.to_be_bytes());
          (
            Table::new(10, class_group.identity_p().clone(), CG::mul(&G, &mask)),
            Table::new(
              10,
              class_group.identity_p().clone(),
              CG::mul(&Y, &mask)
                .add(&CG::mul(class_group.f(), &Zeroizing::new(crate::be_bytes(scalar)))),
            ),
          )
        })
      })
      .collect();

    // Create the view
    let view = Arc::new(SetupView {
      t,
      class_group_seed,
      class_group,
      G,
      Y,
      verification_key,
      share_ciphertexts,
    });

    // Create each participant's setup
    let mut res = HashMap::new();
    for i in (1 ..= n).map(|i| Participant::new(i).unwrap()) {
      res.insert(
        i,
        Arc::new(Setup {
          view: view.clone(),
          i,
          share_ciphertext_opening: share_ciphertext_openings.remove(&i).unwrap(),
        }),
      );
    }
    Some(res)
  }
}
