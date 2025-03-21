use std::io;

use zeroize::{Zeroize, Zeroizing};
use rand_core::{RngCore, CryptoRng};

use group::{ff::Field, prime::PrimeGroup};

/// An eVRF.
///
/// The [eVRF paper](https://eprint.iacr.org/2024/996) details two constructions, one premised on
/// Paillier and one premised on the EC DDH problem. There are also two alternative constructions
/// posited since:
/// - The EC DDH eVRF, optimized by using the function field of the EC to prove scalar
///   multiplications ([as posited by Eagen](https://eprint.iacr.org/2022/596))
/// - [An LWR-based construction](https://eprint.iacr.org/2024/996)
///
/// The eVRF used is left to the choice of the caller.
pub trait Evrf<E: PrimeGroup<Scalar: Zeroize>> {
  /// The view of someone's setup, as necessary to verify someone's invocation of the eVRF.
  type SetupView: Clone;
  /// The setup, as necessary to invoke the eVRF.
  type Setup;
  /// The batch verifier for eVRFs.use core::marker::PhantomData;
  type BatchVerifier;

  /// Perform the setup for the eVRF.
  fn setup(rng: &mut (impl RngCore + CryptoRng)) -> (Self::SetupView, Self::Setup);

  /// Invoke the eVRF to obtain a random value.
  ///
  /// The proof is written to `proof`. If this function returns an error, the status of `proof` is
  /// undefined.
  fn prove(
    rng: &mut (impl RngCore + CryptoRng),
    setup: &Self::Setup,
    session_id: [u8; 32],
    proof: impl io::Write,
  ) -> io::Result<Zeroizing<E::Scalar>>;

  /// Create a batch verifier of eVRFs.
  fn batch_verifier() -> Self::BatchVerifier;
  /// Queue verification of someone else's invocation of the eVRF.
  ///
  /// Returns the commitment to the value over the generator of the elliptic curve. This commitment
  /// is not guaranteed to be verified at this time. The batch verifier must be verified for this
  /// item to be verified.
  ///
  /// If an error is returned, `proof` is left in an undefined state. The batch verifier is
  /// guaranteed to not be mutated however, meaning a proof which raises an error while being
  /// queued will not corrupt the batch verifier and will leave it eligible to verify other proofs.
  fn queue_verification(
    batch_verifier: &mut Self::BatchVerifier,
    participant: dkg::Participant,
    setup: &Self::SetupView,
    session_id: [u8; 32],
    proof: impl io::Read,
  ) -> io::Result<E>;
  /// Verify all proofs within the batch verifier.
  ///
  /// Returns `Ok(())` or a list of *all* of the *faulty* participants.
  fn verify(batch_verifier: Self::BatchVerifier) -> Result<(), Vec<dkg::Participant>>;
}

/// A dummy eVRF which does not perform any proof and accordingly isn't verifiable.
///
/// This is not presented as a secure choice of eVRF. Using this removes the ability to simulate
/// the nonce within the security proofs. This is presented solely for evaluation purposes or in
/// case future works prove the security of this scheme even without the eVRF (as
/// https://eprint.iacr.org/2021/1449 implies the security of).
pub struct DummyEvrf;
impl<E: PrimeGroup<Scalar: Zeroize>> Evrf<E> for DummyEvrf {
  type SetupView = ();
  type Setup = ();
  type BatchVerifier = ();

  fn setup(_rng: &mut (impl RngCore + CryptoRng)) -> (Self::SetupView, Self::Setup) {
    ((), ())
  }

  fn batch_verifier() -> Self::BatchVerifier {
    ()
  }

  fn prove(
    rng: &mut (impl RngCore + CryptoRng),
    _setup: &Self::Setup,
    _session_id: [u8; 32],
    mut proof: impl io::Write,
  ) -> io::Result<Zeroizing<E::Scalar>> {
    let nonce = Zeroizing::new(E::Scalar::random(rng));
    let nonce_commitment = E::generator() * *nonce;
    proof.write_all(nonce_commitment.to_bytes().as_ref())?;
    Ok(nonce)
  }

  fn queue_verification(
    _batch_verifier: &mut Self::BatchVerifier,
    _participant: dkg::Participant,
    _setup: &Self::SetupView,
    _session_id: [u8; 32],
    mut proof: impl io::Read,
  ) -> io::Result<E> {
    let mut nonce_commitment = E::Repr::default();
    proof.read_exact(nonce_commitment.as_mut())?;
    // TODO: This from_bytes doesn't guarantee canonicity
    let Some(nonce_commitment) = Option::<E>::from(E::from_bytes(&nonce_commitment)) else {
      Err(io::Error::other("nonce commitment was invalid"))?
    };
    Ok(nonce_commitment)
  }

  fn verify(_batch_verifier: Self::BatchVerifier) -> Result<(), Vec<dkg::Participant>> {
    Ok(())
  }
}
