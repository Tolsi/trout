use std::io;

use zeroize::Zeroizing;
use rand_core::{RngCore, CryptoRng};

use group::{ff::Field, Group, GroupEncoding};
use class_groups::Element;

use crate::Parameters;

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
pub trait Evrf<CG: Element, P: Parameters<CG>> {
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
  /// The context MUST be binding to the setup and the invocation. This allows the eVRF
  /// implementation to not have to transcript these itself.
  ///
  /// The proof is written to `proof`. If this function returns an error, the status of `proof` is
  /// undefined.
  fn prove(
    rng: &mut (impl RngCore + CryptoRng),
    setup: &Self::Setup,
    context: [u8; 32],
    proof: impl io::Write,
  ) -> io::Result<Zeroizing<P::F>>;

  /// Create a batch verifier of eVRFs.
  fn batch_verifier() -> Self::BatchVerifier;
  /// Queue verification of someone's invocation of the eVRF.
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
    context: [u8; 32],
    proof: impl io::Read,
  ) -> io::Result<P::E>;
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
/// <https://eprint.iacr.org/2021/1449> implies the security of).
pub struct DummyEvrf;
impl<CG: Element, P: Parameters<CG>> Evrf<CG, P> for DummyEvrf {
  type SetupView = ();
  type Setup = ();
  type BatchVerifier = ();

  fn setup(_rng: &mut (impl RngCore + CryptoRng)) -> (Self::SetupView, Self::Setup) {
    ((), ())
  }

  fn batch_verifier() -> Self::BatchVerifier {}

  fn prove(
    rng: &mut (impl RngCore + CryptoRng),
    _setup: &Self::Setup,
    _context: [u8; 32],
    mut proof: impl io::Write,
  ) -> io::Result<Zeroizing<P::F>> {
    let nonce = Zeroizing::new(P::F::random(rng));
    let nonce_commitment = P::E::generator() * *nonce;
    proof.write_all(nonce_commitment.to_bytes().as_ref())?;
    Ok(nonce)
  }

  fn queue_verification(
    _batch_verifier: &mut Self::BatchVerifier,
    _participant: dkg::Participant,
    _setup: &Self::SetupView,
    _context: [u8; 32],
    proof: impl io::Read,
  ) -> io::Result<P::E> {
    P::read_canonical_E(proof)
  }

  fn verify(_batch_verifier: Self::BatchVerifier) -> Result<(), Vec<dkg::Participant>> {
    Ok(())
  }
}
