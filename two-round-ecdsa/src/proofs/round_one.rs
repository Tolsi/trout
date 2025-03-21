use std::io;

use rand_core::{RngCore, CryptoRng};

use group::prime::PrimeGroup;
use class_groups::{Element, Table};

use crate::UnsignedInteger;

/// The proofs for the first round.
///
/// These proofs need to prove
/// `R_i = E \cdot nonce_i \and K_tilde_i = (\alpha_i \cdot G, \alpha_i \cdot Y + nonce_i \cdot H)`
/// and `U_i = \beta_i \cdot G + u_i \cdot Y`: that `K_tilde_i` is the ciphertext of the nonce and
/// `U_i` has a known opening.
pub trait RoundOneProofs<E: PrimeGroup, CG: Element> {
  /// The batch verifier for the round one proofs.
  type BatchVerifier;

  /// Prove the round one statements.
  ///
  /// This uses `E::generator()`, where `E` is the generic type parameter, for `E`, the elliptic
  /// curve generator from the academic notation.
  ///
  /// The provided context hash MUST be binding to `E, G, Y, H, R_i, K_tilde_i, U_i`. This allows
  /// the proofs to not transcript these.
  ///
  /// If an error is returned, the state of `proof` is undefined.
  fn prove(
    rng: &mut (impl RngCore + CryptoRng),
    context: [u8; 32],
    G: &Table<CG>,
    Y: &Table<CG>,
    H: &Table<CG>,
    alpha_i: &UnsignedInteger,
    nonce_i: &E::Scalar,
    beta_i: &UnsignedInteger,
    u_i: &E::Scalar,
    proof: impl io::Write,
  ) -> io::Result<()>;

  /// Create a batch verifier of round one proofs.
  fn batch_verifier() -> Self::BatchVerifier;

  /// Queue verification of someone's round one proofs.
  ///
  /// This context must be the exact same as the prover used, causing the same bounds on what has
  /// already been transcripted.
  ///
  /// If an error is returned, `proof` is left in an undefined state. The batch verifier is
  /// guaranteed to not be mutated however, meaning a proof which raises an error while being
  /// queued will not corrupt the batch verifier and will leave it eligible to verify other proofs.
  fn queue_verification(
    batch_verifier: &mut Self::BatchVerifier,
    participant: dkg::Participant,
    context: [u8; 32],
    G: &Table<CG>,
    Y: &Table<CG>,
    H: &Table<CG>,
    R_i: E,
    K_tilde_i: &(CG, CG),
    U_i: &CG,
    proof: impl io::Read,
  ) -> io::Result<E>;

  /// Verify all proofs within the batch verifier.
  ///
  /// Returns `Ok(())` or a list of *all* of the *faulty* participants.
  fn verify(batch_verifier: Self::BatchVerifier) -> Result<(), Vec<dkg::Participant>>;
}
