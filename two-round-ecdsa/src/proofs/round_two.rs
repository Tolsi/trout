use std::io;

use rand_core::{RngCore, CryptoRng};

use group::prime::PrimeGroup;
use class_groups::{Element, Table};

use crate::UnsignedInteger;

/// The proofs for the second round.
///
/// These proofs need to prove
/// `A_tilde_i_0 = G \cdot alpha_i, B_i = G \cdot beta_i + Y \cdot b_i,
///  F = (A_tilde_1 \cdot b_i) - (B \cdot alpha_i) + (A_tilde_0 \cdot beta_i)` for
/// `A_tilde_i_0 = Z_tilde_i_0, B_i = U_i, A_tilde = Z_tilde, B = U` and
/// `A_tilde_i_0 = K_tilde_i_0, B_i = U_i, A_tilde = K_tilde, B = U` in order to achieve
/// identifiable aborts. Proofs MAY not do anything if forgoing identifiable aborts in favor of
/// efficiency is preferred.
///
/// Given how both instantiations open `B_i, B`, a composition of the two proofs is
/// *strongly recommended*.
//
// The following doesn't define a `BatchVerifier` as we only verify these if we have an invalid
// signature. In that case, while a batch verifier could binary search for invalid elements, that
// still has a worst-case linear complexity to the amount of proofs which are invalid (since all
// invalid proofs are expected to be yielded).
pub trait RoundTwoProofs<E: PrimeGroup, CG: Element> {
  /// Prove the round two statements.
  ///
  /// The provided context hash MUST be binding to
  /// `G, Y, Z_tilde, K_tilde, U, Z_tilde_i_0, K_tilde_i_0, U_i`. This allows the proofs to
  /// not transcript these.
  ///
  /// If an error is returned, the state of `proof` is undefined.
  fn prove(
    rng: &mut (impl RngCore + CryptoRng),
    context: [u8; 32],
    G: &Table<CG>,
    Y: &Table<CG>,
    Z_tilde: &(Table<CG>, Table<CG>),
    K_tilde: &(Table<CG>, Table<CG>),
    U: &Table<CG>,
    alpha_i: &UnsignedInteger,
    beta_i: &UnsignedInteger,
    u_i: &E::Scalar,
    proof: impl io::Write,
  ) -> io::Result<()>;

  /// Verify someone's round two proofs.
  ///
  /// This context must be the exact same as the prover used, causing the same bounds on what has
  /// already been transcripted.
  ///
  /// If an error is returned, `proof` is left in an undefined state.
  fn verify(
    context: [u8; 32],
    G: &Table<CG>,
    Y: &Table<CG>,
    Z_tilde: &(Table<CG>, Table<CG>),
    K_tilde: &(Table<CG>, Table<CG>),
    U: &Table<CG>,
    Z_tilde_i_0: CG,
    K_tilde_i_0: CG,
    U_i: CG,
    ZU_i: CG,
    KU_i: CG,
    proof: impl io::Read,
  ) -> io::Result<()>;
}

/// No identifiable aborts.
///
/// This forgoes the round two proofs, sacrificing identifiable aborts, in the name of efficiency.
pub struct NoIdentifiableAborts;
impl<E: PrimeGroup, CG: Element> RoundTwoProofs<E, CG> for NoIdentifiableAborts {
  fn prove(
    _rng: &mut (impl RngCore + CryptoRng),
    _context: [u8; 32],
    _G: &Table<CG>,
    _Y: &Table<CG>,
    _Z_tilde: &(Table<CG>, Table<CG>),
    _K_tilde: &(Table<CG>, Table<CG>),
    _U: &Table<CG>,
    _alpha_i: &UnsignedInteger,
    _beta_i: &UnsignedInteger,
    _u_i: &E::Scalar,
    _proof: impl io::Write,
  ) -> io::Result<()> {
    Ok(())
  }

  fn verify(
    _context: [u8; 32],
    _G: &Table<CG>,
    _Y: &Table<CG>,
    _Z_tilde: &(Table<CG>, Table<CG>),
    _K_tilde: &(Table<CG>, Table<CG>),
    _U: &Table<CG>,
    _Z_tilde_i_0: CG,
    _K_tilde_i_0: CG,
    _U_i: CG,
    _ZU_i: CG,
    _KU_i: CG,
    _proof: impl io::Read,
  ) -> io::Result<()> {
    Ok(())
  }
}
