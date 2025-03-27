use core::{marker::PhantomData, ops::Deref};
use std::io;

use zeroize::Zeroizing;
use rand_core::{RngCore, CryptoRng};

use class_groups::{Element, Table, ClassGroup};

use crate::{UnsignedInteger, DigestReader, DigestWriter, Primes, Parameters};

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
pub trait RoundTwoProofs<CG: Element, P: Parameters<CG>> {
  /// Prove the round two statements.
  ///
  /// The provided context hash MUST be binding to
  /// `G, Y, Z_tilde, K_tilde, U, Z_tilde_i_0, K_tilde_i_0, U_i`. This allows the proofs to
  /// not transcript these.
  ///
  /// `neg_U` is `-U`.
  ///
  /// If an error is returned, the state of `proof` is undefined.
  fn prove<W: io::Write>(
    rng: &mut (impl RngCore + CryptoRng),
    class_group: &ClassGroup<CG>,
    G: &Table<CG>,
    Y: &Table<CG>,
    Z_tilde: &(Table<CG>, Table<CG>),
    K_tilde: &(Table<CG>, Table<CG>),
    neg_U: &Table<CG>,
    delta_i: &UnsignedInteger,
    alpha_i: &UnsignedInteger,
    beta_i: &UnsignedInteger,
    u_i: &P::F,
    transcript: &mut DigestWriter<W>,
  ) -> io::Result<()>;

  /// Verify someone's round two proofs.
  ///
  /// This context must be the exact same as the prover used, causing the same bounds on what has
  /// already been transcripted.
  ///
  /// `neg_U` is `-U`.
  ///
  /// If an error is returned, `proof` is left in an undefined state.
  fn verify<R: io::Read>(
    class_group: &ClassGroup<CG>,
    G: &Table<CG>,
    Y: &Table<CG>,
    Z_tilde: &(Table<CG>, Table<CG>),
    K_tilde: &(Table<CG>, Table<CG>),
    neg_U: &Table<CG>,
    Z_tilde_i_0: CG,
    K_tilde_i_0: CG,
    U_i: CG,
    ZU_i: CG,
    KU_i: CG,
    transcript: &mut DigestReader<R>,
  ) -> io::Result<()>;
}

/// No identifiable aborts.
///
/// This forgoes the round two proofs, sacrificing identifiable aborts, in the name of efficiency.
pub struct NoIdentifiableAborts;
impl<CG: Element, P: Parameters<CG>> RoundTwoProofs<CG, P> for NoIdentifiableAborts {
  fn prove<W: io::Write>(
    _rng: &mut (impl RngCore + CryptoRng),
    _class_group: &ClassGroup<CG>,
    _G: &Table<CG>,
    _Y: &Table<CG>,
    _Z_tilde: &(Table<CG>, Table<CG>),
    _K_tilde: &(Table<CG>, Table<CG>),
    _U: &Table<CG>,
    _delta_i: &UnsignedInteger,
    _alpha_i: &UnsignedInteger,
    _beta_i: &UnsignedInteger,
    _u_i: &P::F,
    _transcript: &mut DigestWriter<W>,
  ) -> io::Result<()> {
    Ok(())
  }

  fn verify<R: io::Read>(
    _class_group: &ClassGroup<CG>,
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
    _transcript: &mut DigestReader<R>,
  ) -> io::Result<()> {
    Ok(())
  }
}

/// Proofs from Cui, Chan, Yuen, Kang, and Chu's Bandwidth-Efficient Zero-Knowledge Proofs for
/// Threshold ECDSA (2023).
pub struct Ccykc2023RoundTwo<Pr: Primes>(PhantomData<Pr>);
impl<CG: Element, P: Parameters<CG>, Pr: Primes> RoundTwoProofs<CG, P> for Ccykc2023RoundTwo<Pr> {
  fn prove<W: io::Write>(
    rng: &mut (impl RngCore + CryptoRng),
    class_group: &ClassGroup<CG>,
    G: &Table<CG>,
    Y: &Table<CG>,
    Z_tilde: &(Table<CG>, Table<CG>),
    K_tilde: &(Table<CG>, Table<CG>),
    neg_U: &Table<CG>,
    delta_i: &UnsignedInteger,
    alpha_i: &UnsignedInteger,
    beta_i: &UnsignedInteger,
    u_i: &P::F,
    transcript: &mut DigestWriter<W>,
  ) -> io::Result<()> {
    /*
      ZKPoKRepS is proven for elements which are in G_q * F and are not in F (so elements such as
      1G + 1F but not 1F). We prove five ZKPoKRepS on a shared transcript:

      1) Open `Z_tilde_i_0` over `G` for `delta_i`
      2) Open `K_tilde_i_0` over `G` for `alpha_i`
      3) Open `U_i` over `G` for `beta_i`, `Y` for `u_i`
      4) $(Z_tilde_1 \cdot u_i) - (U \cdot delta_i) + (Z_tilde_0 \cdot beta_i)$
      5) $(K_tilde_1 \cdot u_i) - (U \cdot alpha_i) + (K_tilde_0 \cdot beta_i)$

      where, of course, the responses for each scalar are reused across proofs to ensure their
      consistency.
    */

    let B = crate::ccykc::B::<P::F, _>(class_group);

    let r_delta_i = Zeroizing::new(UnsignedInteger::random(B, &mut *rng));
    let r_alpha_i = Zeroizing::new(UnsignedInteger::random(B, &mut *rng));
    let r_beta_i = Zeroizing::new(UnsignedInteger::random(B, &mut *rng));
    let r_u_i = Zeroizing::new(UnsignedInteger::random(B, &mut *rng));

    // Nonce commitments for each invocation
    CG::mul(G, &Zeroizing::new(r_delta_i.to_be_bytes())).compress(&mut *transcript)?;
    CG::mul(G, &Zeroizing::new(r_alpha_i.to_be_bytes())).compress(&mut *transcript)?;
    CG::multiexp(
      class_group.identity_p(),
      &[(G, &Zeroizing::new(r_beta_i.to_be_bytes())), (Y, &Zeroizing::new(r_u_i.to_be_bytes()))],
    )
    .compress(&mut *transcript)?;
    CG::multiexp(
      class_group.identity_p(),
      &[
        (&Z_tilde.1, &Zeroizing::new(r_u_i.to_be_bytes())),
        (neg_U, &Zeroizing::new(r_delta_i.to_be_bytes())),
        (&Z_tilde.0, &Zeroizing::new(r_beta_i.to_be_bytes())),
      ],
    )
    .compress(&mut *transcript)?;
    CG::multiexp(
      class_group.identity_p(),
      &[
        (&K_tilde.1, &Zeroizing::new(r_u_i.to_be_bytes())),
        (neg_U, &Zeroizing::new(r_alpha_i.to_be_bytes())),
        (&K_tilde.0, &Zeroizing::new(r_beta_i.to_be_bytes())),
      ],
    )
    .compress(&mut *transcript)?;

    // Sample the challenge
    let c = P::from_xof(transcript.0.finalize_xof());
    let c = UnsignedInteger::from_be_slice(&crate::be_bytes(&c));
    transcript.0.update(&[0]);
    let prime = Pr::prime(crate::ccykc::LAMBDA, transcript.0.finalize_xof());
    let modulus =
      crypto_bigint::NonZero::new((&prime * &UnsignedInteger::from_be_slice(class_group.p())).0)
        .unwrap();

    let s_delta_i = Zeroizing::new(r_delta_i.deref() + &Zeroizing::new(&c * delta_i));
    let s_alpha_i = Zeroizing::new(r_alpha_i.deref() + &Zeroizing::new(&c * alpha_i));
    let s_beta_i = Zeroizing::new(r_beta_i.deref() + &Zeroizing::new(&c * beta_i));
    let s_u_i = Zeroizing::new(
      r_u_i.deref() +
        &Zeroizing::new(
          &c * &Zeroizing::new(UnsignedInteger::from_be_slice(&Zeroizing::new(crate::be_bytes(
            u_i,
          )))),
        ),
    );

    let (d_delta_i, e_delta_i) = s_delta_i.div_rem(&modulus);
    let (d_alpha_i, e_alpha_i) = s_alpha_i.div_rem(&modulus);
    let (d_beta_i, e_beta_i) = s_beta_i.div_rem(&modulus);
    let (d_u_i, e_u_i) = s_u_i.div_rem(&modulus);

    // The `D` for each invocation
    CG::mul(G, &d_delta_i).compress(&mut *transcript)?;
    CG::mul(G, &d_alpha_i).compress(&mut *transcript)?;
    CG::multiexp(class_group.identity_p(), &[(G, &d_beta_i), (Y, &d_u_i)])
      .compress(&mut *transcript)?;
    CG::multiexp(
      class_group.identity_p(),
      &[(&Z_tilde.1, &d_u_i), (neg_U, &d_delta_i), (&Z_tilde.0, &d_beta_i)],
    )
    .compress(&mut *transcript)?;
    CG::multiexp(
      class_group.identity_p(),
      &[(&K_tilde.1, &d_u_i), (neg_U, &d_alpha_i), (&K_tilde.0, &d_beta_i)],
    )
    .compress(&mut *transcript)?;

    // Each `e`
    crate::ccykc::write_e(&mut *transcript, &modulus, e_delta_i)?;
    crate::ccykc::write_e(&mut *transcript, &modulus, e_alpha_i)?;
    crate::ccykc::write_e(&mut *transcript, &modulus, e_beta_i)?;
    crate::ccykc::write_e(&mut *transcript, &modulus, e_u_i)
  }

  fn verify<R: io::Read>(
    class_group: &ClassGroup<CG>,
    G: &Table<CG>,
    Y: &Table<CG>,
    Z_tilde: &(Table<CG>, Table<CG>),
    K_tilde: &(Table<CG>, Table<CG>),
    neg_U: &Table<CG>,
    Z_tilde_i_0: CG,
    K_tilde_i_0: CG,
    U_i: CG,
    ZU_i: CG,
    KU_i: CG,
    transcript: &mut DigestReader<R>,
  ) -> io::Result<()> {
    let R_Z_tilde_i_0 = class_group.decompress_p(&mut *transcript)?;
    let R_K_tilde_i_0 = class_group.decompress_p(&mut *transcript)?;
    let R_U_i = class_group.decompress_p(&mut *transcript)?;
    let R_ZU_i = class_group.decompress_p(&mut *transcript)?;
    let R_KU_i = class_group.decompress_p(&mut *transcript)?;

    let c = P::from_xof(transcript.0.finalize_xof());
    let c = crate::be_bytes(&c);
    transcript.0.update(&[0]);
    let prime = Pr::prime(crate::ccykc::LAMBDA, transcript.0.finalize_xof());
    let modulus = &prime * &UnsignedInteger::from_be_slice(class_group.p());
    let modulus_bytes = modulus.to_be_bytes();
    let modulus = crypto_bigint::NonZero::new(modulus.0).unwrap();

    let D_Z_tilde_i_0 = class_group.decompress_p(&mut *transcript)?;
    let D_K_tilde_i_0 = class_group.decompress_p(&mut *transcript)?;
    let D_U_i = class_group.decompress_p(&mut *transcript)?;
    let D_ZU_i = class_group.decompress_p(&mut *transcript)?;
    let D_KU_i = class_group.decompress_p(&mut *transcript)?;

    let e_delta_i = crate::ccykc::read_e(&mut *transcript, &modulus)?;
    let e_alpha_i = crate::ccykc::read_e(&mut *transcript, &modulus)?;
    let e_beta_i = crate::ccykc::read_e(&mut *transcript, &modulus)?;
    let e_u_i = crate::ccykc::read_e(&mut *transcript, &modulus)?;

    if CG::mul_once(class_group.identity_p().clone(), D_Z_tilde_i_0, &modulus_bytes)
      .add(&CG::mul(G, &e_delta_i)) !=
      R_Z_tilde_i_0.add(&CG::mul_once(class_group.identity_p().clone(), Z_tilde_i_0, &c))
    {
      Err(io::Error::other("Z_tilde_i.0 PoK was invalid"))?;
    }

    if CG::mul_once(class_group.identity_p().clone(), D_K_tilde_i_0, &modulus_bytes)
      .add(&CG::mul(G, &e_alpha_i)) !=
      R_K_tilde_i_0.add(&CG::mul_once(class_group.identity_p().clone(), K_tilde_i_0, &c))
    {
      Err(io::Error::other("K_tilde_i.0 PoK was invalid"))?;
    }

    if CG::mul_once(class_group.identity_p().clone(), D_U_i, &modulus_bytes)
      .add(&CG::mul(G, &e_beta_i))
      .add(&CG::mul(Y, &e_u_i)) !=
      R_U_i.add(&CG::mul_once(class_group.identity_p().clone(), U_i, &c))
    {
      Err(io::Error::other("U_i.0 PoK was invalid"))?;
    }

    if CG::mul_once(class_group.identity_p().clone(), D_ZU_i, &modulus_bytes)
      .add(&CG::mul(&Z_tilde.1, &e_u_i))
      .add(&CG::mul(neg_U, &e_delta_i))
      .add(&CG::mul(&Z_tilde.0, &e_beta_i)) !=
      R_ZU_i.add(&CG::mul_once(class_group.identity_p().clone(), ZU_i, &c))
    {
      Err(io::Error::other("ZU_i.0 PoK was invalid"))?;
    }

    if CG::mul_once(class_group.identity_p().clone(), D_KU_i, &modulus_bytes)
      .add(&CG::mul(&K_tilde.1, &e_u_i))
      .add(&CG::mul(neg_U, &e_alpha_i))
      .add(&CG::mul(&K_tilde.0, &e_beta_i)) !=
      R_KU_i.add(&CG::mul_once(class_group.identity_p().clone(), KU_i, &c))
    {
      Err(io::Error::other("KU_i.0 PoK was invalid"))?;
    }

    Ok(())
  }
}
