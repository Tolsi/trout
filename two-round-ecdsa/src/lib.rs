#![cfg_attr(docsrs, feature(doc_auto_cfg))]
#![doc = include_str!("../README.md")]
#![deny(missing_docs)]
#![allow(non_snake_case)]

use core::marker::PhantomData;
use std::io;

use zeroize::Zeroize;

use group::{ff::PrimeFieldBits, GroupEncoding, prime::PrimeGroup};
use class_groups::Element;

mod integer;
pub use integer::UnsignedInteger;

mod proofs;
pub use proofs::*;

mod key_gen;
pub use key_gen::*;

mod sign;
pub use sign::*;

pub(crate) fn be_bytes<F: PrimeFieldBits>(scalar: &F) -> Vec<u8> {
  let mut bytes = vec![0; F::NUM_BITS.div_ceil(8).try_into().unwrap()];
  for (i, bit) in scalar.to_le_bits().iter().enumerate() {
    // The least-significant bit goes into the last unpopulated byte
    let byte = bytes.len() - ((i / 8) + 1);
    bytes[byte] |= u8::from(*bit) << (i % 8);
  }
  bytes
}

/// ECDSA parameters.
pub trait Parameters<CG: Element>: Sized {
  /// The elliptic curve.
  type E: PrimeGroup<Scalar = Self::F>;
  /// The scalar field of the elliptic curve.
  type F: Zeroize + PrimeFieldBits;

  /// The eVRF to use.
  type Evrf: Evrf<CG, Self>;
  /// The round one proofs.
  type RoundOneProofs: RoundOneProofs<CG, Self>;
  /// The round two proofs.
  type RoundTwoProofs: RoundTwoProofs<CG, Self>;

  /// Read a `E` while enforcing a canonical encoding.
  ///
  /// The provided implementation assumes encodings are always canonical and re-encodes to check
  /// equality to what was decoded.
  fn read_canonical_E(mut reader: impl io::Read) -> io::Result<Self::E> {
    let mut bytes = <Self::E as GroupEncoding>::Repr::default();
    reader.read_exact(bytes.as_mut())?;
    let res = Option::<Self::E>::from(Self::E::from_bytes(&bytes))
      .ok_or_else(|| io::Error::other("invalid encoding of E"))?;
    if res.to_bytes().as_ref() != bytes.as_ref() {
      Err(io::Error::other("non-canonical encoding of E"))?;
    }
    Ok(res)
  }

  /// Derive a scalar from an XOF.
  fn from_xof(xof: blake3::OutputReader) -> Self::F;
  /// Hash the message and reduce it into a scalar.
  fn hash_message(message: &[u8]) -> Self::F;
  /// Reduce the `x`-coordinate of a point into a scalar.
  fn x_coordinate(point: &Self::E) -> Self::F;
}

/// ECDSA over secp256k1.
#[cfg(feature = "secp256k1")]
pub struct Secp256k1<CG: Element, P: Primes>(PhantomData<(CG, P)>);
#[cfg(feature = "secp256k1")]
impl<CG: Element, P: Primes> Parameters<CG> for Secp256k1<CG, P> {
  type E = k256::ProjectivePoint;
  type F = k256::Scalar;

  // TODO: Use proper proofs
  type Evrf = DummyEvrf;
  type RoundOneProofs = Ccykc2023RoundOne<P>;
  type RoundTwoProofs = Ccykc2023RoundTwo<P>;

  fn from_xof(mut xof: blake3::OutputReader) -> Self::F {
    let mut bytes = [0; 64];
    xof.fill(&mut bytes);
    use k256::elliptic_curve::ops::Reduce;
    <k256::Scalar as Reduce<k256::elliptic_curve::bigint::U512>>::reduce_bytes(&bytes.into())
  }
  fn hash_message(message: &[u8]) -> Self::F {
    use sha2::{Digest, Sha256};
    use k256::elliptic_curve::ops::Reduce;
    <k256::Scalar as Reduce<k256::U256>>::reduce_bytes(&Sha256::digest(message))
  }
  fn x_coordinate(point: &Self::E) -> Self::F {
    use k256::elliptic_curve::{ops::Reduce, point::AffineCoordinates};
    <k256::Scalar as Reduce<k256::U256>>::reduce_bytes(&point.to_affine().x())
  }
}
