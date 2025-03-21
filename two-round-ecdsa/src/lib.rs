#![cfg_attr(docsrs, feature(doc_auto_cfg))]
#![doc = include_str!("../README.md")]
#![deny(missing_docs)]
#![allow(non_snake_case)]

use zeroize::Zeroize;

use group::{ff::PrimeFieldBits, prime::PrimeGroup};

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
pub trait Parameters {
  /// The elliptic curve.
  type E: PrimeGroup<Scalar = Self::F>;
  /// The scalar field of the elliptic curve.
  type F: Zeroize + PrimeFieldBits;

  /// The eVRF to use.
  type Evrf: Evrf<Self::E>;

  /// Hash the message and reduce it into a scalar.
  fn hash_message(message: &[u8]) -> Self::F;
  /// Reduce the `x`-coordinate of a point into a scalar.
  fn x_coordinate(point: &Self::E) -> Self::F;
}

/// ECDSA over secp256k1.
#[cfg(feature = "secp256k1")]
pub struct Secp256k1;
#[cfg(feature = "secp256k1")]
impl Parameters for Secp256k1 {
  type E = k256::ProjectivePoint;
  type F = k256::Scalar;

  // TODO: Use a secure eVRF
  type Evrf = DummyEvrf;

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
