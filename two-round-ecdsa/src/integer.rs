use core::ops::{Add, Mul};

use zeroize::{Zeroize, Zeroizing};
use rand_core::{RngCore, CryptoRng};

use crypto_bigint::BoxedUint;

/// A constant-time variable-size (dynamically-allocated) unsigned integer.
// This wraps BoxedUint with a type which re-allocates as necessary to ensure it never wraps.
#[derive(Clone, Zeroize)]
pub struct UnsignedInteger(BoxedUint);

impl UnsignedInteger {
  #[must_use]
  pub(crate) fn to_be_bytes(&self) -> Box<[u8]> {
    self.0.to_be_bytes()
  }

  #[must_use]
  pub(crate) fn from_be_slice(slice: &[u8]) -> Self {
    Self(BoxedUint::from_be_slice(slice, u32::try_from(slice.len() * 8).unwrap()).unwrap())
  }

  #[must_use]
  pub(crate) fn random(bits: u32, rng: &mut (impl RngCore + CryptoRng)) -> Self {
    let mut bytes = Zeroizing::new(vec![0; bits.div_ceil(8).try_into().unwrap()]);
    rng.fill_bytes(&mut bytes);
    // If we created 8 bits when we were only supposed to create 5 bits...
    if (bits % 8) != 0 {
      // Clear the top bits which shouldn't have been generated
      bytes[0] &= (1 << (bits % 8)) - 1;
    }
    Self(BoxedUint::from_be_slice(&bytes, bits).unwrap())
  }
}

impl Add for &UnsignedInteger {
  type Output = UnsignedInteger;
  fn add(self, other: Self) -> UnsignedInteger {
    let new_precision = self.0.bits_precision().max(other.0.bits_precision()) + 1;
    let mut res = self.0.widen(new_precision);
    res += &other.0;
    UnsignedInteger(res)
  }
}

impl Mul for &UnsignedInteger {
  type Output = UnsignedInteger;
  fn mul(self, other: Self) -> UnsignedInteger {
    let new_precision = self.0.bits_precision() + other.0.bits_precision();
    let mut res = self.0.widen(new_precision);
    res *= &other.0;
    UnsignedInteger(res)
  }
}
