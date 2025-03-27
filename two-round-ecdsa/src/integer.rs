use core::ops::{Add, AddAssign, Mul};

use zeroize::{Zeroize, Zeroizing};
use rand_core::{RngCore, CryptoRng};

use crypto_bigint::{NonZero, BoxedUint};

/// A constant-time variable-size (dynamically-allocated) unsigned integer.
// This wraps BoxedUint with a type which re-allocates as necessary to ensure it never wraps.
#[derive(Clone, Zeroize)]
pub struct UnsignedInteger(pub(crate) BoxedUint);

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

  #[must_use]
  pub(crate) fn div_rem(&self, denominator: &NonZero<BoxedUint>) -> (Zeroizing<Box<[u8]>>, Self) {
    let denominator = denominator.widen(self.0.bits_precision());
    let (d, e) = self.0.div_rem(&denominator);
    let d = Zeroizing::new(d);
    let d = Zeroizing::new(d.to_be_bytes());
    (d, Self(e))
  }
}

impl Add for &UnsignedInteger {
  type Output = UnsignedInteger;
  fn add(self, other: Self) -> UnsignedInteger {
    let new_precision = self.0.bits_precision().max(other.0.bits_precision()) + 1;
    let res = self.0.widen(new_precision);
    UnsignedInteger(&other.0 + res)
  }
}

impl AddAssign for UnsignedInteger {
  fn add_assign(&mut self, other: Self) {
    let new_precision = self.0.bits_precision().max(other.0.bits_precision()) + 1;
    let res = self.0.widen(new_precision);
    *self = Self(&other.0 + res);
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

impl Mul<&BoxedUint> for &UnsignedInteger {
  type Output = UnsignedInteger;
  fn mul(self, other: &BoxedUint) -> UnsignedInteger {
    let new_precision = self.0.bits_precision() + other.bits_precision();
    let mut res = self.0.widen(new_precision);
    res *= other;
    UnsignedInteger(res)
  }
}
