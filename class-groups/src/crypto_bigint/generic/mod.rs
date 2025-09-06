use subtle::{ConstantTimeEq, Choice};

use crypto_bigint::{BitOps, Limb};

mod uint;
mod boxed_uint;

mod reduction;
pub(crate) use reduction::reduce;

/// A collection of limbs and associated helper methods, all expected to execute in constant-time.
///
/// The provided algorithms frequentally dance along Limb boundaries, performance requiring correct
/// decision of when to terminate execution of a given function. This API unifies `Uint` and
/// `BoxedUint` (in a way `Integer` appeared ineligible for) while providing the niche methods
/// required for performance.
trait Limbs: Sized + ConstantTimeEq + BitOps {
  fn zero(limbs: usize) -> Self;
  fn is_zero(&self) -> Choice;

  fn as_limbs(&self) -> &[Limb];
  fn as_mut_limbs(&mut self) -> &mut [Limb];

  fn shl(&self, bits: u32) -> Self;
  fn carrying_add(&self, b: &Self, carry: Limb) -> (Self, Limb);
  fn widening_square(&self) -> (Self, Self);
  // Divide `num`  by `denom`, returning the low bits.
  //
  // Returns `0` if passed `0` for the denominator.
  fn wrapping_div(num: (Self, Self), denom: &Self) -> Self;

  fn double(&self, limbs: usize) -> Self {
    let mut two_a = <Self as Limbs>::zero(limbs);
    for l in (1 .. limbs).rev() {
      two_a.as_mut_limbs()[l] =
        (self.as_limbs()[l] << 1) | (self.as_limbs()[l - 1] >> (Limb::BITS - 1));
    }
    two_a.as_mut_limbs()[0] = self.as_limbs()[0] << 1;
    two_a
  }

  #[allow(unused)]
  fn ct_eq(a: &Self, b: &Self, limbs: usize) -> Choice {
    let mut res = Choice::from(1u8);
    for l in 0 .. limbs {
      res &= a.as_limbs()[l].ct_eq(&b.as_limbs()[l]);
    }
    res
  }

  fn ct_select(a: &Self, b: &Self, limbs: usize, choice: Choice) -> Self {
    let mut res = Self::zero(limbs);
    for l in 0 .. limbs {
      res.as_mut_limbs()[l] = <_ as crypto_bigint::ConstantTimeSelect>::ct_select(
        &a.as_limbs()[l],
        &b.as_limbs()[l],
        choice,
      );
    }
    res
  }

  fn gt(&self, b: &Self, limbs: usize) -> Choice {
    let mut carry = Limb::ZERO;
    for l in 0 .. limbs {
      (_, carry) = b.as_limbs()[l].borrowing_sub(self.as_limbs()[l], carry);
    }
    Choice::from((carry.0 & 1) as u8)
  }

  fn lt(&self, b: &Self, limbs: usize) -> Choice {
    let mut carry = Limb::ZERO;
    for l in 0 .. limbs {
      (_, carry) = self.as_limbs()[l].borrowing_sub(b.as_limbs()[l], carry);
    }
    Choice::from((carry.0 & 1) as u8)
  }
}
