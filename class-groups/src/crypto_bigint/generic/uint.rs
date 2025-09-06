use subtle::{ConditionallySelectable, Choice};

use crypto_bigint::{ConstZero, CheckedDiv, Concat, Split, Limb, Uint};

use super::Limbs;

impl<const LIMBS: usize> Limbs for Uint<LIMBS>
where
  Uint<LIMBS>:
    Concat<Output: ConditionallySelectable + ConstZero + CheckedDiv + Split<Output = Self>>,
{
  fn zero(_limbs: usize) -> Self {
    Self::ZERO
  }
  fn is_zero(&self) -> Choice {
    <Self as crypto_bigint::Zero>::is_zero(self)
  }

  fn as_limbs(&self) -> &[Limb] {
    Uint::as_limbs(self)
  }
  fn as_mut_limbs(&mut self) -> &mut [Limb] {
    Uint::as_mut_limbs(self)
  }

  fn shl(&self, bits: u32) -> Self {
    self.overflowing_shl(bits).unwrap_or(Self::ZERO)
  }

  fn carrying_add(&self, b: &Self, carry: Limb) -> (Self, Limb) {
    self.carrying_add(b, carry)
  }
  fn widening_square(&self) -> (Self, Self) {
    self.square_wide()
  }
  fn wrapping_div(num: (Self, Self), denom: &Self) -> Self {
    let concatenated: <Self as Concat>::Output = Concat::concat(&num.0, &num.1);
    let quotient = <<Self as Concat>::Output as CheckedDiv>::checked_div(
      &concatenated,
      &Concat::concat(denom, &Self::ZERO),
    )
    .unwrap_or(<<Self as Concat>::Output as ConstZero>::ZERO);
    <<Self as Concat>::Output as Split>::split(&quotient).0
  }
}
