use core::ops::{Add, Neg, Sub, Mul, Div, Rem};

use subtle::{Choice, ConstantTimeEq};
use zeroize::Zeroize;

use crypto_bigint_xgcd::{
  ConstantTimeSelect, WideningMul, Zero, NonZero, Odd, Integer, Uint, PrecomputeInverter,
  modular::SafeGcdInverter,
};
#[cfg(test)]
use crypto_bigint_xgcd::U256;

pub(crate) fn mul_arbitrary_uints<
  const LHS_LIMBS: usize,
  const RHS_LIMBS: usize,
  const OUTPUT_LIMBS: usize,
>(
  a: Uint<LHS_LIMBS>,
  b: Uint<RHS_LIMBS>,
) -> Uint<OUTPUT_LIMBS> {
  let (c_lo, c_hi) = a.split_mul(&b);
  let c_lo = c_lo.as_words();
  let c_hi = c_hi.as_words();
  let mut res = Uint::<{ OUTPUT_LIMBS }>::ZERO;
  res.as_words_mut()[.. c_lo.len()].copy_from_slice(c_lo);
  res.as_words_mut()[c_lo.len() ..].copy_from_slice(c_hi);
  res
}

// Calculate the difference of two `I`s, returning it and if `b` was greater
fn difference<I: Copy + Integer>(a: &I, b: &I) -> (I, Choice) {
  let b_is_greater = b.ct_gt(a);
  // These may contain equivalent values which is fine for this
  let greater = I::ct_select(a, b, b_is_greater);
  let lesser = I::ct_select(a, b, !b_is_greater);
  let difference = greater - lesser;
  (difference, b_is_greater)
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct IStruct<I: Copy + Integer> {
  positive: Choice,
  value: I,
}
impl<I: Copy + Integer> IStruct<I> {
  pub(crate) fn positive(&self) -> Choice {
    self.positive.into()
  }
  pub(crate) fn abs(&self) -> &I {
    &self.value
  }
  pub(crate) fn into_abs(self) -> I {
    self.value
  }
  #[must_use]
  pub(crate) fn half(mut self) -> Self {
    self.value = self.value >> 1u32;
    self.positive = Choice::ct_select(&self.positive, &1.into(), self.value.ct_eq(&I::zero()));
    self
  }

  pub(crate) fn one() -> Self {
    Self { positive: 1.into(), value: I::one() }
  }

  pub(crate) fn widen<I2: Copy + Integer + From<(I, I)>>(self) -> IStruct<I2> {
    IStruct { positive: self.positive, value: I2::from((self.value, I::zero())) }
  }
}
impl<const LIMBS: usize> IStruct<Uint<LIMBS>> {
  pub(crate) fn mul_i_uint<const RHS_LIMBS: usize, const OUTPUT_LIMBS: usize>(
    self,
    other: IStruct<Uint<RHS_LIMBS>>,
  ) -> IStruct<Uint<OUTPUT_LIMBS>> {
    let value = mul_arbitrary_uints(self.value, other.value);
    // (positive * positive) | (negative * negative) | (0 * either)
    let positive = self.positive.ct_eq(&other.positive) | value.is_zero();
    IStruct { positive, value }
  }
}
impl<I: Copy + Integer> From<I> for IStruct<I> {
  fn from(value: I) -> Self {
    IStruct { positive: 1.into(), value }
  }
}
impl<I: Copy + Integer> Add<I> for IStruct<I> {
  type Output = IStruct<I>;
  fn add(self, other: I) -> IStruct<I> {
    let same_sign = IStruct { positive: self.positive, value: self.value + other };

    let other_positive = Choice::from(1);
    let (difference, other_is_greater) = difference(&self.value, &other);
    let greater_positive = Choice::ct_select(&self.positive, &other_positive, other_is_greater);
    // If they have different signs, the greater number's sign is preserved
    let not_same_sign = IStruct { positive: greater_positive, value: (difference) };

    IStruct::ct_select(&not_same_sign, &same_sign, self.positive.ct_eq(&other_positive))
  }
}
impl<I: Copy + Integer> Add for IStruct<I> {
  type Output = IStruct<I>;
  fn add(self, other: Self) -> IStruct<I> {
    let same_sign = IStruct { positive: self.positive, value: self.value + other.value };

    let (difference, other_is_greater) = difference(&self.value, &other.value);
    let greater_positive = Choice::ct_select(&self.positive, &other.positive, other_is_greater);
    let not_same_sign = IStruct { positive: greater_positive, value: (difference) };

    IStruct::ct_select(&not_same_sign, &same_sign, self.positive.ct_eq(&other.positive))
  }
}
impl<I: Copy + Integer> Sub for IStruct<I> {
  type Output = IStruct<I>;
  fn sub(self, other: Self) -> IStruct<I> {
    let sum = self.value + other.value;
    let (difference, other_is_greater) = difference(&self.value, &other.value);
    IStruct {
      positive: Choice::ct_select(&self.positive, &!other.positive, other_is_greater),
      value: I::ct_select(&sum, &(difference), self.positive.ct_eq(&other.positive)),
    }
  }
}
impl<I: Copy + Integer> Neg for IStruct<I> {
  type Output = Self;
  fn neg(mut self) -> Self {
    // Perform the negation
    // self.sign = !self.sign;
    // If we had +0, preserve it as +0
    // self.sign = <_>::ct_select(&self.sign, &1.into(), self.value.ct_eq(&I::zero()));

    // Positive if zero or if prior negative, negative otherwise
    self.positive = <_>::ct_select(&0.into(), &1.into(), self.value.is_zero() | (!self.positive));
    self
  }
}

impl<IRhs: Integer, I: Copy + WideningMul<IRhs, Output: Copy> + Integer> Mul<IRhs> for IStruct<I> {
  type Output = IStruct<<I as WideningMul<IRhs>>::Output>;
  fn mul(self, other: IRhs) -> Self::Output {
    let value = self.value.widening_mul(other);
    IStruct { positive: self.positive | value.is_zero(), value }
  }
}
impl<IRhs: Copy + Integer, I: Copy + WideningMul<IRhs, Output: Copy> + Integer> Mul<IStruct<IRhs>>
  for IStruct<I>
{
  type Output = IStruct<<I as WideningMul<IRhs>>::Output>;
  fn mul(self, other: IStruct<IRhs>) -> Self::Output {
    let value = self.value.widening_mul(other.value);
    // (positive * positive) | (negative * negative) | (0 * either)
    let positive = self.positive.ct_eq(&other.positive) | value.is_zero();
    IStruct { positive, value }
  }
}

// These divisions are euclidean
impl<const LIMBS: usize> Div<Uint<LIMBS>> for IStruct<Uint<LIMBS>> {
  type Output = (IStruct<Uint<LIMBS>>, Uint<LIMBS>);
  fn div(self, denominator: Uint<LIMBS>) -> Self::Output {
    let (mut d, mut e) = self.value.div_rem(&NonZero::new(denominator).unwrap());

    let increment = (!self.positive) & (!e.ct_eq(&Uint::ZERO));
    d = Uint::ct_select(&d, &(d + Uint::one()), increment);
    // Since we're dividing by an unsigned number, the sign inherits from the numerator
    let d = IStruct { positive: self.positive, value: d };
    e = Uint::ct_select(&e, &(denominator - e), increment);

    (d, e)
  }
}
impl<const LIMBS: usize> Div for IStruct<Uint<LIMBS>> {
  type Output = (IStruct<Uint<LIMBS>>, Uint<LIMBS>);
  fn div(self, denominator: Self) -> Self::Output {
    let (mut d, mut e) = self.value.div_rem(&NonZero::new(denominator.value).unwrap());

    let increment = (!self.positive) & (!e.ct_eq(&Uint::ZERO));
    d = Uint::ct_select(&d, &(d + Uint::one()), increment);
    e = Uint::ct_select(&e, &(denominator.value - e), increment);

    // (positive * positive) | (negative * negative) | (0 / either)
    let d = IStruct {
      positive: self.positive.ct_eq(&denominator.positive) | d.ct_eq(&Uint::ZERO),
      value: d,
    };
    (d, e)
  }
}
impl<I: Copy + Rem<Output = I> + Integer> Rem<I> for IStruct<I> {
  type Output = I;
  fn rem(self, modulus: I) -> I {
    let rem = self.value % modulus;
    I::ct_select(&(modulus - rem), &rem, self.positive)
  }
}
impl<I: Copy + Integer> ConstantTimeEq for IStruct<I> {
  fn ct_eq(&self, b: &Self) -> Choice {
    self.positive.ct_eq(&b.positive) & self.value.ct_eq(&b.value)
  }
}
impl<I: Copy + Integer> ConstantTimeSelect for IStruct<I> {
  fn ct_select(a: &Self, b: &Self, choice: Choice) -> Self {
    Self {
      positive: Choice::ct_select(&a.positive, &b.positive, choice),
      value: I::ct_select(&a.value, &b.value, choice),
    }
  }
}
impl<I: Copy + Zeroize + Integer> Zeroize for IStruct<I> {
  fn zeroize(&mut self) {
    self.positive = Choice::ct_select(&0.into(), &1.into(), 1.into());
    self.value.zeroize();
  }
}

pub(crate) trait ExtendedGcd: Copy + Sized + Integer {
  fn extended_gcd_part(self, other: Self) -> (Self, Self);
  fn extended_gcd(self, other: Self) -> (Self, Self, IStruct<Self>);
}
impl<const LIMBS: usize, const UNSAT_LIMBS: usize> ExtendedGcd for Uint<LIMBS>
where
  Odd<Self>: PrecomputeInverter<Inverter = SafeGcdInverter<LIMBS, UNSAT_LIMBS>>,
{
  fn extended_gcd_part(self, other: Self) -> (Self, Self) {
    debug_assert!(bool::from((!self.ct_eq(&Self::zero())) | (!other.ct_eq(&Self::zero()))));

    /* TODO: Move to this once `binxgcd` is fixed. Right now, the debug_assert occassionally trips.
    let res = self.binxgcd(&other);
    debug_assert!(!bool::from(
      Choice::from(res.x.is_negative()) & Choice::from(res.y.is_negative())
    ));
    let g = res.gcd;
    let u = res.x;

    let u_abs = u.abs();
    let u = <_>::ct_select(&u_abs, &(other / g).saturating_sub(&u_abs), u.is_negative().into());

    (g, u)
    */

    let a = self;
    let b = other;
    let gcd = a.bingcd(&b);

    let a_is_zero = a.ct_eq(&Self::zero());
    let b_is_zero = b.ct_eq(&Self::zero());
    let a_eq_b = a.ct_eq(&b);
    let special_case = a_is_zero | b_is_zero | a_eq_b;

    // Calculate the multiplicative inverse of `(a / g) % (b / g)`, which is `u`
    let u = |a: Self, b: Self, gcd: Self| {
      let gcd = NonZero::new(gcd).unwrap();
      let a_div_g = a / gcd;
      let b_div_g = b / gcd;
      a_div_g.inv_mod(&b_div_g).unwrap()
    };

    // Call with `a, b, gcd` if not a special case and `1, 2, 1` if a special case
    let u = u(
      Self::ct_select(&a, &Self::one(), special_case),
      Self::ct_select(&b, &Self::from(2u8), special_case),
      Self::ct_select(&gcd, &Self::one(), special_case),
    );

    // Correct for the cases `a == 0`, `b == 0`
    let u = Self::ct_select(&u, &(Self::zero()), a_is_zero);
    let u = Self::ct_select(&u, &Self::one(), b_is_zero);

    // Correct for the case `a == b`
    let u = Self::ct_select(&u, &Self::one(), a_eq_b);

    (gcd, u)
  }

  fn extended_gcd(self, other: Self) -> (Self, Self, IStruct<Self>) {
    debug_assert!(bool::from((!self.ct_eq(&Self::zero())) | (!other.ct_eq(&Self::zero()))));

    let (gcd, u) = self.extended_gcd_part(other);
    let gcd = gcd;
    let a = self;
    let b = other;

    let b_is_zero = b.ct_eq(&Self::zero());

    // Calculate `v` for `ua + vb = g`
    let v = |b: Self| {
      let ua = u * a;
      let (difference, _gcd_is_greater) = difference(&ua, &gcd);
      let (v, rem) = difference.div_rem(&NonZero::new(b).unwrap());
      debug_assert!(bool::from(rem.ct_eq(&Self::zero())));

      let v = IStruct::from(v);
      // We prefer `u` to be positive and `v` to be negative, yet `v` will be positive if `u` is
      // zero
      // TODO: ct_neg
      IStruct::ct_select(&v, &-v.clone(), !u.ct_eq(&Self::zero()))
    };

    // Call with `b` if not a special case and `1` if `b == 0`
    let v = v(Self::ct_select(&b, &Self::one(), b_is_zero));

    // Correct for the case `b == 0`
    let v = IStruct::ct_select(&v, &IStruct::from(Self::zero()), b_is_zero);

    (gcd, u, v)
  }
}

#[test]
fn test_integer_sub() {
  // Positive minus smaller positive
  {
    let res = IStruct::from(U256::from(2u8)) - IStruct::from(U256::one());
    assert!(bool::from(res.positive.ct_eq(&1.into())));
    assert!(bool::from(res.value.ct_eq(&U256::one())));
  }
  // Positive minus smaller negative
  {
    let res = IStruct::from(U256::from(2u8)) - -IStruct::from(U256::one());
    assert!(bool::from(res.positive.ct_eq(&1.into())));
    assert!(bool::from(res.value.ct_eq(&U256::from(3u8))));
  }
  // Positive minus larger positive
  {
    let res = IStruct::from(U256::from(2u8)) - IStruct::from(U256::from(3u8));
    assert!(bool::from(res.positive.ct_eq(&0.into())));
    assert!(bool::from(res.value.ct_eq(&U256::one())));
  }
  // Positive minus larger negative
  {
    let res = IStruct::from(U256::from(2u8)) - -IStruct::from(U256::from(3u8));
    assert!(bool::from(res.positive.ct_eq(&1.into())));
    assert!(bool::from(res.value.ct_eq(&U256::from(5u8))));
  }
  // Negative minus smaller positive
  {
    let res = -IStruct::from(U256::from(2u8)) - IStruct::from(U256::one());
    assert!(bool::from(res.positive.ct_eq(&0.into())));
    assert!(bool::from(res.value.ct_eq(&U256::from(3u8))));
  }
  // Negative minus smaller negative
  {
    let res = -IStruct::from(U256::from(2u8)) - -IStruct::from(U256::one());
    assert!(bool::from(res.positive.ct_eq(&0.into())));
    assert!(bool::from(res.value.ct_eq(&U256::one())));
  }
  // Negative minus larger positive
  {
    let res = -IStruct::from(U256::from(2u8)) - IStruct::from(U256::from(3u8));
    assert!(bool::from(res.positive.ct_eq(&0.into())));
    assert!(bool::from(res.value.ct_eq(&U256::from(5u8))));
  }
  // Negative minus larger negative
  {
    let res = -IStruct::from(U256::from(2u8)) - -IStruct::from(U256::from(3u8));
    assert!(bool::from(res.positive.ct_eq(&1.into())));
    assert!(bool::from(res.value.ct_eq(&U256::one())));
  }
}

#[test]
fn test_integer_div() {
  let two = IStruct::from(U256::from(2u8));
  let neg_two = -two.clone();
  let three = U256::from(3u8);

  {
    let (res, rem) = two / three;
    assert!(bool::from(res.positive.ct_eq(&1.into())));
    assert_eq!(res.value, U256::zero());
    assert_eq!(rem, two.value);
  }
  {
    let (res, rem) = -IStruct::from(U256::from(6u8)) / three;
    assert!(bool::from(res.positive.ct_eq(&0.into())));
    assert_eq!(res.value, U256::from(2u8));
    assert_eq!(rem, U256::zero());
  }
  {
    let (res, rem) = neg_two / three;
    assert!(bool::from(res.positive.ct_eq(&0.into())));
    assert_eq!(res.value, U256::one());
    assert_eq!(rem, U256::one());
  }

  let three = IStruct::from(three);
  {
    let (res, rem) = two / three;
    assert!(bool::from(res.positive.ct_eq(&1.into())));
    assert_eq!(res.value, U256::zero());
    assert_eq!(rem, two.value);
  }
  {
    let (res, rem) = neg_two / three;
    assert!(bool::from(res.positive.ct_eq(&0.into())));
    assert_eq!(res.value, U256::one());
    assert_eq!(rem, U256::one());
  }

  let neg_three = -three;
  {
    let (res, rem) = two / neg_three;
    assert!(bool::from(res.positive.ct_eq(&1.into())));
    assert_eq!(res.value, U256::zero());
    assert_eq!(rem, two.value);
  }
  {
    let (res, rem) = neg_two / neg_three;
    assert!(bool::from(res.positive.ct_eq(&1.into())));
    assert_eq!(res.value, U256::one());
    assert_eq!(rem, U256::one());
  }
}

#[test]
fn gcd() {
  // Ensure the underlying crypto-bigint handles the case where one is zero correctly
  assert_eq!(U256::one().gcd(&U256::zero()), U256::one());

  {
    let (gcd, u, v) = U256::one().extended_gcd(U256::zero());
    assert_eq!(gcd, U256::one());
    assert_eq!(u, U256::one());
    assert!(bool::from(v.positive.ct_eq(&1.into())));
    assert_eq!(v.value, U256::zero());
  }

  {
    let (gcd, u, v) = U256::zero().extended_gcd(U256::one());
    assert_eq!(gcd, U256::one());
    assert_eq!(u, U256::zero());
    assert!(bool::from(v.positive.ct_eq(&1.into())));
    assert_eq!(v.value, U256::one());
  }

  {
    let (gcd, u, v) = U256::from(2u8).extended_gcd(U256::from(3u8));
    assert_eq!(gcd, U256::one());
    assert_eq!(u, U256::from(2u8));
    assert!(bool::from(v.positive.ct_eq(&0.into())));
    assert_eq!(v.value, U256::one());
  }

  {
    let (gcd, u, v) = (U256::from(4u8)).extended_gcd(U256::from(8u8));
    assert_eq!(gcd, U256::from(4u8));
    assert_eq!(u, U256::one());
    assert!(bool::from(v.positive.ct_eq(&1.into())));
    assert_eq!(v.value, U256::zero());
  }

  {
    let (gcd, u, v) = (U256::from(8u8)).extended_gcd(U256::from(4u8));
    assert_eq!(gcd, U256::from(4u8));
    assert_eq!(u, U256::ZERO);
    assert!(bool::from(v.positive.ct_eq(&1.into())));
    assert_eq!(v.value, U256::one());
  }

  {
    let (gcd, u, v) = (U256::from(4u8)).extended_gcd(U256::from(10u8));
    assert_eq!(gcd, U256::from(2u8));
    assert_eq!(u, U256::from(3u8));
    assert!(bool::from(v.positive.ct_eq(&0.into())));
    assert_eq!(v.value, U256::one());
  }

  {
    let (gcd, u, v) = U256::from(2u8).extended_gcd(U256::from(2u8));
    assert_eq!(gcd, U256::from(2u8));
    assert_eq!(u, U256::one());
    assert!(bool::from(v.positive.ct_eq(&1.into())));
    assert_eq!(v.value, U256::zero());
  }

  {
    let (gcd, u, v) = (U256::from(10u8)).extended_gcd(U256::from(4u8));
    assert_eq!(gcd, U256::from(2u8));
    assert_eq!(u, U256::from(1u8));
    assert!(bool::from(v.positive.ct_eq(&0.into())));
    assert_eq!(v.value, U256::from(2u8));
  }

  {
    let a = crypto_bigint_xgcd::U512::from_be_hex(concat!(
      "0000000000000000000000000000000000000000000000000000000000000000",
      "000000000000000000000000000000000000001A0DEEF6F3AC2566149D925044"
    ));
    let b = crypto_bigint_xgcd::U512::from_be_hex(concat!(
      "0000000000000000000000000000000000000000000000000000000000000000",
      "000000000000072B69C9DD0AA15F135675EA9C5180CF8FF0A59298CFC92E87FA"
    ));
    let (gcd, u, v) = a.extended_gcd(b);
    // u * a + v * b = g
    // v is either 0 or negative, so this is equivalent to
    // u * a - |v| * b = g
    // which is equivalent to
    // u * a = g + |v| * b
    assert_eq!(u * a, gcd + (v.value * b));
  }
}
