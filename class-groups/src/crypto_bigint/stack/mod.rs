use core::ops::Neg;

use subtle::{ConstantTimeEq, ConstantTimeLess, ConstantTimeGreater};
use zeroize::Zeroize;

use crypto_bigint_xgcd::{ConstantTimeSelect, Zero, NonZero, Uint};

use crate::Table;

mod numbers;
use numbers::*;

// 2048-bit fundamental discriminant with 256-bit subgroup = 2560-bit discriminant
/*
  We use a further 128 bits for the misc additions/shifts we perform during steps. While ideally,
  we'd only use a further 64 bits, we need an even amount of limbs inside crypto-bigint.
*/
const BITS: u32 = 2688;

// We use `U` to represent `a` which is bounded by the square root of the absolute value of the
// discriminant, so its bit-length will be half of the absolute value of the discriminant's
const A_BITS: u32 = BITS / 2;
type U = Uint<{ crypto_bigint_xgcd::nlimbs!(A_BITS) }>;
// We use `I` to represent `b` which is bounded `-a < b < a`, so its absolute value fits into the
// same amount of bits as `a` does
type I = IStruct<Uint<{ crypto_bigint_xgcd::nlimbs!(A_BITS) }>>;

type WideU = Uint<{ crypto_bigint_xgcd::nlimbs!(BITS) }>;
type WideI = IStruct<WideU>;

type WideWideU = Uint<{ crypto_bigint_xgcd::nlimbs!(2 * BITS) }>;
type WideWideI = IStruct<WideWideU>;

/// A constant-time element of a class group, implemented via crypto-bigint's `Uint, Int`.
///
/// This is implemented in time variable to the discriminant yet constant to `a, b`. This prevents
/// timing analysis from leaking the elements being composed. It is only recommended for provers as
/// it has a significant performance overhead to other backends, which verifiers should take
/// advantage of.
///
/// The usage of `Uint, Int` means these elements live on the stack and are fixed size. They
/// accordingly only support discriminants of bounded size. Using a larger discriminant may cause a
/// runtime panic. The officially supported bound is a 2560-bit discriminant.
// TODO: Parameterize bits at a higher level
#[derive(Clone, Debug)]
pub struct CryptoBigintStackElement {
  a: U,
  b: I,
  discriminant: WideI,
}

impl PartialEq for CryptoBigintStackElement {
  fn eq(&self, other: &Self) -> bool {
    (self.a.ct_eq(&other.a) & self.b.ct_eq(&other.b) & self.discriminant.ct_eq(&other.discriminant))
      .into()
  }
}
impl Eq for CryptoBigintStackElement {}

impl Zeroize for CryptoBigintStackElement {
  fn zeroize(&mut self) {
    // Zeroize
    self.a.zeroize();
    self.b.zeroize();

    // Set to the identity
    self.a = U::ONE;
    self.b = I::one();
  }
}

impl crypto_bigint_xgcd::ConstantTimeSelect for CryptoBigintStackElement {
  fn ct_select(a: &Self, b: &Self, choice: subtle::Choice) -> Self {
    Self {
      a: U::ct_select(&a.a, &b.a, choice),
      b: I::ct_select(&a.b, &b.b, choice),
      // Safe since `Element` is documented to have undefined behavior when mixed across class
      // groups
      discriminant: a.discriminant,
    }
  }
}

impl CryptoBigintStackElement {
  // Algorithm 5.4.2 of A Course in Computational Algebraic Number Theory
  fn reduce(log_2_a_bound: u32, mut a: WideU, mut b: WideI, discriminant: WideI) -> Self {
    let mut c: WideU = {
      // The `b` from composition is `% 2a`, so at most `b**2 = (2a-1)**2`. We increase this bound
      // to `b**2 = 4 a**2`. `(4 a**2) / 4a` would be `a`, meaning `c <= a` even for `a, b`
      // directly from the composition formulas (and unreduced).

      // b**2 - 4ac = discriminant
      // b**2 = discriminant + 4ac
      // b**2 - discriminant = 4ac
      let wide_discriminant: WideWideI = discriminant.widen();
      let four_ac: WideWideI = (b * b) - wide_discriminant;
      // `b**2` is positive, and `4ac` must be since subtracting it equals a negative number
      // Since `a` is positive, `c` also must be positive
      debug_assert!(bool::from(four_ac.positive()));
      let four_ac: WideWideU = four_ac.into_abs();
      let ac: WideWideU = four_ac >> 2;
      let (c, rem): (WideWideU, WideWideU) =
        ac.div_rem(&NonZero::new(WideWideU::from((a, WideU::ZERO))).unwrap());
      debug_assert!(bool::from(rem.ct_eq(&WideWideU::ZERO)));
      let (lo, hi) = c.split();
      debug_assert!(bool::from(hi.ct_eq(&WideU::ZERO)));
      lo
    };

    // First, we establish the bound on the amount of iterations
    let iterations = 2 + (log_2_a_bound - (discriminant.abs().bits().div_ceil(2) - 1));

    // We start our reduction by implementing step 1 and step 3
    let mut done = {
      // If b is negative or zero, then we check `a > b.abs()`
      let mut neg_a_less_than_b = ((!b.positive()) | b.abs().is_zero()) & a.ct_gt(b.abs());
      // If b is positive and non-zero, `-a` will always be `< b` as `a` is in range `[0 ..]`
      neg_a_less_than_b |= (!b.abs().is_zero()) & b.positive();
      let b_less_than_or_equal_to_a = (!b.positive()) | b.abs().ct_lt(&a) | b.abs().ct_eq(&a);

      let jump_to_step_three = neg_a_less_than_b & b_less_than_or_equal_to_a;

      // Continuation clause
      let to_continue = a.ct_gt(&c);
      // Only perform these writes if we jumped to step 3 and should continue
      let prepare_for_next_step = jump_to_step_three & to_continue;
      let neg_b = -b;
      b = <_>::ct_select(&b, &neg_b, prepare_for_next_step);
      let a_copy = a;
      a = <_>::ct_select(&a, &c, prepare_for_next_step);
      c = <_>::ct_select(&c, &a_copy, prepare_for_next_step);

      // Termination clause
      let should_neg_b = a.ct_eq(&c) & (!b.positive());
      b = <_>::ct_select(&b, &neg_b, jump_to_step_three & (!to_continue) & should_neg_b);

      jump_to_step_three & (!to_continue)
    };

    for _ in 0 .. iterations {
      let two_a: WideU = a << 1;
      // b / 2a
      let (mut q, r): (WideI, WideU) = b / WideI::from(two_a);
      let r_gt_a = r.ct_gt(&a);
      q = <_>::ct_select(&q, &(q + WideI::one()), r_gt_a);
      let mut r = WideI::from(r);
      r = <_>::ct_select(&r, &(r - WideI::from(two_a)), r_gt_a);

      // Write the reduced `(c, b)` if we aren't already done
      let b_r = (b + r).half();
      let next_c = WideI::from(c).widen::<WideWideU>() - (b_r * q);
      debug_assert!(bool::from(next_c.positive()));
      // This is safe as for unreduced `a`, `c <= a / 2`
      let (next_c_lo, next_c_hi) = next_c.into_abs().split();
      debug_assert!(bool::from(done | next_c_hi.is_zero()));
      c = <_>::ct_select(&c, &next_c_lo, !done);
      b = <_>::ct_select(&b, &r, !done);

      // Step 3

      // Continuation clause
      let to_continue = a.ct_gt(&c);
      let prepare_for_next_step = !done & to_continue;
      let neg_b = -b;
      b = <_>::ct_select(&b, &neg_b, prepare_for_next_step);
      let a_copy = a;
      a = <_>::ct_select(&a, &c, prepare_for_next_step);
      c = <_>::ct_select(&c, &a_copy, prepare_for_next_step);

      // Termination clause
      done = !prepare_for_next_step;
      let should_neg_b = a.ct_eq(&c) & (!b.positive());
      b = <_>::ct_select(&b, &neg_b, done & should_neg_b);
    }
    debug_assert!(bool::from(done));

    let (a_lo, a_hi): (U, U) = a.split();
    debug_assert!(bool::from(a_hi.is_zero()));
    let a = a_lo;

    let b_positive = b.positive();
    let (b_lo, b_hi): (U, U) = b.into_abs().split();
    debug_assert!(bool::from(b_hi.is_zero()));
    let b = I::from(b_lo);
    let b = <_>::ct_select(&-b, &b, b_positive);

    Self { a, b, discriminant }
  }
}

impl crate::Element for CryptoBigintStackElement {
  const MAX_TABLE_BITS: u32 = 8;

  fn is_identity(&self) -> subtle::Choice {
    self.a.ct_eq(&U::ONE) & self.b.ct_eq(&I::one())
  }

  // Allegedly, Arndt's method, as specified on the Wikipedia page for binary quadratic forms
  fn add(&self, other: &Self) -> CryptoBigintStackElement {
    let B_mu: I = (self.b + other.b).half();

    let A1_A2_xgcd = self.a.extended_gcd(other.a);
    let e: U = A1_A2_xgcd.0.bingcd(B_mu.abs());
    let e = NonZero::new(e).unwrap();
    let A1_div_e: U = self.a / e;
    let A2_div_e: U = other.a / e;
    let A: WideU = A1_div_e.widening_mul(&A2_div_e);

    let mod_1: U = A1_div_e << 1;
    let mod_2: U = A2_div_e << 1;
    let two_A: WideU = A << 1;
    let mut mod_3 = two_A;

    let congruence_1 = self.b % mod_1;
    let congruence_2 = other.b % mod_2;
    let e = e.get();
    let wide_e = WideU::from((e, U::ZERO));
    let congruence_3 = {
      let congruence_3_rhs = {
        let congruence_3_rhs_numerator = self.discriminant + (self.b * other.b);
        let (congruence_3_rhs_mul_2, rem) = congruence_3_rhs_numerator / wide_e;
        debug_assert!(bool::from(rem.is_zero()));
        congruence_3_rhs_mul_2.half()
      } % mod_3;

      // We drop the remainder here because `e` is explicitly a divisor of `B_mu`
      let congruence_3_lhs_factor = (B_mu / e).0.widen::<WideU>();

      /*
        We have `ax congruent to b mod c`.

        We can't scale `b` by `a**-1` as `a` may not have a multiplicative inverse `mod c`. We
        instead scale `a` by `u` where for `g = 1`, `a * u congruent to 1 mod c` (so `u` would be
        the multiplicative inverse of `a` if `g = 1`). When `g != 1`, this generalizes as
        `a * u congruent to g mod c`. Scaling `a` by `u` accordingly produces `a * a**-1 * g`,
        which we convert to `a * a**-1` via integer division by `g`.
      */
      /*
        This GCD calculates the product of the list of common prime factors of
        `B_mu / e, 2 * A_1 * A_2 / e**2`. This can be paraphrased as:
        ```
        common_factors(
          F_{B_mu} - common_factors(F_{B_mu}, F_{A_1}, F_{A_2}),
          [2] +
            F_{A_1} - common_factors(F_{B_mu}, F_{A_1}, F_{A_2}) +
            F_{A_2} - common_factors(F_{B_mu}, F_{A_1}, F_{A_2})
        )
        ```
        where `F_{...} = factors(...). This is equivalent to the statement
        `product(common_factors(A, [2] + B + C)) / gcd(B_mu, A_1, A_2)`.
      */
      let (g, u, mod_3_div_g): (WideU, WideU, WideU) =
        congruence_3_lhs_factor.abs().extended_gcd_part(mod_3);
      let wide_g = WideWideU::from((g, WideU::ZERO));
      let (res, rem): (WideWideU, WideWideU) =
        congruence_3_rhs.widening_mul(&u).div_rem(&NonZero::new(wide_g).unwrap());
      debug_assert!(bool::from(rem.is_zero()));
      mod_3 = mod_3_div_g;

      // Reduce res by the modulus
      let wide_mod_3 = WideWideU::from((mod_3, WideU::ZERO));
      let res = res % wide_mod_3;
      // Since this modulus only used the low bits, this only has low bits
      let res = res.split().0;
      <_>::ct_select(&(mod_3 - res), &res, congruence_3_lhs_factor.positive())
    };

    // CRT generalized for coprime moduli
    fn crt<const LIMBS: usize, const TWICE_LIMBS: usize, const THRICE_LIMBS: usize>(
      congruence_1: Uint<LIMBS>,
      mod_1: Uint<LIMBS>,
      congruence_2: Uint<LIMBS>,
      mod_2: Uint<LIMBS>,
      mod_1_mod_2_xgcd: (Uint<LIMBS>, Uint<LIMBS>, IStruct<Uint<LIMBS>>, Uint<LIMBS>),
    ) -> (IStruct<Uint<THRICE_LIMBS>>, Uint<TWICE_LIMBS>) {
      let (g, u, v, mod_1_div_g) = mod_1_mod_2_xgcd;
      debug_assert!(bool::from((congruence_1 % g).ct_eq(&(congruence_2 % g))));

      let M = mul_arbitrary_uints::<LIMBS, LIMBS, TWICE_LIMBS>(mod_1_div_g, mod_2);
      let x1: IStruct<Uint<{ THRICE_LIMBS }>> =
        IStruct::<Uint<TWICE_LIMBS>>::from(mul_arbitrary_uints(congruence_1, mod_2)).mul_i_uint(v);
      let x2 = mul_arbitrary_uints::<TWICE_LIMBS, LIMBS, THRICE_LIMBS>(
        mul_arbitrary_uints::<LIMBS, LIMBS, TWICE_LIMBS>(congruence_2, mod_1),
        u,
      );
      let x = x1 + x2;

      let g_words = g.as_words();
      let mut wide_g = Uint::<{ THRICE_LIMBS }>::ZERO;
      wide_g.as_words_mut()[.. g_words.len()].copy_from_slice(g_words);
      let (x, rem) = x / wide_g;
      debug_assert!(bool::from(rem.is_zero()));

      (x, M)
    }

    let mod_1_mod_2_xgcd =
      ((A1_A2_xgcd.0 / e) << 1, A1_A2_xgcd.1, A1_A2_xgcd.2, self.a / A1_A2_xgcd.0);
    #[cfg(debug_assertions)]
    {
      let actual = mod_1.extended_gcd(mod_2);
      debug_assert_eq!(mod_1_mod_2_xgcd.0, actual.0);
      debug_assert_eq!(mod_1_mod_2_xgcd.3, actual.3);
      debug_assert_eq!(mod_1_mod_2_xgcd.1, actual.1);
      debug_assert_eq!(bool::from(mod_1_mod_2_xgcd.2.positive()), bool::from(actual.2.positive()));
      debug_assert_eq!(mod_1_mod_2_xgcd.2.abs(), actual.2.abs());
    }
    let (wide_congruence_12, mod_12): (_, WideU) =
      crt::<
        { crypto_bigint_xgcd::nlimbs!(BITS / 2) },
        { crypto_bigint_xgcd::nlimbs!(BITS) },
        { crypto_bigint_xgcd::nlimbs!(BITS + (BITS / 2)) },
      >(congruence_1, mod_1, congruence_2, mod_2, mod_1_mod_2_xgcd);

    let mut wide_mod_12 = Uint::<{ crypto_bigint_xgcd::nlimbs!(BITS + (BITS / 2)) }>::ZERO;
    let mod_12_words = mod_12.as_words();
    wide_mod_12.as_words_mut()[.. mod_12_words.len()].copy_from_slice(mod_12_words);
    let wide_congruence_12 = wide_congruence_12 % wide_mod_12;

    let mut congruence_12 = WideU::ZERO;
    let wide_words_len = congruence_12.as_words().len();
    congruence_12.as_words_mut().copy_from_slice(&wide_congruence_12.as_words()[.. wide_words_len]);

    let (x, _mod_123): (_, WideWideU) =
      crt::<
        { crypto_bigint_xgcd::nlimbs!(BITS) },
        { crypto_bigint_xgcd::nlimbs!(2 * BITS) },
        { crypto_bigint_xgcd::nlimbs!(3 * BITS) },
      >(congruence_12, mod_12, congruence_3, mod_3, mod_12.extended_gcd(mod_3));

    let mut wide_two_A = Uint::<{ crypto_bigint_xgcd::nlimbs!(3 * BITS) }>::ZERO;
    let two_A_words = two_A.as_words();
    wide_two_A.as_words_mut()[.. two_A_words.len()].copy_from_slice(two_A_words);
    let wide_B = x % wide_two_A;

    let mut B = WideU::ZERO;
    B.as_words_mut().copy_from_slice(&wide_B.as_words()[.. wide_words_len]);

    // Since `A = (A_1 / e) * (A_2 / e)`, where `e = gcd(A_1, A_2, B_mu)`, we assume `e = 1` and
    // the bound on `log_2(A)` becomes `log_2(A_1 * A_2)`
    let log_2_a_bound = 2 * self.discriminant.abs().bits().div_ceil(2);
    Self::reduce(log_2_a_bound, A, WideI::from(B), self.discriminant)
  }

  // A copy/paste of `Self::add` which removes the duplicated congruence for this specialization
  fn double(&self) -> CryptoBigintStackElement {
    let B_mu: I = self.b;

    let e: U = self.a.bingcd(B_mu.abs());
    let e = NonZero::new(e).unwrap();
    let A_div_e: U = self.a / e;
    let A: WideU = A_div_e.widening_mul(&A_div_e);

    let mod_1: U = A_div_e << 1;
    let two_A: WideU = A << 1;
    let mut mod_3 = two_A;

    let congruence_1 = self.b % mod_1;
    let e = e.get();
    let wide_e = WideU::from((e, U::ZERO));
    let congruence_3 = {
      let congruence_3_rhs = {
        let congruence_3_rhs_numerator = self.discriminant + (self.b * self.b);
        let (congruence_3_rhs_mul_2, rem) = congruence_3_rhs_numerator / wide_e;
        debug_assert!(bool::from(rem.is_zero()));
        congruence_3_rhs_mul_2.half()
      } % mod_3;

      // We drop the remainder here because `e` is explicitly a divisor of `B_mu`
      let congruence_3_lhs_factor = (B_mu / e).0.widen::<WideU>();

      /*
        We have `ax congruent to b mod c`.

        We can't scale `b` by `a**-1` as `a` may not have a multiplicative inverse `mod c`. We
        instead scale `a` by `u` where for `g = 1`, `a * u congruent to 1 mod c` (so `u` would be
        the multiplicative inverse of `a` if `g = 1`). When `g != 1`, this generalizes as
        `a * u congruent to g mod c`. Scaling `a` by `u` accordingly produces `a * a**-1 * g`,
        which we convert to `a * a**-1` via integer division by `g`.
      */
      let (g, u, mod_3_div_g): (WideU, WideU, WideU) =
        congruence_3_lhs_factor.abs().extended_gcd_part(mod_3);
      let wide_g = WideWideU::from((g, WideU::ZERO));
      let (res, rem): (WideWideU, WideWideU) =
        congruence_3_rhs.widening_mul(&u).div_rem(&NonZero::new(wide_g).unwrap());
      debug_assert!(bool::from(rem.is_zero()));
      mod_3 = mod_3_div_g;

      // Reduce res by the modulus
      let wide_mod_3 = WideWideU::from((mod_3, WideU::ZERO));
      let res = res % wide_mod_3;
      // Since this modulus only used the low bits, this only has low bits
      let res = res.split().0;
      <_>::ct_select(&(mod_3 - res), &res, congruence_3_lhs_factor.positive())
    };

    let x = {
      let (g, u, v) = {
        /*
          a = 2 (A1 / e)
          b = 2 (A2 / e)
          c = (a * b) / 2

          We want to calculate `gcd(lcm(a, b), c)`.

          gcd(a * b / gcd(a, b), c)
          gcd(a * b / gcd(2 AI / e, 2 A2 / e), c)
          gcd(a * b / (2 gcd(AI / e, A2 / e)), c)
          gcd(a * b / (2 gcd(AI / e, A2 / e)), a * b / 2)
          gcd(a * b / 2 / gcd(AI / e, A2 / e), a * b / 2)

          Please note how regardless of what the inner `gcd` yields, the second argument will be
          divisible by the first argument. This lets us simplify the calculation of the outer
          `gcd`.

          The one complexity is in how `c` isn't `a * b / 2` yet
          `a * b / 2 / gcd(B_mu / e, 2 A_1 * A_2 / e**2)`. `e = gcd(B_mu, A_1, A_2)` so `B_mu / e`
          has no common factors with `A_1 * A_2 / e**2`. This is due to `e = gcd(B_mu, A_1, A_2)`.
          If `A_1 != A_2`, then there may still be the common factors present in `B_mu, A_1` yet
          not `A_2` (and vice versa), but `A_1 == A_2` when doubling. The only question is if
          `B_mu / e` is divisible by `2`, bounding the `gcd` further divided by to being `1` or
          `2`.

          This means the second argument may not be divisible yet two times it will be, and still
          lets us greatly accelerate calculation.
        */
        let mod_1 = Uint::from((mod_1, Uint::ZERO));
        let divisible_by_mod_1 = (mod_3 % mod_1).is_zero();
        let mod_1_div_2 = mod_1 >> 1;
        // If not divisible by `mod_1`, then twice `mod_3` is, meaning divisble by half `mod_1`
        // Since `mod_1, mod_2` are even, `mod_1` will be and half `mod_1` is well-defined
        let g = <_>::ct_select(&mod_1, &mod_1_div_2, !divisible_by_mod_1);

        // If `mod_3` is divisible by `mod_1`, then `u = 1, v = 0`
        let if_divisble_by_mod12 = (WideU::ONE, IStruct::from(WideU::ZERO));
        // If `mod_3` is greater than `mod_1` and divisible by `mod_1 / 2`, then
        // `u = mod_3.div_ceil(mod_1), v = -1`
        let if_gt_mod12_and_not_divisble_by_mod12 =
          ((mod_3 / mod_1) + WideU::ONE, -IStruct::from(WideU::ONE));
        // If `mod_3` is less than `mod_1` and divisible by `mod_1 / 2`, then
        // `mod_3 = mod_1 / 2`, and `u = 0, v = 1.
        let if_mod_3_eq_mod12_div_2 = (WideU::ZERO, IStruct::from(WideU::ONE));
        let mod_3_eq_mod12_div_2 = mod_3.ct_eq(&mod_1_div_2);

        let u = <_>::ct_select(
          &if_gt_mod12_and_not_divisble_by_mod12.0,
          &if_divisble_by_mod12.0,
          divisible_by_mod_1,
        );
        let u = <_>::ct_select(&u, &if_mod_3_eq_mod12_div_2.0, mod_3_eq_mod12_div_2);

        let v = <_>::ct_select(
          &if_gt_mod12_and_not_divisble_by_mod12.1,
          &if_divisble_by_mod12.1,
          divisible_by_mod_1,
        );
        let v = <_>::ct_select(&v, &if_mod_3_eq_mod12_div_2.1, mod_3_eq_mod12_div_2);

        (g, u, v)
      };

      const LIMBS: usize = crypto_bigint_xgcd::nlimbs!(BITS / 2);
      const TWICE_LIMBS: usize = crypto_bigint_xgcd::nlimbs!(BITS);
      const THRICE_LIMBS: usize = crypto_bigint_xgcd::nlimbs!(3 * (BITS / 2));
      const FIVE_LIMBS: usize = crypto_bigint_xgcd::nlimbs!(5 * (BITS / 2));

      let x1: IStruct<Uint<{ FIVE_LIMBS }>> =
        IStruct::<Uint<THRICE_LIMBS>>::from(mul_arbitrary_uints(congruence_1, mod_3)).mul_i_uint(v);
      let x2 = mul_arbitrary_uints::<THRICE_LIMBS, TWICE_LIMBS, FIVE_LIMBS>(
        mul_arbitrary_uints::<TWICE_LIMBS, LIMBS, THRICE_LIMBS>(congruence_3, mod_1),
        u,
      );
      let x = x1 + x2;

      let g_words = g.as_words();
      let mut wide_g = Uint::<{ FIVE_LIMBS }>::ZERO;
      wide_g.as_words_mut()[.. g_words.len()].copy_from_slice(g_words);
      let (x, rem) = x / wide_g;
      debug_assert!(bool::from(rem.is_zero()));

      x
    };

    let mut wide_two_A = Uint::<{ crypto_bigint_xgcd::nlimbs!(5 * (BITS / 2)) }>::ZERO;
    let two_A_words = two_A.as_words();
    wide_two_A.as_words_mut()[.. two_A_words.len()].copy_from_slice(two_A_words);
    let wide_B = x % wide_two_A;

    let mut B = WideU::ZERO;
    let wide_words_len = B.as_words().len();
    B.as_words_mut().copy_from_slice(&wide_B.as_words()[.. wide_words_len]);

    // Since `A = (A_1 / e) * (A_2 / e)`, where `e = gcd(A_1, A_2, B_mu)`, we assume `e = 1` and
    // the bound on `log_2(A)` becomes `log_2(A_1 * A_2)`
    let log_2_a_bound = 2 * self.discriminant.abs().bits().div_ceil(2);
    Self::reduce(log_2_a_bound, A, WideI::from(B), self.discriminant)
  }

  fn sub(&self, other: CryptoBigintStackElement) -> CryptoBigintStackElement {
    self.add(&-other)
  }

  fn multiexp(identity: &Self, pairs: &[(&Table<Self>, &[u8])]) -> Self {
    let mut longest_scalar_bits = 0;
    for (_table, scalar) in pairs {
      longest_scalar_bits = longest_scalar_bits.max(scalar.len() * 8);
    }

    let mut res: Option<Self> = None;
    for i in 0 .. longest_scalar_bits {
      // Shift over the existing result by a bit
      if let Some(res) = res.as_mut() {
        *res = res.double();
      }

      for (table, scalar) in pairs {
        let scalar_bits = scalar.len() * 8;
        // Transform the index of the bit in our longest scalar to the index of the bit in this one
        let Some(i) = i.checked_sub(longest_scalar_bits - scalar_bits) else {
          // If we're indexing a bit which doesn't exist in this scalar, continue
          continue;
        };

        // If it's time to add this entry, do so
        let table_bits = table.bits();
        if ((i + 1) % table_bits) == 0 {
          let mut accum = 0usize;
          debug_assert_eq!(i - (i + 1 - table_bits) + 1, table_bits);
          for i in (i + 1 - table_bits) ..= i {
            accum <<= 1;
            accum |= (usize::from(scalar[i / 8] >> (7 - (i % 8)))) & 1;
          }

          let mut to_add = Self::ct_select(&table[0], &table[1], 1.ct_eq(&accum));
          for i in 2 .. table.as_ref().len() {
            to_add = Self::ct_select(&to_add, &table[i], i.ct_eq(&accum));
          }
          res = Some(res.as_ref().map(|res| res.add(&to_add)).unwrap_or_else(|| to_add.clone()));
        }
      }
    }

    // Perform the final step of the accumulator
    for (table, scalar) in pairs {
      let scalar_bits = scalar.len() * 8;

      let table_bits = table.bits();
      let mut accum = 0usize;
      for i in ((scalar_bits / table_bits) * table_bits) .. scalar_bits {
        accum <<= 1;
        accum |= (usize::from(scalar[i / 8] >> (7 - (i % 8)))) & 1;
      }

      let mut to_add = Self::ct_select(&table[0], &table[1], 1.ct_eq(&accum));
      for i in 2 .. table.as_ref().len() {
        to_add = Self::ct_select(&to_add, &table[i], i.ct_eq(&accum));
      }
      res = Some(res.as_ref().map(|res| res.add(&to_add)).unwrap_or_else(|| to_add.clone()));
    }

    res.unwrap_or_else(|| identity.clone())
  }

  fn from_be_abc_discriminant_tess_root_unchecked(
    a: &[u8],
    b_positive: subtle::Choice,
    b: &[u8],
    _c: &[u8],
    abs_value_of_neg_discriminant: &[u8],
    _tess_root: &[u8],
  ) -> Self {
    if (8 * abs_value_of_neg_discriminant.len()) > usize::try_from(BITS - 128).unwrap() {
      panic!("too large of a discriminant");
    }

    let full_bytes = |bits: usize, bytes: &[u8]| {
      let mut full_bytes = vec![0u8; bits / 8];
      full_bytes[(bits / 8) - bytes.len() ..].copy_from_slice(bytes);
      full_bytes
    };

    let b = I::from(U::from_be_slice(&full_bytes(usize::try_from(A_BITS).unwrap(), b)));
    // TODO: ct_neg
    let b = I::ct_select(&-b, &b, b_positive);

    Self {
      a: U::from_be_slice(&full_bytes(usize::try_from(A_BITS).unwrap(), a)),
      b,
      discriminant: -WideI::from(WideU::from_be_slice(&full_bytes(
        usize::try_from(BITS).unwrap(),
        abs_value_of_neg_discriminant,
      ))),
    }
  }

  fn a(&self) -> Vec<u8> {
    let bytes = self.a.to_be_bytes();
    let mut start = 0;
    while bytes.get(start) == Some(&0) {
      start += 1;
    }
    bytes[start ..].to_vec()
  }

  fn b(&self) -> (subtle::Choice, Vec<u8>) {
    let bytes = self.b.abs().to_be_bytes();
    let mut start = 0;
    while bytes.get(start) == Some(&0) {
      start += 1;
    }
    (self.b.positive(), bytes[start ..].to_vec())
  }
}

impl Neg for CryptoBigintStackElement {
  type Output = Self;
  fn neg(self) -> Self {
    Self::reduce(
      self.discriminant.abs().bits().div_ceil(2),
      (&self.a).into(),
      (-self.b).widen(),
      self.discriminant,
    )
  }
}
