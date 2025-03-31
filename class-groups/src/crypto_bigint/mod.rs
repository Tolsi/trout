// TODO: multiexp, MAX_TABLE_LEN

use core::ops::Neg;
use std::sync::Arc;

use subtle::{ConstantTimeEq, ConstantTimeLess, ConstantTimeGreater};
use zeroize::Zeroize;

use crypto_bigint::{ConstantTimeSelect, BoxedUint};

mod numbers;
use numbers::*;

/// A constant-time element of a class group, implemented via crypto-bigint.
///
/// This is implemented in time variable to the discriminant yet constant to `a, b`.
#[derive(Clone, Debug)]
pub struct CryptoBigintElement {
  a: UnsignedInteger,
  b: Integer,
  discriminant: Arc<Integer>,
}

impl PartialEq for CryptoBigintElement {
  fn eq(&self, other: &Self) -> bool {
    (self.a.ct_eq(&other.a) & self.b.ct_eq(&other.b) & self.discriminant.ct_eq(&other.discriminant))
      .into()
  }
}
impl Eq for CryptoBigintElement {}

impl Zeroize for CryptoBigintElement {
  fn zeroize(&mut self) {
    // Zeroize
    self.a.zeroize();
    self.b.zeroize();

    // Set to the identity
    self.a = UnsignedInteger::from(BoxedUint::one_with_precision(self.max_bits_for_a()));
    self.b =
      Integer::from(UnsignedInteger::from(BoxedUint::one_with_precision(self.max_bits_for_b())));
  }
}

impl CryptoBigintElement {
  fn max_bits_for_a(&self) -> u32 {
    /*
      Immediately prior to lemma 5.4.4 of A Course in Computational Algebraic Number Theory,
      "Hence, after at most `ceil(log_2(a / sqrt(abs(D))))` steps, we obtain at the beginning of
      step 3 a form with `a < sqrt(abs(D))`".

      Lemma 5.4.4 proceeds to state this form is either reduced as `(a, b, c)`, `(a, -b, a)`, or
      `(c, r, s)` where `c < a`. This means that the reduction algorithm always terminates with
      the result's `a` being less than `sqrt(abs(D))`.
    */
    self.discriminant.abs().bits().div_ceil(2)
  }

  fn max_bits_for_b(&self) -> u32 {
    // For reduced elements, `|b| <= a`
    self.max_bits_for_a()
  }

  // Algorithm 5.4.2 of A Course in Computational Algebraic Number Theory
  fn reduce(
    log_2_a_bound: u32,
    mut a: UnsignedInteger,
    mut b: Integer,
    discriminant: Arc<Integer>,
  ) -> Self {
    let start_a_bits = a.precision();

    let mut c = {
      // b**2 - 4ac = discriminant
      // b**2 = discriminant + 4ac
      // b**2 - discriminant = 4ac
      let (c, rem) = &(&(&b * &b) - &*discriminant) / &Integer::from(&a << 2);
      debug_assert!(bool::from(rem.is_zero()));
      // `b**2` is positive, and `4ac` must be since subtracting it equals a negative number
      // Since `a` is positive, `c` also must be positive
      debug_assert!(bool::from(c.positive()));
      c.into_abs()
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
      let neg_b = -b.clone();
      b = Integer::ct_select(&b, &neg_b, prepare_for_next_step);
      let a_copy = a.clone();
      a = UnsignedInteger::ct_select(&a, &c, prepare_for_next_step);
      c = UnsignedInteger::ct_select(&c, &a_copy, prepare_for_next_step);

      // Termination clause
      let should_neg_b = a.ct_eq(&c) & (!b.positive());
      b = Integer::ct_select(&b, &neg_b, jump_to_step_three & (!to_continue) & should_neg_b);

      jump_to_step_three & (!to_continue)
    };

    for _ in 0 .. iterations {
      let two_a = &a << 1;
      // b / 2a
      let (mut q, r) = &b / &two_a;
      let r_gt_a = r.ct_gt(&a);
      q = Integer::ct_select(
        &q,
        &(&q + &Integer::from(UnsignedInteger::from(BoxedUint::one()))),
        r_gt_a,
      );
      let mut r = Integer::from(r);
      r = Integer::ct_select(&r, &(&r - &Integer::from(two_a)), r_gt_a);

      // Write the reduced `(c, b)` if we aren't already done
      let b_r = (&b + &r).half();
      let next_c = &Integer::from(c.clone()) - &(&b_r * &q);
      debug_assert!(bool::from(next_c.positive()));
      c = UnsignedInteger::ct_select(&c, next_c.abs(), !done);
      b = Integer::ct_select(&b, &r, !done);

      // Step 3

      // Continuation clause
      let to_continue = a.ct_gt(&c);
      let prepare_for_next_step = !done & to_continue;
      let neg_b = -b.clone();
      b = Integer::ct_select(&b, &neg_b, prepare_for_next_step);
      let a_copy = a.clone();
      a = UnsignedInteger::ct_select(&a, &c, prepare_for_next_step);
      c = UnsignedInteger::ct_select(&c, &a_copy, prepare_for_next_step);

      // Termination clause
      done = !prepare_for_next_step;
      let should_neg_b = a.ct_eq(&c) & (!b.positive());
      b = Integer::ct_select(&b, &neg_b, done & should_neg_b);

      // `a` is set to `c` when `a > c`, and accordingly always reduces in size
      a.shorten(start_a_bits);
      // `b` is set to `r` which is in the range `-a < r <= a`, or its own negative
      // If `b` entered this function unreduced, then `|b| <= a` and this is valid
      b.abs_mut().shorten(start_a_bits);
      /*
        `c` was set to `c - 1/2(b+r)q` in step 2. In step 3, `c` is swapped with the former `a`
        (which always decreases in size) or the algorithm terminates. If the algorithm terminated,
        `abs(b) <= a <= c` and `a < sqrt(abs(discriminant))`. This means `b` is at most
        `sqrt(abs(discriminant))` and `b**2` is at most of bit-length equal to the discriminant.
        If so, we have `k - log2(4ac) = k`. If we assume `a = 1`, which is impossible for our
        definition of `b` yet also lets us establish clear bounds, then we get a bound of
        `log2(c) = k - 2`.

        We shorten `c` to the initial length of `a` (the longest it'll ever be) or the length of
        the discriminant, whichever is higher.
      */
      c.shorten(start_a_bits.max(discriminant.abs().precision()));
    }

    let mut res = Self { a, b, discriminant };
    res.a.shorten(res.max_bits_for_a());
    let max_bits_for_b = res.max_bits_for_b();
    res.b.abs_mut().shorten(max_bits_for_b);
    res
  }
}

impl crate::Element for CryptoBigintElement {
  fn is_identity(&self) -> subtle::Choice {
    self.a.is_one() & self.b.positive() & self.b.abs().is_one()
  }

  fn double(&self) -> Self {
    self.add(self)
  }

  // Allegedly, Arndt's method, as specified on the Wikipedia page for binary quadratic forms
  fn add(&self, other: &Self) -> CryptoBigintElement {
    let B_mu = (&self.b + &other.b).half();

    let e = self.a.gcd(&other.a).gcd(B_mu.abs());
    let (A1_div_e, _) = &self.a / &e;
    let (A2_div_e, _) = &other.a / &e;
    let A = &A1_div_e * &A2_div_e;

    let mod_1 = &A1_div_e << 1;
    let mod_2 = &A2_div_e << 1;
    let two_A = &A << 1;
    let mut mod_3 = two_A.clone();

    let congruence_1 = &self.b % &mod_1;
    let congruence_2 = &other.b % &mod_2;
    let congruence_3 = {
      let congruence_3_rhs = &{
        let congruence_3_rhs_numerator = &*self.discriminant + &(&self.b * &other.b);
        let (congruence_3_rhs_mul_2, rem) = &congruence_3_rhs_numerator / &e;
        debug_assert!(bool::from(rem.is_zero()));
        congruence_3_rhs_mul_2.half()
      } % &mod_3;

      // We drop the remainder here because `e` is explicitly a divisor of `B_mu`
      let congruence_3_lhs_factor = &(&B_mu / &e).0 % &mod_3;

      /*
        We have `ax congruent to b mod c`.

        We can't scale `b` by `a**-1` as `a` may not have a multiplicative inverse `mod c`. We
        instead scale `a` by `u` where for `g = 1`, `a * u congruent to 1 mod c` (so `u` would be
        the multiplicative inverse of `a` if `g = 1`). When `g != 1`, this generalizes as
        `a * u congruent to g mod c`. Scaling `a` by `u` accordingly produces `a * a**-1 * g`,
        which we convert to `a * a**-1` via integer division by `g`.
      */
      let (g, u, _v) = congruence_3_lhs_factor.extended_gcd(&mod_3);
      let (res, rem) = &(&congruence_3_rhs * &u) / &g;
      debug_assert!(bool::from(rem.is_zero()));
      mod_3 = (&mod_3 / &g).0;
      &res % &mod_3
    };

    // CRT generalized for coprime moduli
    let crt = |congruence_1: &UnsignedInteger,
               mod_1: &UnsignedInteger,
               congruence_2: &UnsignedInteger,
               mod_2: &UnsignedInteger|
     -> (UnsignedInteger, UnsignedInteger) {
      let (g, u, v) = mod_1.extended_gcd(mod_2);
      debug_assert!(bool::from((congruence_1 % &g).ct_eq(&(congruence_2 % &g))));
      let M = &(mod_1 / &g).0 * mod_2;
      let x =
        &(&Integer::from(congruence_1 * mod_2) * &v) + &(&Integer::from(congruence_2 * mod_1) * &u);
      let (x, rem) = &x / &g;
      debug_assert!(bool::from(rem.0.is_zero()));
      debug_assert!(bool::from((&x % mod_1).ct_eq(congruence_1)));
      debug_assert!(bool::from((&x % mod_2).ct_eq(congruence_2)));
      (&x % &M, M)
    };

    let (congruence_12, mod_12) = crt(&congruence_1, &mod_1, &congruence_2, &mod_2);
    let (x, _mod_123) = crt(&congruence_12, &mod_12, &congruence_3, &mod_3);

    let B = x;

    debug_assert!(bool::from(congruence_1.ct_eq(&(&B % &mod_1))));
    debug_assert!(bool::from(congruence_2.ct_eq(&(&B % &mod_2))));
    debug_assert!(bool::from(congruence_3.ct_eq(&(&B % &mod_3))));

    let max_bits_for_a = self.max_bits_for_a();
    let log_2_a_1_bound = max_bits_for_a;
    let log_2_a_2_bound = max_bits_for_a;
    // Since `A = (A_1 / e) * (A_2 / e)`, where `e = gcd(A_1, A_2, B_mu)`, we assume `e = 1` and
    // the bound on `log_2(A)` becomes `log_2(A_1 * A_2)`
    let log_2_a_bound = log_2_a_1_bound + log_2_a_2_bound;
    Self::reduce(log_2_a_bound, A, Integer::from(B), self.discriminant.clone())
  }

  fn sub(&self, other: CryptoBigintElement) -> CryptoBigintElement {
    self.add(&-other)
  }

  fn from_be_abc_discriminant_tess_root_unchecked(
    a: &[u8],
    b_positive: subtle::Choice,
    b: &[u8],
    _c: &[u8],
    abs_value_of_neg_discriminant: &[u8],
    _tess_root: &[u8],
  ) -> Self {
    let b = Integer::from(UnsignedInteger::from_be_slice(b));
    // TODO: ct_neg
    let b = Integer::ct_select(&-b.clone(), &b, b_positive);

    let mut res = Self {
      a: UnsignedInteger::from_be_slice(a),
      b,
      discriminant: Arc::new(-Integer::from(UnsignedInteger::from_be_slice(
        abs_value_of_neg_discriminant,
      ))),
    };
    res.a.widen(res.max_bits_for_a());
    let max_bits_for_b = res.max_bits_for_b();
    res.b.abs_mut().widen(max_bits_for_b);
    res
  }

  fn a(&self) -> Vec<u8> {
    let mut bytes = self.a.to_be_bytes();
    while bytes.first() == Some(&0) {
      bytes.remove(0);
    }
    bytes
  }

  fn b(&self) -> (subtle::Choice, Vec<u8>) {
    let mut bytes = self.b.abs().to_be_bytes();
    while bytes.first() == Some(&0) {
      bytes.remove(0);
    }
    (self.b.positive(), bytes)
  }
}

impl Neg for CryptoBigintElement {
  type Output = Self;
  fn neg(self) -> Self {
    Self::reduce(self.max_bits_for_a(), self.a, self.b.neg(), self.discriminant)
  }
}
