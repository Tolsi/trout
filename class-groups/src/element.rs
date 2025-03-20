use core::{
  ops::{Index, Neg},
  cmp::Ordering,
};
use std::io;

use ::malachite::{
  base::num::{arithmetic::traits::*, basic::traits::*},
  *,
};

use crate::{malachite::natural_from_bytes, compression};

/// An element of a class group.
///
/// This is a member of a specific class group. The operations on it are not expected to enforce
/// it's only used with members of the same class group. Mixing class groups causes undefined
/// behavior.
///
/// Implementations are allowed to define if they execute in variable or constant time, even for
/// methods working with types expected to be used in a constant-time context.
pub trait Element:
  Sized + Send + Sync + Clone + Neg<Output = Self> + PartialEq + Eq + core::fmt::Debug
{
  /// Returns if the element is identity.
  fn is_identity(&self) -> subtle::Choice;

  /// Double the element.
  fn double(&self) -> Self;
  /// Add two elements.
  fn add(&self, other: &Self) -> Self;
  /// Subtract one element from another.
  fn sub(&self, other: Self) -> Self;

  /// Perform a multiplication with a `Table`.
  ///
  /// The scalar is expected to be represented by its big-endian bytes.
  ///
  /// The implementation provided by this trait runs in variable time.
  fn mul(table: &Table<Self>, scalar: &[u8]) -> Self {
    let scalar_bits = scalar.len() * 8;
    let mut accum = 0usize;
    let mut res: Option<Self> = None;
    for i in 0 .. scalar_bits {
      accum <<= 1;
      // Shift this bit into the accumulator
      // TODO: If this bit is zero and the accum is zero, immediately double. Don't init the accum
      accum |= (usize::from(scalar[i / 8] >> (7 - (i % 8)))) & 1;
      // i + 1 is the bits accumulated, and if it's the table size, perform this addition
      if ((i + 1) % table.bits()) == 0 {
        // Shift over the existing result by the proper amount of bits
        if let Some(res) = res.as_mut() {
          for _ in 0 .. table.bits() {
            *res = res.double();
          }
        }

        if accum != 0 {
          let to_add = &table[accum];
          res = Some(res.as_ref().map(|res| res.add(to_add)).unwrap_or_else(|| to_add.clone()));
          accum = 0;
        }
      }
    }

    // Perform the final step of the accumulator

    // Shift over by the remaining bits
    if let Some(res) = res.as_mut() {
      for _ in 0 .. (scalar_bits % table.bits()) {
        *res = res.double();
      }
    }

    let to_add = &table[accum];
    res.as_ref().map(|res| res.add(to_add)).unwrap_or_else(|| to_add.clone())
  }

  /// Parse an element from the big-endian encoding of its coordinates and the floored tesseract
  /// (fourth) root of the absolute value of the discriminant divided by four.
  ///
  /// This does not check for consistency between the discriminant of the coordinates and the
  /// provided root, nor that the coordinates were reduced. It MUST only be called with validated
  /// arguments.
  fn from_be_abc_tess_root_unchecked(
    a: &[u8],
    b_positive: subtle::Choice,
    b: &[u8],
    c: &[u8],
    tess_root: &[u8],
  ) -> Self;

  /// Fetch the `a`-coordinate of an element, big-endian encoded.
  fn a(&self) -> Vec<u8>;

  /// Fetch the `b`-coordinate of an element, big-endian encoded.
  ///
  /// The `Choice` represents the sign and is to be `0` if `b` is negative and `1` otherwise.
  fn b(&self) -> (subtle::Choice, Vec<u8>);

  /// Compress an element.
  ///
  /// The compressed representation is of variable-length, but internally length-prefixed such that
  /// no additional length-prefixing is necessary to read a sequence from a tape. Due to being of
  /// variable-length, all implementations will fundamentally execute in time variable to the
  /// arguments (as the provided implementation does).
  ///
  /// The exact encoding is as follows:
  /// - epsilon (1 bit)
  /// - t' is negative (1 bit)
  /// - The amount of bytes in the big-endian encoding of a', as a LE-chunked VarInt starting
  ///   immediately after the sign bits (6 bits + n bytes)
  /// - The big-endian encoding of a' (n bytes)
  /// - The amount of bytes in the big-endian encoding of g, as a LE-chunked VarInt (n bytes)
  /// - The big-endian encoding of g (n bytes)
  /// - The amount of bytes in the big-endian encoding of t', as a LE-chunked VarInt (n bytes)
  /// - The big-endian encoding of t' (n bytes)
  /// - The amount of bytes in the big-endian encoding of b_0, as a LE-chunked VarInt (n bytes)
  /// - The big-endian encoding of b_0 (n bytes)
  fn compress(&self, mut writer: impl io::Write) -> io::Result<()> {
    let a = natural_from_bytes(&self.a());
    let (epsilon, b) = {
      let (b_sign, b_value) = self.b();
      let b = natural_from_bytes(&b_value);
      // We store `< 0` as `0`, and compression stores `< 0` as `1`
      ((!b_sign).unwrap_u8(), b)
    };

    let (a_, g, t_, b_0) = if a == b {
      // Since `a >= 0`, `b >= 0`, and `epsilon == 0` as expected
      (Natural::ONE, a, Integer::ZERO, Natural::ZERO)
    } else if b == 0 {
      // Since `b >= 0`, `epsilon == 0` as expected
      (Natural::from(a), Natural::ZERO, Integer::ZERO, Natural::ZERO)
    } else {
      let (s, t) = compression::partial_xgcd(a.clone(), b.clone());
      // Calculate the positive GCD of a, t
      let (g, _x, _y) = a.clone().extended_gcd(t.unsigned_abs_ref());
      // a and g are positive so this is unsigned
      let a_ = &a / &g;
      // t may be negative so this is an integer
      let t_ = t / Integer::from(g.clone());
      // `g`, `a`, `a_` are positive so `f` is unsigned
      let f = compression::f(&a_, g.clone());
      assert_eq!(&s % &g, Natural::ZERO);
      // `b` is in its absolute value form and `f` is positive, so `b_0` is unsigned
      let b_0 = b % &f;
      // (unsigned, unsigned, signed, unsigned)
      (a_, g, t_, b_0)
    };

    /*
      We now need to convert `(a_, g, t_, b_0, epsilon)` to bytes, where `t_` is an integer. We
      define the first two bits as the sign of `t_` and `epsilon`, before encoding, with
      VarInt-length prefixes, `a_, g, t_, b_0` (the first varint having the quirk of starting two
      bits into its byte).
    */
    let sign_bits = ((epsilon << 1) + u8::from(t_.sign() == Ordering::Less)) << 6;
    let t_ = t_.unsigned_abs();

    compression::write_number(&mut writer, sign_bits, 6, &a_)?;
    let mut write_number = |number| compression::write_number(&mut writer, 0, 8, number);
    write_number(&g)?;
    write_number(&t_)?;
    write_number(&b_0)
  }
}

/// A table to perform multiplications with.
#[derive(Clone)]
pub struct Table<E: Element>(usize, Vec<E>);
impl<E: Element> Table<E> {
  /// Create a new table.
  pub fn new(bits: u32, identity: E, element: E) -> Self {
    let bits = bits.max(1).min(16);
    let len = 2usize.pow(bits);
    let mut res = Vec::with_capacity(len);
    res.push(identity);
    res.push(element);

    for i in 2 .. len {
      // Check if we can calculate this with solely a doubling
      if (i % 2) == 0 {
        res.push(res[i / 2].double());
      } else {
        let next = res[i - 1].add(&res[1]);
        res.push(next);
      }
    }
    Self(usize::try_from(bits).unwrap(), res)
  }

  /// Create a new table of size optimal for a scalar-length.
  ///
  /// This is usable in ad-hoc multiplications where creating the table, and performing the
  /// multiplication with it, should not cost more than performing the multiplication out-right.
  pub fn new_for_scalar_bits(scalar_bits: usize, identity: E, element: E) -> Self {
    let mut bits = 0u32;
    let mut adds = usize::MAX;
    while {
      let new_bits = bits + 1;
      let new_adds = 2usize.pow(new_bits) + (scalar_bits.min(8192) / (new_bits as usize));
      if new_adds <= adds {
        bits = new_bits;
        adds = new_adds;
        true
      } else {
        false
      }
    } {}
    Self::new(bits, identity, element)
  }

  /// The bits preprocessed by this table.
  pub fn bits(&self) -> usize {
    self.0
  }
}

impl<E: Element> AsRef<[E]> for Table<E> {
  fn as_ref(&self) -> &[E] {
    self.1.as_slice()
  }
}

impl<E: Element> Index<usize> for Table<E> {
  type Output = E;
  fn index(&self, i: usize) -> &E {
    &self.1[i]
  }
}
