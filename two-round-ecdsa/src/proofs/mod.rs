use core::marker::PhantomData;
use std::io;

mod evrf;
pub use evrf::*;

mod round_one;
pub use round_one::*;

mod round_two;
pub use round_two::*;

use crate::UnsignedInteger;

/*
  Reader/Writer which transcripts what they read/write. The Reader avoids the read, decompress,
  compress, hash flow solely read, hash, decompress. Since compressions can be expensive, this
  is greatly appreciated, while the pattern also ensures our transcript is complete.
*/

/// A reader which transcripts as it reads.
pub struct DigestReader<R: io::Read>(pub(crate) blake3::Hasher, pub(crate) R);
impl<R: io::Read> io::Read for DigestReader<R> {
  fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
    let read_bytes = self.1.read(buf)?;
    if read_bytes > buf.len() {
      Err(io::Error::other("more bytes read than size of buffer"))?;
    }
    self.0.update(&buf[.. read_bytes]);
    Ok(read_bytes)
  }
}

/// A writer which transcripts as it writes.
pub struct DigestWriter<W: io::Write>(pub(crate) blake3::Hasher, pub(crate) W);
impl<W: io::Write> io::Write for DigestWriter<W> {
  fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
    self.0.update(buf);
    self.1.write(buf)
  }
  fn flush(&mut self) -> io::Result<()> {
    self.1.flush()
  }
}

/// A source of prime numbers.
pub trait Primes {
  /// Derive a prime number from the XOF.
  ///
  /// The prime number MUST be sampled from the primes `2 < prime < 2**lambda`. Different
  /// satisfiers of this trait MAY yield distinct results, making the choice for `Primes` part of
  /// the protocol.
  ///
  /// This function is assumed to execute in variable time. This function has undefined behavior
  /// when `lambda <= 1`.
  fn prime(lambda: u32, xof: blake3::OutputReader) -> UnsignedInteger;
}

mod crypto_primes {
  use super::*;

  // Wrap the XOF into an RNG to satisfy crypto_primes's requirement for an RNG
  struct Blake3Rng(blake3::OutputReader);
  impl rand_core::RngCore for Blake3Rng {
    fn next_u32(&mut self) -> u32 {
      let mut bytes = [0; 4];
      self.0.fill(&mut bytes);
      u32::from_le_bytes(bytes)
    }
    fn next_u64(&mut self) -> u64 {
      let mut bytes = [0; 8];
      self.0.fill(&mut bytes);
      u64::from_le_bytes(bytes)
    }
    fn fill_bytes(&mut self, dst: &mut [u8]) {
      self.0.fill(dst)
    }
    fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), rand_core::Error> {
      self.0.fill(dst);
      Ok(())
    }
  }
  impl rand_core::CryptoRng for Blake3Rng {}

  /// A source of primes premised on crypto-primes.
  ///
  /// Panics at runtime if asked for a prime larger than its generic.
  ///
  /// This is here for evaluation purposes. It is not posited to be uniform and accordingly isn't
  /// posited to be secure. Results may differ across patch versions of crypto-primes.
  // https://github.com/entropyxyz/crypto-primes/issues/23
  // https://github.com/entropyxyz/crypto-primes/issues/25
  pub struct CryptoPrimesStack<
    U: crypto_bigint::Integer
      + crypto_bigint::RandomBits
      + crypto_bigint::RandomMod
      + crypto_bigint::Encoding,
  >(PhantomData<U>);
  impl<
    U: crypto_bigint::Integer
      + crypto_bigint::RandomBits
      + crypto_bigint::RandomMod
      + crypto_bigint::Encoding,
  > Primes for CryptoPrimesStack<U>
  {
    fn prime(lambda: u32, xof: blake3::OutputReader) -> UnsignedInteger {
      let mut rng = Blake3Rng(xof);
      loop {
        let candidate = ::crypto_primes::generate_prime_with_rng::<U>(&mut rng, lambda);
        if bool::from(crypto_bigint::Integer::is_even(&candidate)) {
          continue;
        }
        break UnsignedInteger::from_be_slice(candidate.to_be_bytes().as_ref());
      }
    }
  }

  /// CryptoPrimesStack, guaranteed to not panic when used with this library's Ccyck* proofs.
  pub type CryptoPrimesStackCcyck = CryptoPrimesStack<crypto_bigint::U128>;

  /// A source of primes premised on crypto-primes.
  ///
  /// This is here for evaluation purposes. It is not posited to be uniform and accordingly isn't
  /// posited to be secure. Results may differ across patch versions of crypto-primes.
  // https://github.com/entropyxyz/crypto-primes/issues/23
  // https://github.com/entropyxyz/crypto-primes/issues/25
  pub struct CryptoPrimesHeap;
  impl Primes for CryptoPrimesHeap {
    fn prime(lambda: u32, xof: blake3::OutputReader) -> UnsignedInteger {
      let mut rng = Blake3Rng(xof);
      loop {
        let candidate =
          ::crypto_primes::generate_prime_with_rng::<crypto_bigint::BoxedUint>(&mut rng, lambda);
        if bool::from(crypto_bigint::Integer::is_even(&candidate)) {
          continue;
        }
        break UnsignedInteger::from_be_slice(candidate.to_be_bytes().as_ref());
      }
    }
  }
}
pub use crypto_primes::*;

#[cfg(feature = "gmp")]
mod gmp_primes {
  use super::*;

  /// A source of primes premised on gmp.
  ///
  /// This is here for evaluation purposes. It is not posited to be uniform and accordingly isn't
  /// posited to be secure.
  // This isn't uniform as we sample a start position uniform from [0, 2**k] and then call for the
  // next prime. The distribution of primes isn't uniform over [0, 2**k]. It is presumably
  // consistent across versions of gmp however as it doesn't use gmp's prime sieving function yet
  // `next_prime`.
  pub struct GmpPrimes;
  impl Primes for GmpPrimes {
    fn prime(lambda: u32, mut xof: blake3::OutputReader) -> UnsignedInteger {
      loop {
        let mut bytes = vec![0; lambda.div_ceil(8).try_into().unwrap()];
        xof.fill(&mut bytes);
        let bits_in_top_byte = lambda % 8;
        // Panics if asked for a 0-bit prime, which doesn't exist
        bytes[0] &= (1 << bits_in_top_byte) - 1;

        let mut start = rug::Integer::new();
        unsafe {
          start.assign_bytes_radix_unchecked(&bytes, 256, false);
        }
        let candidate = start.next_prime();

        if candidate.significant_bits() > lambda {
          continue;
        }
        if candidate.is_even() {
          continue;
        }
        break UnsignedInteger::from_be_slice(
          &candidate.to_digits::<u8>(rug::integer::Order::MsfBe),
        );
      }
    }
  }
}
#[cfg(feature = "gmp")]
pub use gmp_primes::*;
