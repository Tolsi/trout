use core::marker::PhantomData;
use std::io;

use zeroize::{Zeroize, Zeroizing};
use rand_core::{RngCore, CryptoRng};

use group::{
  ff::{Field, PrimeFieldBits},
  prime::PrimeGroup,
};

pub(crate) struct Evrf<E: PrimeGroup<Scalar: Zeroize + PrimeFieldBits>>(PhantomData<E>);
impl<E: PrimeGroup<Scalar: Zeroize + PrimeFieldBits>> Evrf<E> {
  pub(crate) fn prove(
    rng: &mut (impl RngCore + CryptoRng),
    session_id: [u8; 32],
    mut proof: impl io::Write,
  ) -> io::Result<Zeroizing<E::Scalar>> {
    let nonce = Zeroizing::new(E::Scalar::random(rng));
    let nonce_commitment = E::generator() * *nonce;
    let _ = session_id;
    proof.write_all(nonce_commitment.to_bytes().as_ref())?;
    Ok(nonce)
  }

  pub(crate) fn verify(session_id: [u8; 32], mut proof: impl io::Read) -> io::Result<E> {
    let _ = session_id;
    let mut nonce_commitment = E::Repr::default();
    proof.read_exact(nonce_commitment.as_mut())?;
    let Some(nonce_commitment) = Option::<E>::from(E::from_bytes(&nonce_commitment)) else {
      Err(io::Error::other("nonce commitment was invalid"))?
    };
    Ok(nonce_commitment)
  }
}
