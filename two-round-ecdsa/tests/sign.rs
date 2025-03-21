use rand_core::OsRng;
use class_groups::MalachiteElement;
use dkg::Participant;
use two_round_ecdsa::{SecurityLevel, Setup, SigningProtocol, Ready};

#[test]
fn sign() {
  let mut setups = Setup::<two_round_ecdsa::Secp256k1, MalachiteElement>::dealer(
    &mut OsRng,
    SecurityLevel::Insecure,
    2,
    3,
  )
  .unwrap();
  println!("Setup!");

  let first_i = Participant::new(1).unwrap();
  let first = setups.remove(&first_i).unwrap();
  let second_i = Participant::new(3).unwrap();
  let second = setups.remove(&second_i).unwrap();

  let (first, first_message) =
    SigningProtocol::<two_round_ecdsa::Secp256k1, _>::participate(&mut OsRng, first, [0; 32]);
  let (second, second_message) =
    SigningProtocol::<two_round_ecdsa::Secp256k1, _>::participate(&mut OsRng, second, [0; 32]);
  println!("Participated!");

  let Ready::Ready(first) = first.accumulate(second_i, second_message) else { panic!() };
  let Ready::Ready(second) = second.accumulate(first_i, first_message) else { panic!() };
  println!("Accumulated!");

  const MESSAGE: &[u8] = b"Hello, World!";
  let (first, first_message) = first.sign(MESSAGE);
  let (second, second_message) = second.sign(MESSAGE);
  println!("Signed!");

  let Ready::Ready(first_signature) = first.aggregate(second_i, second_message) else { panic!() };
  let Ready::Ready(second_signature) = second.aggregate(first_i, first_message) else { panic!() };
  assert_eq!(first_signature, second_signature);
  println!("Aggregated!");

  {
    use ecdsa::signature::Verifier;
    ecdsa::VerifyingKey::<k256::Secp256k1>::from_affine(
      setups.values().next().unwrap().view().verification_key().to_affine(),
    )
    .unwrap()
    .verify(
      MESSAGE,
      &ecdsa::Signature::from_scalars(first_signature.r(), {
        // Use a normalized `s` since the ECDSA crate rejects non-normalized signature
        let s = first_signature.s();
        if bool::from(k256::elliptic_curve::scalar::IsHigh::is_high(&s)) { -s } else { s }
      })
      .unwrap(),
    )
    .unwrap();
  }
}
