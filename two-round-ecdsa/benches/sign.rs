use criterion::{BatchSize, Criterion, criterion_group, criterion_main};
use dkg::Participant;
use rand_core::OsRng;
use two_round_ecdsa::{Ready, SecurityLevel, Setup, SigningProtocol};

type ProverElement = class_groups::CryptoBigintStackElement;
#[cfg(not(feature = "gmp"))]
type Element = class_groups::MalachiteElement;
#[cfg(not(feature = "gmp"))]
type Primes = two_round_ecdsa::proofs::CryptoPrimesStackCcykc;
#[cfg(feature = "gmp")]
type Element = class_groups::GmpElement;
#[cfg(feature = "gmp")]
type Primes = two_round_ecdsa::proofs::GmpPrimes;
type Params = two_round_ecdsa::Secp256k1<Primes>;

const MESSAGE: &[u8] = b"Hello, World!";
const T: u16 = 2;
const N: u16 = 3;
const SESSION_ID: [u8; 32] = [0u8; 32];

fn make_setups() -> std::collections::HashMap<Participant, std::sync::Arc<Setup<ProverElement, Element, Params>>> {
  Setup::<ProverElement, Element, Params>::dealer(
    &mut OsRng,
    SecurityLevel::Insecure,
    T,
    N,
  )
  .unwrap()
}

fn bench_dealer(c: &mut Criterion) {
  c.bench_function("dealer setup (2-of-3, Insecure)", |b| {
    b.iter(make_setups);
  });
}

fn bench_round1_participate(c: &mut Criterion) {
  c.bench_function("round1: participate", |b| {
    b.iter_batched(
      || make_setups().remove(&Participant::new(1).unwrap()).unwrap(),
      |setup| SigningProtocol::<_, _, Params>::participate(&mut OsRng, setup, SESSION_ID),
      BatchSize::SmallInput,
    );
  });
}

fn bench_round1_accumulate(c: &mut Criterion) {
  c.bench_function("round1: accumulate (t=2)", |b| {
    b.iter_batched(
      || {
        let mut setups = make_setups();
        let first = setups.remove(&Participant::new(1).unwrap()).unwrap();
        let second = setups.remove(&Participant::new(3).unwrap()).unwrap();
        let second_i = Participant::new(3).unwrap();
        let (first_state, _) =
          SigningProtocol::<_, _, Params>::participate(&mut OsRng, first, SESSION_ID);
        let (_, second_message) =
          SigningProtocol::<_, _, Params>::participate(&mut OsRng, second, SESSION_ID);
        (first_state, second_i, second_message)
      },
      |(first_state, second_i, second_message)| {
        first_state.accumulate(&mut OsRng, second_i, second_message)
      },
      BatchSize::SmallInput,
    );
  });
}

fn bench_round2_sign(c: &mut Criterion) {
  c.bench_function("round2: sign", |b| {
    b.iter_batched(
      || {
        let mut setups = make_setups();
        let first_i = Participant::new(1).unwrap();
        let first = setups.remove(&first_i).unwrap();
        let second_i = Participant::new(3).unwrap();
        let second = setups.remove(&second_i).unwrap();
        let (first_state, first_msg) =
          SigningProtocol::<_, _, Params>::participate(&mut OsRng, first, SESSION_ID);
        let (second_state, second_msg) =
          SigningProtocol::<_, _, Params>::participate(&mut OsRng, second, SESSION_ID);
        let Ready::Ready(first_signing) =
          first_state.accumulate(&mut OsRng, second_i, second_msg)
        else {
          panic!()
        };
        let Ready::Ready(_) = second_state.accumulate(&mut OsRng, first_i, first_msg) else {
          panic!()
        };
        first_signing
      },
      |signing| signing.sign(&mut OsRng, MESSAGE),
      BatchSize::SmallInput,
    );
  });
}

fn bench_round2_aggregate(c: &mut Criterion) {
  c.bench_function("round2: aggregate", |b| {
    b.iter_batched(
      || {
        let mut setups = make_setups();
        let first_i = Participant::new(1).unwrap();
        let first = setups.remove(&first_i).unwrap();
        let second_i = Participant::new(3).unwrap();
        let second = setups.remove(&second_i).unwrap();
        let (first_state, first_msg) =
          SigningProtocol::<_, _, Params>::participate(&mut OsRng, first, SESSION_ID);
        let (second_state, second_msg) =
          SigningProtocol::<_, _, Params>::participate(&mut OsRng, second, SESSION_ID);
        let Ready::Ready(first_signing) =
          first_state.accumulate(&mut OsRng, second_i, second_msg)
        else {
          panic!()
        };
        let Ready::Ready(second_signing) =
          second_state.accumulate(&mut OsRng, first_i, first_msg)
        else {
          panic!()
        };
        let (first_agg, _) = first_signing.sign(&mut OsRng, MESSAGE);
        let (_, second_r2_msg) = second_signing.sign(&mut OsRng, MESSAGE);
        (first_agg, second_i, second_r2_msg)
      },
      |(first_agg, second_i, second_msg)| {
        first_agg.aggregate(&mut OsRng, second_i, second_msg)
      },
      BatchSize::SmallInput,
    );
  });
}

fn bench_full_sign(c: &mut Criterion) {
  c.bench_function("full mpc sign (all rounds)", |b| {
    b.iter_batched(
      make_setups,
      |mut setups| {
        let first_i = Participant::new(1).unwrap();
        let first = setups.remove(&first_i).unwrap();
        let second_i = Participant::new(3).unwrap();
        let second = setups.remove(&second_i).unwrap();

        let (first_state, first_msg) =
          SigningProtocol::<_, _, Params>::participate(&mut OsRng, first, SESSION_ID);
        let (second_state, second_msg) =
          SigningProtocol::<_, _, Params>::participate(&mut OsRng, second, SESSION_ID);

        let Ready::Ready(first_signing) =
          first_state.accumulate(&mut OsRng, second_i, second_msg)
        else {
          panic!()
        };
        let Ready::Ready(second_signing) =
          second_state.accumulate(&mut OsRng, first_i, first_msg)
        else {
          panic!()
        };

        let (first_agg, first_r2_msg) = first_signing.sign(&mut OsRng, MESSAGE);
        let (second_agg, second_r2_msg) = second_signing.sign(&mut OsRng, MESSAGE);

        let Ready::Ready(first_sig) = first_agg.aggregate(&mut OsRng, second_i, second_r2_msg)
        else {
          panic!()
        };
        let Ready::Ready(second_sig) = second_agg.aggregate(&mut OsRng, first_i, first_r2_msg)
        else {
          panic!()
        };
        (first_sig, second_sig)
      },
      BatchSize::SmallInput,
    );
  });
}

criterion_group! {
  name = benches;
  config = Criterion::default()
    .sample_size(10)
    .warm_up_time(std::time::Duration::from_secs(3))
    .measurement_time(std::time::Duration::from_secs(100));
  targets =
    bench_dealer,
    bench_round1_participate,
    bench_round1_accumulate,
    bench_round2_sign,
    bench_round2_aggregate,
    bench_full_sign
}
criterion_main!(benches);
