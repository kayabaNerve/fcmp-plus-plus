use zeroize::Zeroizing;
use rand_core::OsRng;

use transcript::{Transcript, RecommendedTranscript};

use ciphersuite::{
  group::{ff::Field, Group},
  Ciphersuite,
};

use frost::{
  curve::Ed25519,
  tests::{key_gen, algorithm_machines, sign},
};

use crate::GeneralizedSchnorr;

#[test]
fn mpc_test() {
  const OUTPUTS: usize = 3;
  const SCALARS: usize = 2;
  const SCALARS_PLUS_TWO: usize = SCALARS + 2;

  let matrix = [
    [
      <Ed25519 as Ciphersuite>::G::random(&mut OsRng),
      <Ed25519 as Ciphersuite>::G::random(&mut OsRng),
    ],
    [
      <Ed25519 as Ciphersuite>::G::random(&mut OsRng),
      <Ed25519 as Ciphersuite>::G::random(&mut OsRng),
    ],
    [
      <Ed25519 as Ciphersuite>::G::random(&mut OsRng),
      <Ed25519 as Ciphersuite>::G::random(&mut OsRng),
    ],
  ];

  let keys = key_gen::<_, Ed25519>(&mut OsRng);
  let other_scalar = Zeroizing::new(<Ed25519 as Ciphersuite>::F::random(&mut OsRng));

  let algorithm =
    GeneralizedSchnorr::<Ed25519, OUTPUTS, SCALARS, SCALARS_PLUS_TWO>::multiparty_prove(
      RecommendedTranscript::new(b"Generalized Schnorr MPC Test"),
      RecommendedTranscript::new(b"Generalized Schnorr MPC Proof Test"),
      matrix,
      [None, Some(other_scalar)],
    )
    .unwrap();

  let (outputs, _, proof) = sign(
    &mut OsRng,
    &algorithm,
    keys.clone(),
    algorithm_machines(&mut OsRng, &algorithm, &keys),
    &[],
  );

  assert!(proof.verify(
    &mut RecommendedTranscript::new(b"Generalized Schnorr MPC Proof Test"),
    matrix,
    outputs
  ));
}
