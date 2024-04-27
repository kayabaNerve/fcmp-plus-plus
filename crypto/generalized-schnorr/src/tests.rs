use zeroize::Zeroizing;
use rand_core::OsRng;

use transcript::{Transcript, RecommendedTranscript};

use ciphersuite::{
  group::{ff::Field, Group},
  Ciphersuite, Ed25519,
};

use crate::GeneralizedSchnorr;

#[test]
fn test() {
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

  let (outputs, proof) = GeneralizedSchnorr::<Ed25519, OUTPUTS, SCALARS, SCALARS_PLUS_TWO>::prove(
    &mut OsRng,
    &mut RecommendedTranscript::new(b"Generalized Schnorr Test"),
    matrix,
    [
      &Zeroizing::new(<Ed25519 as Ciphersuite>::F::random(&mut OsRng)),
      &Zeroizing::new(<Ed25519 as Ciphersuite>::F::random(&mut OsRng)),
    ],
  );
  assert!(proof.verify(
    &mut RecommendedTranscript::new(b"Generalized Schnorr Test"),
    matrix,
    outputs
  ));
}
