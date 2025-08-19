use rand_core::OsRng;

use transcript::{Transcript, RecommendedTranscript};

use multiexp::BatchVerifier;
use ciphersuite::group::{ff::Field, Group};
use dalek_ff_group::{Scalar, EdwardsPoint};

use modular_frost::tests::{key_gen, algorithm_machines, sign};

use crate::{
  Output,
  sal::{*, multisig::*},
};

#[test]
fn test_sal_multisig() {
  let x = Scalar::random(&mut OsRng);

  let mut keys = key_gen::<_, Ed25519T>(&mut OsRng);

  let O = (EdwardsPoint::generator() * x) + keys.values().next().unwrap().group_key();
  let I = EdwardsPoint::random(&mut OsRng);
  let C = EdwardsPoint::random(&mut OsRng);

  let L = I * x;

  let rerandomized_output = RerandomizedOutput::new(&mut OsRng, Output::new(O, I, C).unwrap());
  let input = rerandomized_output.input();

  let algorithm = SalAlgorithm::new(
    OsRng,
    RecommendedTranscript::new(b"SpendAuthAndLinkability Multisig Test"),
    [0; 32],
    rerandomized_output.clone(),
    x,
  );

  for keys in keys.values_mut() {
    let new_keys = keys.clone().offset(-rerandomized_output.o_blind());
    *keys = new_keys;
  }

  let sig = sign(
    &mut OsRng,
    &algorithm,
    keys.clone(),
    algorithm_machines(&mut OsRng, &algorithm, &keys),
    &[],
  );

  let mut verifier = BatchVerifier::new(1);
  sig.verify(&mut OsRng, &mut verifier, [0; 32], &input, L);
  assert!(verifier.verify_vartime());
}
