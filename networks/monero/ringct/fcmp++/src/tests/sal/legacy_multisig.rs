use rand_core::OsRng;

use transcript::{Transcript, RecommendedTranscript};

use multiexp::BatchVerifier;
use ciphersuite::group::{ff::Field, Group};
use dalek_ff_group::{Scalar, EdwardsPoint};

use modular_frost::{
  curve::Ed25519,
  tests::{key_gen, algorithm_machines, sign, recover_key},
};

use monero_generators::T;

use crate::{
  Output,
  sal::{*, legacy_multisig::*},
};

#[test]
fn test_sal_legacy_multisig() {
  let y = Scalar::random(&mut OsRng);

  let keys = key_gen::<_, Ed25519>(&mut OsRng);

  let O = keys.values().next().unwrap().group_key() + (EdwardsPoint(*T) * y);
  let I = EdwardsPoint::random(&mut OsRng);
  let C = EdwardsPoint::random(&mut OsRng);

  let rerandomized_output = RerandomizedOutput::new(&mut OsRng, Output::new(O, I, C).unwrap());
  let input = rerandomized_output.input();

  let algorithm = SalLegacyAlgorithm::new(
    OsRng,
    RecommendedTranscript::new(b"SpendAuthAndLinkability Legacy Multisig Test"),
    [0; 32],
    rerandomized_output,
    y,
  );

  let (L, sig) = sign(
    &mut OsRng,
    &algorithm,
    keys.clone(),
    algorithm_machines(&mut OsRng, &algorithm, &keys),
    &[],
  );
  assert_eq!(I * *recover_key(&keys.values().cloned().collect::<Vec<_>>()).unwrap(), L);

  let mut verifier = BatchVerifier::new(1);
  sig.verify(&mut OsRng, &mut verifier, [0; 32], &input, L);
  assert!(verifier.verify_vartime());
}
