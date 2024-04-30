use rand_core::OsRng;

use transcript::{Transcript, RecommendedTranscript};

use multiexp::BatchVerifier;
use ciphersuite::{group::ff::Field, Ciphersuite, Ristretto};

use crate::{
  ScalarVector, ScalarMatrix, PointVector, PedersenCommitment, PedersenVectorCommitment,
  arithmetic_circuit_proof::{ArithmeticCircuitStatement, ArithmeticCircuitWitness},
  tests::generators,
};

#[test]
fn test_zero_arithmetic_circuit() {
  let generators = generators(1);

  let value = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let gamma = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let commitment = (generators.g() * value) + (generators.h() * gamma);
  let V = PointVector(vec![commitment]);

  let zero_vec =
    || ScalarVector::<<Ristretto as Ciphersuite>::F>(vec![<Ristretto as Ciphersuite>::F::ZERO]);

  let aL = zero_vec();
  let aR = zero_vec();

  let mut WL = ScalarMatrix::new();
  WL.push(vec![(0, <Ristretto as Ciphersuite>::F::ZERO)]);
  let mut WR = ScalarMatrix::new();
  WR.push(vec![(0, <Ristretto as Ciphersuite>::F::ZERO)]);
  let mut WO = ScalarMatrix::new();
  WO.push(vec![(0, <Ristretto as Ciphersuite>::F::ZERO)]);
  let mut WV = ScalarMatrix::new();
  WV.push(vec![(0, <Ristretto as Ciphersuite>::F::ZERO)]);
  let c = zero_vec();

  let statement = ArithmeticCircuitStatement::<_, Ristretto>::new(
    generators.reduce(1).unwrap(),
    WL,
    WR,
    WO,
    vec![],
    WV,
    c,
    PointVector(vec![]),
    V,
  )
  .unwrap();
  let witness = ArithmeticCircuitWitness::<Ristretto>::new(
    aL,
    aR,
    vec![],
    vec![PedersenCommitment { value, mask: gamma }],
  )
  .unwrap();

  let mut transcript = RecommendedTranscript::new(b"Zero Circuit Test");
  let proof = statement.clone().prove(&mut OsRng, &mut transcript.clone(), witness).unwrap();
  let mut verifier = BatchVerifier::new(1);
  statement.verify(&mut OsRng, &mut verifier, &mut transcript, proof).unwrap();
  assert!(verifier.verify_vartime());
}

#[test]
fn test_vector_commitment_arithmetic_circuit() {
  let generators = generators(2);
  let reduced = generators.reduce(2).unwrap();

  let v1 = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let v2 = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let gamma = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let commitment = (reduced.g_bold(0) * v1) + (reduced.g_bold(1) * v2) + (generators.h() * gamma);
  let V = PointVector(vec![]);
  let C = PointVector(vec![commitment]);

  let zero_vec =
    || ScalarVector::<<Ristretto as Ciphersuite>::F>(vec![<Ristretto as Ciphersuite>::F::ZERO]);

  let aL = zero_vec();
  let aR = zero_vec();

  let mut WL = ScalarMatrix::new();
  WL.push(vec![(0, <Ristretto as Ciphersuite>::F::ZERO)]);
  let mut WR = ScalarMatrix::new();
  WR.push(vec![(0, <Ristretto as Ciphersuite>::F::ZERO)]);
  let mut WO = ScalarMatrix::new();
  WO.push(vec![(0, <Ristretto as Ciphersuite>::F::ZERO)]);
  let mut WV = ScalarMatrix::new();
  WV.push(vec![]);
  let mut WC = vec![ScalarMatrix::new()];
  WC[0]
    .push(vec![(0, <Ristretto as Ciphersuite>::F::ONE), (1, <Ristretto as Ciphersuite>::F::ONE)]);
  let c = ScalarVector::<<Ristretto as Ciphersuite>::F>(vec![v1 + v2]);

  let statement =
    ArithmeticCircuitStatement::<_, Ristretto>::new(reduced, WL, WR, WO, WC, WV, c, C, V).unwrap();
  let witness = ArithmeticCircuitWitness::<Ristretto>::new(
    aL,
    aR,
    vec![PedersenVectorCommitment { values: ScalarVector(vec![v1, v2]), mask: gamma }],
    vec![],
  )
  .unwrap();

  let mut transcript = RecommendedTranscript::new(b"Vector Commitment Circuit Test");
  let proof = statement.clone().prove(&mut OsRng, &mut transcript.clone(), witness).unwrap();
  let mut verifier = BatchVerifier::new(1);
  statement.verify(&mut OsRng, &mut verifier, &mut transcript, proof).unwrap();
  assert!(verifier.verify_vartime());
}

#[test]
fn test_multiplication_arithmetic_circuit() {
  #[allow(unused)]
  let m = 4; // Input secrets
  let n = 1; // Multiplications
  let q = 5; // Constraints

  // Hand-written circuit for:
  // Commitments x, y, z, z1
  // x * y = z
  // z + 1 = z1

  let generators = generators(n);

  let commit = |value, gamma| (generators.g() * value) + (generators.h() * gamma);

  let x = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let x_mask = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let x_commitment = commit(x, x_mask);

  let x_vector_mask = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let x_vector_commitment =
    (generators.reduce(1).unwrap().g_bold(0) * x) + (generators.h() * x_vector_mask);

  let y = x.double();
  let y_mask = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let y_commitment = commit(y, y_mask);

  let z = x * y;
  let z_mask = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let z_commitment = commit(z, z_mask);

  let z1 = z + <Ristretto as Ciphersuite>::F::ONE;
  let z1_mask = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let z1_commitment = commit(z1, z1_mask);

  let V = PointVector(vec![x_commitment, y_commitment, z_commitment, z1_commitment]);
  let C = PointVector(vec![x_vector_commitment]);

  let aL = ScalarVector::<<Ristretto as Ciphersuite>::F>(vec![x]);
  let aR = ScalarVector::<<Ristretto as Ciphersuite>::F>(vec![y]);

  let mut WL = ScalarMatrix::new();
  WL.push(vec![(0, <Ristretto as Ciphersuite>::F::ONE)]);
  while WL.len() < q {
    WL.push(vec![]);
  }

  let mut WR = ScalarMatrix::new();
  WR.push(vec![]);
  WR.push(vec![(0, <Ristretto as Ciphersuite>::F::ONE)]);
  WR.push(vec![]);
  WR.push(vec![]);
  WR.push(vec![(0, <Ristretto as Ciphersuite>::F::ONE)]);

  let mut WO = ScalarMatrix::new();
  WO.push(vec![]);
  WO.push(vec![]);
  WO.push(vec![(0, <Ristretto as Ciphersuite>::F::ONE)]);
  WO.push(vec![(0, <Ristretto as Ciphersuite>::F::ONE)]);
  WO.push(vec![]);

  let mut WV = ScalarMatrix::new();
  // Constrain inputs
  WV.push(vec![(0, <Ristretto as Ciphersuite>::F::from(2u64))]);
  WV.push(vec![(1, <Ristretto as Ciphersuite>::F::ONE)]);
  // Confirm the multiplication
  WV.push(vec![(2, <Ristretto as Ciphersuite>::F::ONE)]);
  // Verify the next commitment is output + 1
  WV.push(vec![(3, <Ristretto as Ciphersuite>::F::ONE)]);
  // Verify y is 2x
  WV.push(vec![(0, <Ristretto as Ciphersuite>::F::ONE.double())]);

  let mut WC = vec![ScalarMatrix::new()];
  WC[0].push(vec![(0, <Ristretto as Ciphersuite>::F::ONE)]);
  WC[0].push(vec![]);
  WC[0].push(vec![]);
  WC[0].push(vec![]);
  WC[0].push(vec![]);

  let c = ScalarVector::<<Ristretto as Ciphersuite>::F>(vec![
    <Ristretto as Ciphersuite>::F::ZERO,
    <Ristretto as Ciphersuite>::F::ZERO,
    <Ristretto as Ciphersuite>::F::ZERO,
    -<Ristretto as Ciphersuite>::F::ONE,
    <Ristretto as Ciphersuite>::F::ZERO,
  ]);

  let statement = ArithmeticCircuitStatement::<_, Ristretto>::new(
    generators.reduce(1).unwrap(),
    WL,
    WR,
    WO,
    WC,
    WV,
    c,
    C,
    V,
  )
  .unwrap();
  let witness = ArithmeticCircuitWitness::<Ristretto>::new(
    aL,
    aR,
    vec![PedersenVectorCommitment { values: ScalarVector(vec![x]), mask: x_vector_mask }],
    vec![
      PedersenCommitment { value: x, mask: x_mask },
      PedersenCommitment { value: y, mask: y_mask },
      PedersenCommitment { value: z, mask: z_mask },
      PedersenCommitment { value: z1, mask: z1_mask },
    ],
  )
  .unwrap();

  let mut transcript = RecommendedTranscript::new(b"Multiplication Circuit Test");
  let proof = statement.clone().prove(&mut OsRng, &mut transcript.clone(), witness).unwrap();
  let mut verifier = BatchVerifier::new(1);
  statement.verify(&mut OsRng, &mut verifier, &mut transcript, proof).unwrap();
  assert!(verifier.verify_vartime());
}
