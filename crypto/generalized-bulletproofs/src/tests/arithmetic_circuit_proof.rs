use rand_core::{RngCore, OsRng};

use transcript::{Transcript, RecommendedTranscript};

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
  let mut verifier = generators.batch_verifier();
  statement.verify(&mut OsRng, &mut verifier, &mut transcript, proof).unwrap();
  assert!(generators.verify(verifier));
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
  let mut verifier = generators.batch_verifier();
  statement.verify(&mut OsRng, &mut verifier, &mut transcript, proof).unwrap();
  assert!(generators.verify(verifier));
}

#[test]
fn fuzz_test_arithmetic_circuit() {
  let generators = generators(32);

  for i in 0 .. 100 {
    dbg!(i);

    // Create aL, aR, aO
    let mut aL = ScalarVector(vec![]);
    let mut aR = ScalarVector(vec![]);
    while aL.len() < ((OsRng.next_u64() % 8) + 1).try_into().unwrap() {
      aL.0.push(<Ristretto as Ciphersuite>::F::random(&mut OsRng));
    }
    while aR.len() < aL.len() {
      aR.0.push(<Ristretto as Ciphersuite>::F::random(&mut OsRng));
    }
    let aO = aL.clone() * &aR;

    let mut C = vec![];
    while C.len() < (OsRng.next_u64() % 16).try_into().unwrap() {
      let mut values = ScalarVector(vec![]);
      while values.0.len() < ((OsRng.next_u64() % 8) + 1).try_into().unwrap() {
        values.0.push(<Ristretto as Ciphersuite>::F::random(&mut OsRng));
      }
      C.push(PedersenVectorCommitment {
        values,
        mask: <Ristretto as Ciphersuite>::F::random(&mut OsRng),
      });
    }
    let mut V = vec![];
    while V.len() < (OsRng.next_u64() % 4).try_into().unwrap() {
      V.push(PedersenCommitment {
        value: <Ristretto as Ciphersuite>::F::random(&mut OsRng),
        mask: <Ristretto as Ciphersuite>::F::random(&mut OsRng),
      });
    }

    let mut WL = ScalarMatrix::new();
    let mut WR = ScalarMatrix::new();
    let mut WO = ScalarMatrix::new();
    let mut WC = vec![];
    for _ in 0 .. C.len() {
      WC.push(ScalarMatrix::new());
    }
    let mut WV = ScalarMatrix::new();
    let mut c = ScalarVector(vec![]);

    // Generate random constraints
    for _ in 0 .. (OsRng.next_u64() % 8).try_into().unwrap() {
      let mut eval = <Ristretto as Ciphersuite>::F::ZERO;

      {
        let mut wl = vec![];
        for _ in 0 .. (OsRng.next_u64() % 4) {
          let index = usize::try_from(OsRng.next_u64()).unwrap() % aL.len();
          let weight = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
          wl.push((index, weight));
          eval += weight * aL[index];
        }
        WL.push(wl);
      }

      {
        let mut wr = vec![];
        for _ in 0 .. (OsRng.next_u64() % 4) {
          let index = usize::try_from(OsRng.next_u64()).unwrap() % aR.len();
          let weight = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
          wr.push((index, weight));
          eval += weight * aR[index];
        }
        WR.push(wr);
      }

      {
        let mut wo = vec![];
        for _ in 0 .. (OsRng.next_u64() % 4) {
          let index = usize::try_from(OsRng.next_u64()).unwrap() % aO.len();
          let weight = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
          wo.push((index, weight));
          eval += weight * aO[index];
        }
        WO.push(wo);
      }

      for (WC, C) in WC.iter_mut().zip(C.iter()) {
        let mut wc = vec![];
        for _ in 0 .. (OsRng.next_u64() % 4) {
          let index = usize::try_from(OsRng.next_u64()).unwrap() % C.values.len();
          let weight = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
          wc.push((index, weight));
          eval += weight * C.values[index];
        }
        WC.push(wc);
      }

      {
        let mut wv = vec![];
        if !V.is_empty() {
          for _ in 0 .. (OsRng.next_u64() % 4) {
            let index = usize::try_from(OsRng.next_u64()).unwrap() % V.len();
            let weight = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
            wv.push((index, weight));
            eval -= weight * V[index].value;
          }
        }
        WV.push(wv);
      }

      c.0.push(eval);
    }

    let statement = ArithmeticCircuitStatement::<_, Ristretto>::new(
      generators.reduce(16).unwrap(),
      WL,
      WR,
      WO,
      WC,
      WV,
      c,
      PointVector(C.iter().map(|C| C.commit(generators.g_bold_slice(), generators.h())).collect()),
      PointVector(V.iter().map(|V| V.commit(generators.g(), generators.h())).collect()),
    )
    .unwrap();

    let witness = ArithmeticCircuitWitness::<Ristretto>::new(aL, aR, C, V).unwrap();

    let mut transcript = RecommendedTranscript::new(b"Fuzz Arithmetic Circuit Test");
    let proof = statement.clone().prove(&mut OsRng, &mut transcript.clone(), witness).unwrap();
    let mut verifier = generators.batch_verifier();
    statement.verify(&mut OsRng, &mut verifier, &mut transcript, proof).unwrap();
    assert!(generators.verify(verifier));
  }
}
