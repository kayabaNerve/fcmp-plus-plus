use rand_core::{RngCore, OsRng};

use ciphersuite::{group::ff::Field, Ciphersuite, Ristretto};

use crate::{
  ScalarVector, ScalarMatrix, PointVector, PedersenCommitment, PedersenVectorCommitment,
  transcript::*,
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

  let statement = ArithmeticCircuitStatement::<Ristretto>::new(
    generators.reduce(1).unwrap(),
    WL,
    WR,
    WO,
    vec![],
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

  let proof = {
    let mut transcript = Transcript::new([0; 32]);
    statement.clone().prove(&mut OsRng, &mut transcript, witness).unwrap();
    transcript.complete()
  };
  let mut verifier = generators.batch_verifier();
  statement
    .verify(&mut OsRng, &mut verifier, &mut VerifierTranscript::new([0; 32], &proof))
    .unwrap();
  assert!(generators.verify(verifier));
}

#[test]
fn test_vector_commitment_arithmetic_circuit() {
  let generators = generators(2);
  let reduced = generators.reduce(2).unwrap();

  let v1 = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let v2 = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let v3 = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let v4 = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let gamma = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
  let commitment = (reduced.g_bold(0) * v1) +
    (reduced.g_bold(1) * v2) +
    (reduced.h_bold(0) * v3) +
    (reduced.h_bold(1) * v4) +
    (generators.h() * gamma);
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
  let mut WCL = vec![ScalarMatrix::new()];
  WCL[0].push(vec![
    (0, <Ristretto as Ciphersuite>::F::ONE),
    (1, <Ristretto as Ciphersuite>::F::from(2u64)),
  ]);
  let mut WCR = vec![ScalarMatrix::new()];
  WCR[0].push(vec![
    (0, <Ristretto as Ciphersuite>::F::from(3u64)),
    (1, <Ristretto as Ciphersuite>::F::from(4u64)),
  ]);
  let c = ScalarVector::<<Ristretto as Ciphersuite>::F>(vec![
    v1 + (v2 + v2) + (v3 + v3 + v3) + (v4 + v4 + v4 + v4),
  ]);

  let statement =
    ArithmeticCircuitStatement::<Ristretto>::new(reduced, WL, WR, WO, WCL, WCR, WV, c, C, V)
      .unwrap();
  let witness = ArithmeticCircuitWitness::<Ristretto>::new(
    aL,
    aR,
    vec![PedersenVectorCommitment {
      g_values: ScalarVector(vec![v1, v2]),
      h_values: ScalarVector(vec![v3, v4]),
      mask: gamma,
    }],
    vec![],
  )
  .unwrap();

  let proof = {
    let mut transcript = Transcript::new([0; 32]);
    statement.clone().prove(&mut OsRng, &mut transcript, witness).unwrap();
    transcript.complete()
  };
  let mut verifier = generators.batch_verifier();
  statement
    .verify(&mut OsRng, &mut verifier, &mut VerifierTranscript::new([0; 32], &proof))
    .unwrap();
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
      let mut g_values = ScalarVector(vec![]);
      while g_values.0.len() < ((OsRng.next_u64() % 8) + 1).try_into().unwrap() {
        g_values.0.push(<Ristretto as Ciphersuite>::F::random(&mut OsRng));
      }
      let mut h_values = ScalarVector(vec![]);
      while h_values.0.len() < ((OsRng.next_u64() % 8) + 1).try_into().unwrap() {
        h_values.0.push(<Ristretto as Ciphersuite>::F::random(&mut OsRng));
      }
      C.push(PedersenVectorCommitment {
        g_values,
        h_values,
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
    let mut WCL = vec![];
    let mut WCR = vec![];
    for _ in 0 .. C.len() {
      WCL.push(ScalarMatrix::new());
      WCR.push(ScalarMatrix::new());
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

      for ((WCL, WCR), C) in WCL.iter_mut().zip(WCR.iter_mut()).zip(C.iter()) {
        let mut wcl = vec![];
        for _ in 0 .. (OsRng.next_u64() % 4) {
          let index = usize::try_from(OsRng.next_u64()).unwrap() % C.g_values.len();
          let weight = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
          wcl.push((index, weight));
          eval += weight * C.g_values[index];
        }
        WCL.push(wcl);

        let mut wcr = vec![];
        for _ in 0 .. (OsRng.next_u64() % 4) {
          let index = usize::try_from(OsRng.next_u64()).unwrap() % C.h_values.len();
          let weight = <Ristretto as Ciphersuite>::F::random(&mut OsRng);
          wcr.push((index, weight));
          eval += weight * C.h_values[index];
        }
        WCR.push(wcr);
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

    let statement = ArithmeticCircuitStatement::<Ristretto>::new(
      generators.reduce(16).unwrap(),
      WL,
      WR,
      WO,
      WCL,
      WCR,
      WV,
      c,
      PointVector(
        C.iter()
          .map(|C| {
            C.commit(generators.g_bold_slice(), generators.h_bold_slice(), generators.h()).unwrap()
          })
          .collect(),
      ),
      PointVector(V.iter().map(|V| V.commit(generators.g(), generators.h())).collect()),
    )
    .unwrap();

    let witness = ArithmeticCircuitWitness::<Ristretto>::new(aL, aR, C, V).unwrap();

    let proof = {
      let mut transcript = Transcript::new([0; 32]);
      statement.clone().prove(&mut OsRng, &mut transcript, witness).unwrap();
      transcript.complete()
    };
    let mut verifier = generators.batch_verifier();
    statement
      .verify(&mut OsRng, &mut verifier, &mut VerifierTranscript::new([0; 32], &proof))
      .unwrap();
    assert!(generators.verify(verifier));
  }
}
