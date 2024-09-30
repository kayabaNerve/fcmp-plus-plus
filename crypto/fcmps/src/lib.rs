#![allow(non_snake_case)]

use core::marker::PhantomData;

use rand_core::{RngCore, CryptoRng};
use zeroize::{Zeroize, Zeroizing};

use blake2::{
  digest::{consts::U32, Digest},
  Blake2b,
};

use ciphersuite::{
  group::{
    ff::{Field, PrimeField},
    Group, GroupEncoding,
  },
  Ciphersuite,
};

use ec_divisors::{DivisorCurve, ScalarDecomposition};
use generalized_bulletproofs::{
  BatchVerifier, PedersenVectorCommitment,
  transcript::{Transcript as ProverTranscript, VerifierTranscript},
};

mod gadgets;
pub(crate) use gadgets::*;
mod circuit;
pub(crate) use circuit::*;
pub use circuit::FcmpCurves;

mod blinds;
pub use blinds::*;

mod tape;
use tape::*;

mod params;
pub use params::*;

pub mod tree;

#[cfg(test)]
mod tests;

/// A struct representing an output tuple.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Zeroize)]
pub struct Output<G: Group> {
  O: G,
  I: G,
  C: G,
}

impl<G: Group> Output<G> {
  pub fn new(O: G, I: G, C: G) -> Option<Self> {
    if bool::from(O.is_identity() | I.is_identity() | C.is_identity()) {
      None?;
    }
    Some(Output { O, I, C })
  }
}

/// A struct representing an input tuple.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Zeroize)]
pub struct Input<F: PrimeField> {
  O_tilde: (F, F),
  I_tilde: (F, F),
  R: (F, F),
  C_tilde: (F, F),
}

impl<F: PrimeField> Input<F> {
  pub fn new<G: DivisorCurve<FieldElement = F>>(
    O_tilde: G,
    I_tilde: G,
    R: G,
    C_tilde: G,
  ) -> Option<Self> {
    Some(Input {
      O_tilde: G::to_xy(O_tilde)?,
      I_tilde: G::to_xy(I_tilde)?,
      R: G::to_xy(R)?,
      C_tilde: G::to_xy(C_tilde)?,
    })
  }
}

/// A tree root, represented as a point from either curve.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TreeRoot<C1: Ciphersuite, C2: Ciphersuite> {
  C1(C1::G),
  C2(C2::G),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Branches<C: FcmpCurves> {
  leaves: Vec<Output<<C::OC as Ciphersuite>::G>>,
  curve_2_layers: Vec<Vec<<C::C2 as Ciphersuite>::F>>,
  curve_1_layers: Vec<Vec<<C::C1 as Ciphersuite>::F>>,
}

/// The full-chain membership proof.
#[derive(Clone, Debug, Zeroize)]
pub struct Fcmp<C: FcmpCurves> {
  _curves: PhantomData<C>,
  proof: Vec<u8>,
  root_blind_pok: [u8; 64],
}
impl<C: FcmpCurves> Fcmp<C>
where
  <C::OC as Ciphersuite>::G: DivisorCurve<FieldElement = <C::C1 as Ciphersuite>::F>,
  <C::C1 as Ciphersuite>::G: DivisorCurve<FieldElement = <C::C2 as Ciphersuite>::F>,
  <C::C2 as Ciphersuite>::G: DivisorCurve<FieldElement = <C::C1 as Ciphersuite>::F>,
{
  fn transcript(
    tree: TreeRoot<C::C1, C::C2>,
    input: Input<<C::C1 as Ciphersuite>::F>,
    root_blind_R: &[u8],
  ) -> [u8; 32] {
    let mut res = Blake2b::<U32>::new();

    // Transcript the tree root
    match tree {
      TreeRoot::C1(p) => {
        res.update([0]);
        res.update(p.to_bytes());
      }
      TreeRoot::C2(p) => {
        res.update([1]);
        res.update(p.to_bytes());
      }
    }

    // Transcript the input tuple
    res.update(input.O_tilde.0.to_repr());
    res.update(input.O_tilde.1.to_repr());
    res.update(input.I_tilde.0.to_repr());
    res.update(input.I_tilde.1.to_repr());
    res.update(input.R.0.to_repr());
    res.update(input.R.1.to_repr());
    res.update(input.C_tilde.0.to_repr());
    res.update(input.C_tilde.1.to_repr());

    // Transcript the nonce for the difference of the root and our output VC of the root
    res.update(root_blind_R);

    res.finalize().into()
  }

  pub fn prove<R: RngCore + CryptoRng>(
    rng: &mut R,
    params: &FcmpParams<C>,
    tree: TreeRoot<C::C1, C::C2>,
    output: Output<<C::OC as Ciphersuite>::G>,
    output_blinds: BlindedOutput<<C::OC as Ciphersuite>::G>,
    branches: Branches<C>,
  ) -> Self
  where
    <C::C1 as Ciphersuite>::G: GroupEncoding<Repr = [u8; 32]>,
    <C::C2 as Ciphersuite>::G: GroupEncoding<Repr = [u8; 32]>,
    <C::C1 as Ciphersuite>::F: PrimeField<Repr = [u8; 32]>,
    <C::C2 as Ciphersuite>::F: PrimeField<Repr = [u8; 32]>,
  {
    // Flatten the leaves for the branch
    let mut flattened_leaves = vec![];
    for leaf in branches.leaves {
      // leaf is of type Output which checks its members to not be the identity
      flattened_leaves.extend(&[
        <C::OC as Ciphersuite>::G::to_xy(leaf.O).unwrap().0,
        <C::OC as Ciphersuite>::G::to_xy(leaf.I).unwrap().0,
        <C::OC as Ciphersuite>::G::to_xy(leaf.C).unwrap().0,
      ]);
    }

    // Append the leaves and the rest of the branches to the tape
    let mut c1_tape =
      VectorCommitmentTape { commitment_len: 256, current_j_offset: 0, commitments: vec![] };
    let mut c1_branches = vec![];
    {
      let branch = c1_tape.append_branch::<C::C1>(flattened_leaves.len(), Some(flattened_leaves));
      c1_branches.push(branch);
    }
    for branch in branches.curve_1_layers {
      let branch = c1_tape.append_branch::<C::C1>(branch.len(), Some(branch));
      c1_branches.push(branch);
    }

    let mut c2_tape =
      VectorCommitmentTape { commitment_len: 128, current_j_offset: 0, commitments: vec![] };
    let mut c2_branches = vec![];
    for branch in branches.curve_2_layers {
      let branch = c2_tape.append_branch::<C::C2>(branch.len(), Some(branch));
      c2_branches.push(branch);
    }

    // Decide blinds for each branch
    // TODO: Move this out of prove so it can be done async
    let mut branches_1_blinds = vec![];
    let mut branches_1_blinds_prepared = vec![];
    for _ in 0 .. c1_branches.len() {
      let blind = <C::C1 as Ciphersuite>::F::random(&mut *rng);
      branches_1_blinds.push(blind);
      branches_1_blinds_prepared.push(BranchBlind::<<C::C1 as Ciphersuite>::G>::new(
        params.curve_1_generators.h(),
        ScalarDecomposition::new(-blind).unwrap(),
      ));
    }

    let mut branches_2_blinds = vec![];
    let mut branches_2_blinds_prepared = vec![];
    for _ in 0 .. c2_branches.len() {
      let blind = <C::C2 as Ciphersuite>::F::random(&mut *rng);
      branches_2_blinds.push(blind);
      branches_2_blinds_prepared.push(BranchBlind::<<C::C2 as Ciphersuite>::G>::new(
        params.curve_2_generators.h(),
        ScalarDecomposition::new(-blind).unwrap(),
      ));
    }

    // Accumulate the opening for the leaves
    let append_claimed_point_1 =
      |c1_tape: &mut VectorCommitmentTape<<C::C1 as Ciphersuite>::F>,
       dlog: &[u64],
       scalar_mul_and_divisor: ScalarMulAndDivisor<<C::OC as Ciphersuite>::G>,
       padding| {
        c1_tape.append_claimed_point::<C::OcParameters>(
          Some(dlog),
          Some(scalar_mul_and_divisor.divisor),
          Some((scalar_mul_and_divisor.x, scalar_mul_and_divisor.y)),
          Some(padding),
        )
      };

    // Since this is presumed over Ed25519, which has a 253-bit discrete logarithm, we have two
    // items avilable in padding. We use this padding for all the other points we must commit to
    // For o_blind, we use the padding for O
    let (o_blind_claim, O) = {
      let (x, y) = <C::OC as Ciphersuite>::G::to_xy(output.O).unwrap();

      append_claimed_point_1(
        &mut c1_tape,
        output_blinds.o_blind.0.scalar.decomposition(),
        output_blinds.o_blind.0.scalar_mul_and_divisor.clone(),
        vec![x, y],
      )
    };
    // For i_blind_u, we use the padding for I
    let (i_blind_u_claim, I) = {
      let (x, y) = <C::OC as Ciphersuite>::G::to_xy(output.I).unwrap();
      append_claimed_point_1(
        &mut c1_tape,
        output_blinds.i_blind.scalar.decomposition(),
        output_blinds.i_blind.u.clone(),
        vec![x, y],
      )
    };

    // Commit to the divisor for `i_blind V`, which doesn't commit to the point `i_blind V`
    // (and that still has to be done)
    let (i_blind_v_divisor, _extra) = c1_tape.append_divisor(
      Some(output_blinds.i_blind.v.divisor.clone()),
      Some(<C::C1 as Ciphersuite>::F::ZERO),
    );

    // For i_blind_blind, we use the padding for (i_blind V)
    let (i_blind_blind_claim, i_blind_V) = {
      let (x, y) = (output_blinds.i_blind.v.x, output_blinds.i_blind.v.y);
      append_claimed_point_1(
        &mut c1_tape,
        output_blinds.i_blind_blind.0.scalar.decomposition(),
        output_blinds.i_blind_blind.0.scalar_mul_and_divisor.clone(),
        vec![x, y],
      )
    };

    let i_blind_v_claim = PointWithDlog {
      // This has the same discrete log, i_blind, as i_blind_u
      dlog: i_blind_u_claim.dlog.clone(),
      divisor: i_blind_v_divisor,
      point: (i_blind_V[0], i_blind_V[1]),
    };

    // For c_blind, we use the padding for C
    let (c_blind_claim, C) = {
      let (x, y) = <C::OC as Ciphersuite>::G::to_xy(output.C).unwrap();
      append_claimed_point_1(
        &mut c1_tape,
        output_blinds.c_blind.0.scalar.decomposition(),
        output_blinds.c_blind.0.scalar_mul_and_divisor.clone(),
        vec![x, y],
      )
    };

    // We now have committed to O, I, C, and all interpolated points

    // The first circuit's tape opens the blinds from the second curve
    let mut commitment_blind_claims_1 = vec![];
    for blind in branches_2_blinds_prepared {
      commitment_blind_claims_1.push(
        c1_tape
          .append_claimed_point::<C::C2Parameters>(
            Some(blind.0.scalar.decomposition()),
            Some(blind.0.scalar_mul_and_divisor.divisor),
            Some((blind.0.scalar_mul_and_divisor.x, blind.0.scalar_mul_and_divisor.y)),
            Some(vec![]),
          )
          .0,
      );
    }

    // The second circuit's tape opens the blinds from the first curve
    let mut commitment_blind_claims_2 = vec![];
    for blind in branches_1_blinds_prepared {
      commitment_blind_claims_2.push(
        c2_tape
          .append_claimed_point::<C::C1Parameters>(
            Some(blind.0.scalar.decomposition()),
            Some(blind.0.scalar_mul_and_divisor.divisor),
            Some((blind.0.scalar_mul_and_divisor.x, blind.0.scalar_mul_and_divisor.y)),
            Some(vec![]),
          )
          .0,
      );
    }

    // We have now committed to the discrete logs, the divisors, and the output points...
    // and the sets, and the set members used within the tuple set membership (as needed)

    // Calculate all of the PVCs and transcript them
    let mut root_blind_r_C1 = None;
    let mut root_blind_r_C2 = None;
    let mut root_blind_C1 = None;
    let mut root_blind_C2 = None;
    let root_blind_R: [u8; 32];
    if branches_1_blinds.len() > branches_2_blinds.len() {
      root_blind_C1 = Some(*branches_1_blinds.last().unwrap());
      let root_blind_r = Zeroizing::new(<C::C1 as Ciphersuite>::F::random(&mut *rng));
      root_blind_R = (params.curve_1_generators.h() * *root_blind_r).to_bytes();
      root_blind_r_C1 = Some(root_blind_r);
    } else {
      root_blind_C2 = Some(*branches_2_blinds.last().unwrap());
      let root_blind_r = Zeroizing::new(<C::C2 as Ciphersuite>::F::random(&mut *rng));
      root_blind_R = (params.curve_2_generators.h() * *root_blind_r).to_bytes();
      root_blind_r_C2 = Some(root_blind_r);
    }

    let mut pvc_blinds_1 = branches_1_blinds;
    while pvc_blinds_1.len() < c1_tape.commitments.len() {
      pvc_blinds_1.push(<C::C1 as Ciphersuite>::F::random(&mut *rng));
    }

    let mut pvc_blinds_2 = branches_2_blinds;
    while pvc_blinds_2.len() < c2_tape.commitments.len() {
      pvc_blinds_2.push(<C::C2 as Ciphersuite>::F::random(&mut *rng));
    }

    let commitments_1 = c1_tape.commit(&params.curve_1_generators, &pvc_blinds_1);
    let commitments_2 = c2_tape.commit(&params.curve_2_generators, &pvc_blinds_2);

    let mut transcript =
      ProverTranscript::new(Self::transcript(tree, output_blinds.input, &root_blind_R));
    let commitments_1 = transcript.write_commitments(commitments_1, vec![]);
    let commitments_2 = transcript.write_commitments(commitments_2, vec![]);

    let mut root_blind_pok = [0; 64];
    if c1_branches.len() > c2_branches.len() {
      let s = *root_blind_r_C1.unwrap() +
        (transcript.challenge::<<C::C1 as Ciphersuite>::F>() * root_blind_C1.unwrap());
      root_blind_pok[.. 32].copy_from_slice(&root_blind_R);
      root_blind_pok[32 ..].copy_from_slice(s.to_repr().as_ref());
    } else {
      let s = *root_blind_r_C2.unwrap() +
        (transcript.challenge::<<C::C2 as Ciphersuite>::F>() * root_blind_C2.unwrap());
      root_blind_pok[.. 32].copy_from_slice(&root_blind_R);
      root_blind_pok[32 ..].copy_from_slice(s.to_repr().as_ref());
    }

    // Create the circuits
    let mut c1_circuit = Circuit::<C::C1>::prove(
      c1_tape
        .commitments
        .into_iter()
        .zip(&pvc_blinds_1)
        .map(|((g_values, h_values), mask)| PedersenVectorCommitment {
          g_values: g_values.into(),
          h_values: h_values.into(),
          mask: *mask,
        })
        .collect(),
    );
    let mut c2_circuit = Circuit::<C::C2>::prove(
      c2_tape
        .commitments
        .into_iter()
        .zip(&pvc_blinds_2)
        .map(|((g_values, h_values), mask)| PedersenVectorCommitment {
          g_values: g_values.into(),
          h_values: h_values.into(),
          mask: *mask,
        })
        .collect(),
    );

    // Perform the layers
    c1_circuit.first_layer(
      &mut transcript,
      &CurveSpec {
        a: <<C::OC as Ciphersuite>::G as DivisorCurve>::a(),
        b: <<C::OC as Ciphersuite>::G as DivisorCurve>::b(),
      },
      &params.T_table,
      &params.U_table,
      &params.V_table,
      &params.G_table,
      //
      output_blinds.input.O_tilde,
      o_blind_claim,
      (O[0], O[1]),
      //
      output_blinds.input.I_tilde,
      i_blind_u_claim,
      (I[0], I[1]),
      //
      output_blinds.input.R,
      i_blind_v_claim,
      i_blind_blind_claim,
      //
      output_blinds.input.C_tilde,
      c_blind_claim,
      (C[0], C[1]),
      //
      c1_branches[0]
        .chunks(3)
        .map(|chunk| {
          assert_eq!(chunk.len(), 3);
          chunk.to_vec()
        })
        .collect(),
    );

    // We do have a spare blind for the last branch
    // If the first curve has more layers, it has the final blind
    // If the amount of layers are even, the blind is from the second curve
    if c1_branches.len() > c2_branches.len() {
      commitment_blind_claims_2.pop();
    } else {
      commitment_blind_claims_1.pop();
    }

    let mut c1_dlog_challenge = None;
    if commitment_blind_claims_1.first().is_some() {
      c1_dlog_challenge = Some(c1_circuit.additional_layer_discrete_log_challenge(
        &mut transcript,
        &CurveSpec {
          a: <<C::C2 as Ciphersuite>::G as DivisorCurve>::a(),
          b: <<C::C2 as Ciphersuite>::G as DivisorCurve>::b(),
        },
        &params.H_2_table,
      ));
    }

    assert_eq!(commitments_2.C().len(), pvc_blinds_2.len());
    // - 1, as the leaves are the first branch
    assert_eq!(c1_branches.len() - 1, commitment_blind_claims_1.len());
    assert!(commitments_2.C().len() > c1_branches.len());
    let commitment_iter = commitments_2.C().iter().cloned().zip(pvc_blinds_2.clone());
    let branch_iter = c1_branches.into_iter().skip(1).zip(commitment_blind_claims_1);
    // The following two to_xy calls have negligible probability of failing as they'd require
    // randomly selected blinds be the discrete logarithm of commitments, or one of our own
    // commitments be identity
    for ((mut prior_commitment, prior_blind), (branch, prior_blind_opening)) in
      commitment_iter.into_iter().zip(branch_iter)
    {
      prior_commitment += params.curve_2_hash_init;
      let unblinded_hash = prior_commitment - (params.curve_2_generators.h() * prior_blind);
      let (hash_x, hash_y, _) =
        c1_circuit.mul(None, None, Some(<C::C2 as Ciphersuite>::G::to_xy(unblinded_hash).unwrap()));
      c1_circuit.additional_layer(
        &CurveSpec {
          a: <<C::C2 as Ciphersuite>::G as DivisorCurve>::a(),
          b: <<C::C2 as Ciphersuite>::G as DivisorCurve>::b(),
        },
        c1_dlog_challenge.as_ref().unwrap(),
        <C::C2 as Ciphersuite>::G::to_xy(prior_commitment).unwrap(),
        prior_blind_opening,
        (hash_x, hash_y),
        branch,
      );
    }

    let mut c2_dlog_challenge = None;
    if commitment_blind_claims_2.first().is_some() {
      c2_dlog_challenge = Some(c2_circuit.additional_layer_discrete_log_challenge(
        &mut transcript,
        &CurveSpec {
          a: <<C::C1 as Ciphersuite>::G as DivisorCurve>::a(),
          b: <<C::C1 as Ciphersuite>::G as DivisorCurve>::b(),
        },
        &params.H_1_table,
      ));
    }

    assert_eq!(commitments_1.C().len(), pvc_blinds_1.len());
    assert_eq!(c2_branches.len(), commitment_blind_claims_2.len());
    assert!(commitments_1.C().len() > c2_branches.len());
    let commitment_iter = commitments_1.C().iter().cloned().zip(pvc_blinds_1.clone());
    let branch_iter = c2_branches.into_iter().zip(commitment_blind_claims_2);
    for ((mut prior_commitment, prior_blind), (branch, prior_blind_opening)) in
      commitment_iter.into_iter().zip(branch_iter)
    {
      prior_commitment += params.curve_1_hash_init;
      let unblinded_hash = prior_commitment - (params.curve_1_generators.h() * prior_blind);
      // unwrap should be safe as no hash we built should be identity
      let (hash_x, hash_y, _) =
        c2_circuit.mul(None, None, Some(<C::C1 as Ciphersuite>::G::to_xy(unblinded_hash).unwrap()));
      c2_circuit.additional_layer(
        &CurveSpec {
          a: <<C::C1 as Ciphersuite>::G as DivisorCurve>::a(),
          b: <<C::C1 as Ciphersuite>::G as DivisorCurve>::b(),
        },
        c2_dlog_challenge.as_ref().unwrap(),
        // unwrap should be safe as no commitment we've made should be identity
        <C::C1 as Ciphersuite>::G::to_xy(prior_commitment).unwrap(),
        prior_blind_opening,
        (hash_x, hash_y),
        branch,
      );
    }

    // Escape to the raw weights to form a GBP with
    assert!(c1_circuit.muls() <= 256);
    assert!(c2_circuit.muls() <= 128);
    // dbg!(c1_circuit.muls());
    // dbg!(c2_circuit.muls());

    // TODO: unwrap -> Result
    let (c1_statement, c1_witness) =
      c1_circuit.statement(params.curve_1_generators.reduce(256).unwrap(), commitments_1).unwrap();
    c1_statement.clone().prove(rng, &mut transcript, c1_witness.unwrap()).unwrap();

    let (c2_statement, c2_witness) =
      c2_circuit.statement(params.curve_2_generators.reduce(128).unwrap(), commitments_2).unwrap();
    c2_statement.prove(rng, &mut transcript, c2_witness.unwrap()).unwrap();

    Fcmp { _curves: PhantomData, proof: transcript.complete(), root_blind_pok }
  }

  #[allow(clippy::too_many_arguments)]
  pub fn verify<R: RngCore + CryptoRng>(
    &self,
    rng: &mut R,
    verifier_1: &mut BatchVerifier<C::C1>,
    verifier_2: &mut BatchVerifier<C::C2>,
    params: &FcmpParams<C>,
    tree: TreeRoot<C::C1, C::C2>,
    layer_lens: &[usize],
    input: Input<<C::C1 as Ciphersuite>::F>,
  ) {
    // TODO: Check the length of the VCs for this proof

    // Append the leaves and the rest of the branches to the tape

    let mut c1_tape =
      VectorCommitmentTape { commitment_len: 256, current_j_offset: 0, commitments: vec![] };
    let mut c1_branches = Vec::with_capacity((layer_lens.len() / 2) + (layer_lens.len() % 2));
    let mut c2_tape =
      VectorCommitmentTape { commitment_len: 128, current_j_offset: 0, commitments: vec![] };
    let mut c2_branches = Vec::with_capacity(layer_lens.len() / 2);

    for (i, layer_len) in layer_lens.iter().enumerate() {
      if (i % 2) == 0 {
        let branch = c1_tape.append_branch::<C::C1>(*layer_len, None);
        c1_branches.push(branch);
      } else {
        let branch = c2_tape.append_branch::<C::C2>(*layer_len, None);
        c2_branches.push(branch);
      }
    }

    // Accumulate the opening for the leaves
    let append_claimed_point_1 = |c1_tape: &mut VectorCommitmentTape<<C::C1 as Ciphersuite>::F>| {
      c1_tape.append_claimed_point::<C::OcParameters>(None, None, None, None)
    };

    // Since this is presumed over Ed25519, which has a 253-bit discrete logarithm, we have two
    // items avilable in padding. We use this padding for all the other points we must commit to
    // For o_blind, we use the padding for O
    let (o_blind_claim, O) = append_claimed_point_1(&mut c1_tape);
    // For i_blind_u, we use the padding for I
    let (i_blind_u_claim, I) = append_claimed_point_1(&mut c1_tape);

    // Commit to the divisor for `i_blind V`, which doesn't commit to the point `i_blind V`
    // (and that still has to be done)
    let (i_blind_v_divisor, _extra) = c1_tape.append_divisor(None, None);

    // For i_blind_blind, we use the padding for (i_blind V)
    let (i_blind_blind_claim, i_blind_V) = append_claimed_point_1(&mut c1_tape);

    let i_blind_v_claim = PointWithDlog {
      // This has the same discrete log, i_blind, as i_blind_u
      dlog: i_blind_u_claim.dlog.clone(),
      divisor: i_blind_v_divisor,
      point: (i_blind_V[0], i_blind_V[1]),
    };

    // For c_blind, we use the padding for C
    let (c_blind_claim, C) = append_claimed_point_1(&mut c1_tape);

    // We now have committed to O, I, C, and all interpolated points

    // The first circuit's tape opens the blinds from the second curve
    let mut commitment_blind_claims_1 = vec![];
    for _ in 0 .. (c1_branches.len() - 1) {
      commitment_blind_claims_1
        .push(c1_tape.append_claimed_point::<C::C2Parameters>(None, None, None, None).0);
    }

    // The second circuit's tape opens the blinds from the first curve
    let mut commitment_blind_claims_2 = vec![];
    for _ in 0 .. c2_branches.len() {
      commitment_blind_claims_2
        .push(c2_tape.append_claimed_point::<C::C1Parameters>(None, None, None, None).0);
    }

    let mut transcript = VerifierTranscript::new(
      Self::transcript(tree, input, &self.root_blind_pok[.. 32]),
      &self.proof,
    );
    // TODO: Return an error here
    // TODO: `1 +`? Fuzz this for different layer lens
    let proof_1_vcs =
      transcript.read_commitments::<C::C1>(1 + c1_tape.commitments.len(), 0).unwrap();
    let proof_2_vcs = transcript.read_commitments::<C::C2>(c2_tape.commitments.len(), 0).unwrap();

    // Verify the root blind PoK
    {
      let claimed_root = if (layer_lens.len() % 2) == 1 {
        TreeRoot::<C::C1, C::C2>::C1(match c1_branches.last().unwrap()[0] {
          Variable::CG { commitment: i, index: _ } => params.curve_1_hash_init + proof_1_vcs.C()[i],
          _ => panic!("branch wasn't present in a vector commitment"),
        })
      } else {
        TreeRoot::<C::C1, C::C2>::C2(match c2_branches.last().unwrap()[0] {
          Variable::CG { commitment: i, index: _ } => params.curve_2_hash_init + proof_2_vcs.C()[i],
          _ => panic!("branch wasn't present in a vector commitment"),
        })
      };
      // TODO: Batch verify this
      // TODO: unwrap -> Result
      match (claimed_root, tree) {
        (TreeRoot::C1(claimed), TreeRoot::C1(actual)) => {
          let mut R = <<C::C1 as Ciphersuite>::G as GroupEncoding>::Repr::default();
          R.as_mut().copy_from_slice(&self.root_blind_pok[.. 32]);
          let R = <C::C1 as Ciphersuite>::G::from_bytes(&R).unwrap();

          let mut s = <<C::C1 as Ciphersuite>::F as PrimeField>::Repr::default();
          s.as_mut().copy_from_slice(&self.root_blind_pok[32 ..]);
          let s = <C::C1 as Ciphersuite>::F::from_repr(s).unwrap();

          let c: <C::C1 as Ciphersuite>::F = transcript.challenge();

          // R + cX == sH, where X is the difference in the roots
          // (which should only be the randomness, and H is the generator for the randomness)
          assert_eq!(R + (claimed - actual) * c, params.curve_1_generators.h() * s);
        }
        (TreeRoot::C2(claimed), TreeRoot::C2(actual)) => {
          let mut R = <<C::C2 as Ciphersuite>::G as GroupEncoding>::Repr::default();
          R.as_mut().copy_from_slice(&self.root_blind_pok[.. 32]);
          let R = <C::C2 as Ciphersuite>::G::from_bytes(&R).unwrap();

          let mut s = <<C::C2 as Ciphersuite>::F as PrimeField>::Repr::default();
          s.as_mut().copy_from_slice(&self.root_blind_pok[32 ..]);
          let s = <C::C2 as Ciphersuite>::F::from_repr(s).unwrap();

          let c: <C::C2 as Ciphersuite>::F = transcript.challenge();

          // R + cX == sH, where X is the difference in the roots
          // (which should only be the randomness, and H is the generator for the randomness)
          assert_eq!(R + ((claimed - actual) * c), params.curve_2_generators.h() * s);
        }
        _ => panic!("claimed root is on a distinct layer than tree root"),
      }
    };

    // Create the circuits
    let mut c1_circuit = Circuit::<C::C1>::verify();
    let mut c2_circuit = Circuit::<C::C2>::verify();

    // Perform the layers
    c1_circuit.first_layer(
      &mut transcript,
      &CurveSpec {
        a: <<C::OC as Ciphersuite>::G as DivisorCurve>::a(),
        b: <<C::OC as Ciphersuite>::G as DivisorCurve>::b(),
      },
      &params.T_table,
      &params.U_table,
      &params.V_table,
      &params.G_table,
      //
      input.O_tilde,
      o_blind_claim,
      (O[0], O[1]),
      //
      input.I_tilde,
      i_blind_u_claim,
      (I[0], I[1]),
      //
      input.R,
      i_blind_v_claim,
      i_blind_blind_claim,
      //
      input.C_tilde,
      c_blind_claim,
      (C[0], C[1]),
      //
      c1_branches[0]
        .chunks(3)
        .map(|chunk| {
          assert_eq!(chunk.len(), 3);
          chunk.to_vec()
        })
        .collect(),
    );

    let mut c1_dlog_challenge = None;
    if commitment_blind_claims_1.first().is_some() {
      c1_dlog_challenge = Some(c1_circuit.additional_layer_discrete_log_challenge(
        &mut transcript,
        &CurveSpec {
          a: <<C::C2 as Ciphersuite>::G as DivisorCurve>::a(),
          b: <<C::C2 as Ciphersuite>::G as DivisorCurve>::b(),
        },
        &params.H_2_table,
      ));
    }

    // - 1, as the leaves are the first branch
    assert_eq!(c1_branches.len() - 1, commitment_blind_claims_1.len());
    assert!(proof_2_vcs.C().len() > c1_branches.len());
    let commitment_iter = proof_2_vcs.C().iter().cloned();
    let branch_iter = c1_branches.into_iter().skip(1).zip(commitment_blind_claims_1);
    for (prior_commitment, (branch, prior_blind_opening)) in
      commitment_iter.into_iter().zip(branch_iter)
    {
      let (hash_x, hash_y, _) = c1_circuit.mul(None, None, None);
      c1_circuit.additional_layer(
        &CurveSpec {
          a: <<C::C2 as Ciphersuite>::G as DivisorCurve>::a(),
          b: <<C::C2 as Ciphersuite>::G as DivisorCurve>::b(),
        },
        c1_dlog_challenge.as_ref().unwrap(),
        // TODO: unwrap -> error, this can get hit by a malicious proof
        <C::C2 as Ciphersuite>::G::to_xy(params.curve_2_hash_init + prior_commitment).unwrap(),
        prior_blind_opening,
        (hash_x, hash_y),
        branch,
      );
    }

    let mut c2_dlog_challenge = None;
    if commitment_blind_claims_2.first().is_some() {
      c2_dlog_challenge = Some(c2_circuit.additional_layer_discrete_log_challenge(
        &mut transcript,
        &CurveSpec {
          a: <<C::C1 as Ciphersuite>::G as DivisorCurve>::a(),
          b: <<C::C1 as Ciphersuite>::G as DivisorCurve>::b(),
        },
        &params.H_1_table,
      ));
    }

    assert_eq!(c2_branches.len(), commitment_blind_claims_2.len());
    assert!(proof_1_vcs.C().len() > c2_branches.len());
    let commitment_iter = proof_1_vcs.C().iter().cloned();
    let branch_iter = c2_branches.into_iter().zip(commitment_blind_claims_2);
    for (prior_commitment, (branch, prior_blind_opening)) in
      commitment_iter.into_iter().zip(branch_iter)
    {
      let (hash_x, hash_y, _) = c2_circuit.mul(None, None, None);
      c2_circuit.additional_layer(
        &CurveSpec {
          a: <<C::C1 as Ciphersuite>::G as DivisorCurve>::a(),
          b: <<C::C1 as Ciphersuite>::G as DivisorCurve>::b(),
        },
        c2_dlog_challenge.as_ref().unwrap(),
        // TODO: unwrap -> error, this can get hit by a malicious proof
        <C::C1 as Ciphersuite>::G::to_xy(params.curve_1_hash_init + prior_commitment).unwrap(),
        prior_blind_opening,
        (hash_x, hash_y),
        branch,
      );
    }

    // Escape to the raw weights to form a GBP with
    assert!(c1_circuit.muls() <= 256);
    assert!(c2_circuit.muls() <= 128);
    // dbg!(c1_circuit.muls());
    // dbg!(c2_circuit.muls());

    // TODO: unwrap -> Result
    let (c1_statement, _witness) =
      c1_circuit.statement(params.curve_1_generators.reduce(256).unwrap(), proof_1_vcs).unwrap();
    c1_statement.verify(rng, verifier_1, &mut transcript).unwrap();

    let (c2_statement, _witness) =
      c2_circuit.statement(params.curve_2_generators.reduce(128).unwrap(), proof_2_vcs).unwrap();
    c2_statement.verify(rng, verifier_2, &mut transcript).unwrap();
  }
}
