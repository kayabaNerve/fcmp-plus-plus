#![allow(non_snake_case)]

use core::{marker::PhantomData, borrow::Borrow};

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

use ec_divisors::DivisorCurve;
use generalized_bulletproofs::{
  BatchVerifier, PedersenVectorCommitment,
  transcript::{Transcript as ProverTranscript, VerifierTranscript},
};

mod gadgets;
pub(crate) use gadgets::*;
mod circuit;
pub(crate) use circuit::*;
pub use circuit::FcmpCurves;

mod prover;
pub use prover::*;

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
    if bool::from(O.is_identity()) || bool::from(I.is_identity()) || bool::from(C.is_identity()) {
      None?
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
    inputs: &[impl Borrow<Input<<C::C1 as Ciphersuite>::F>>],
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

    // Transcript the input tuples
    res.update(u32::try_from(inputs.len()).unwrap().to_le_bytes());
    for input in inputs {
      let input = input.borrow();
      res.update(input.O_tilde.0.to_repr());
      res.update(input.O_tilde.1.to_repr());
      res.update(input.I_tilde.0.to_repr());
      res.update(input.I_tilde.1.to_repr());
      res.update(input.R.0.to_repr());
      res.update(input.R.1.to_repr());
      res.update(input.C_tilde.0.to_repr());
      res.update(input.C_tilde.1.to_repr());
    }

    // Transcript the nonce for the difference of the root and our output VC of the root
    res.update(root_blind_R);

    res.finalize().into()
  }

  /// Prove a FCMP.
  ///
  /// This function MAY panic upon an invalid witness.
  #[allow(clippy::too_many_arguments)]
  pub fn prove<R: RngCore + CryptoRng>(
    rng: &mut R,
    params: &FcmpParams<C>,
    tree: TreeRoot<C::C1, C::C2>,
    branches: BranchesWithBlinds<C>,
  ) -> Self
  where
    <C::C1 as Ciphersuite>::G: GroupEncoding<Repr = [u8; 32]>,
    <C::C2 as Ciphersuite>::G: GroupEncoding<Repr = [u8; 32]>,
    <C::C1 as Ciphersuite>::F: PrimeField<Repr = [u8; 32]>,
    <C::C2 as Ciphersuite>::F: PrimeField<Repr = [u8; 32]>,
  {
    // TODO: Pad to nearest power of 2
    let mut c1_tape = VectorCommitmentTape {
      commitment_len: branches.per_input.len() * 256,
      current_j_offset: 0,
      commitments: vec![],
    };
    let mut c2_tape = VectorCommitmentTape {
      commitment_len: branches.per_input.len() * 128,
      current_j_offset: 0,
      commitments: vec![],
    };

    // This transcripts each input's branches, then the root
    let transcripted_branches = branches.transcript_branches(&mut c1_tape, &mut c2_tape);
    let transcripted_inputs = branches.transcript_inputs(&mut c1_tape);
    let transcripted_blinds = branches.transcript_blinds(&mut c1_tape, &mut c2_tape);

    // The blinds we have are for each input's branches
    // We explicitly transcript each input's branches before transcripting anything else, so we
    // simply exhaust all blinds on the first commitments
    let mut pvc_blinds_1 = Zeroizing::new(Vec::with_capacity(c1_tape.commitments.len()));
    for blind in &branches.branches_1_blinds {
      pvc_blinds_1.push(-*blind.0.scalar.scalar());
    }
    let mut pvc_blinds_2 = Zeroizing::new(Vec::with_capacity(c2_tape.commitments.len()));
    for blind in &branches.branches_2_blinds {
      pvc_blinds_2.push(-*blind.0.scalar.scalar());
    }

    // Now that we've mapped the blinds to the relevant commitments, create random blinds for the
    // rest of the commitments
    while pvc_blinds_1.len() < c1_tape.commitments.len() {
      pvc_blinds_1.push(<C::C1 as Ciphersuite>::F::random(&mut *rng));
    }
    while pvc_blinds_2.len() < c2_tape.commitments.len() {
      pvc_blinds_2.push(<C::C2 as Ciphersuite>::F::random(&mut *rng));
    }

    // Actually commit
    let commitments_1 = c1_tape.commit(&params.curve_1_generators, &pvc_blinds_1);
    let commitments_2 = c2_tape.commit(&params.curve_2_generators, &pvc_blinds_2);

    // Decide the nonce which will be used for proving knowledge of the tree root blind
    let mut root_blind_r_C1 = None;
    let mut root_blind_r_C2 = None;
    let mut root_blind_C1 = None;
    let mut root_blind_C2 = None;
    let root_blind_R: [u8; 32];
    if matches!(tree, TreeRoot::C1(_)) {
      root_blind_C1 = Some(pvc_blinds_1[branches.branches_1_blinds.len()]);
      let root_blind_r = Zeroizing::new(<C::C1 as Ciphersuite>::F::random(&mut *rng));
      root_blind_R = (params.curve_1_generators.h() * *root_blind_r).to_bytes();
      root_blind_r_C1 = Some(root_blind_r);
    } else {
      root_blind_C2 = Some(pvc_blinds_2[branches.branches_2_blinds.len()]);
      let root_blind_r = Zeroizing::new(<C::C2 as Ciphersuite>::F::random(&mut *rng));
      root_blind_R = (params.curve_2_generators.h() * *root_blind_r).to_bytes();
      root_blind_r_C2 = Some(root_blind_r);
    }

    let mut transcript = ProverTranscript::new(Self::transcript(
      tree,
      &branches.per_input.iter().map(|input| &input.input).collect::<Vec<_>>(),
      &root_blind_R,
    ));
    let commitments_1 = transcript.write_commitments(commitments_1, vec![]);
    let commitments_2 = transcript.write_commitments(commitments_2, vec![]);

    let mut root_blind_pok = [0; 64];
    if matches!(tree, TreeRoot::C1(_)) {
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
        .zip(pvc_blinds_1.iter())
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
        .zip(pvc_blinds_2.iter())
        .map(|((g_values, h_values), mask)| PedersenVectorCommitment {
          g_values: g_values.into(),
          h_values: h_values.into(),
          mask: *mask,
        })
        .collect(),
    );

    let mut c1_dlog_challenge = None;
    let mut c2_dlog_challenge = None;

    let TranscriptedBlinds { c1: transcripted_blinds_c1, c2: transcripted_blinds_c2 } =
      transcripted_blinds;
    let mut transcripted_blinds_c1 = transcripted_blinds_c1.into_iter();
    let mut transcripted_blinds_c2 = transcripted_blinds_c2.into_iter();

    // Perform the layers
    for (i, (input, transcripted_input)) in
      branches.per_input.iter().zip(transcripted_inputs).enumerate()
    {
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
        input.input.O_tilde,
        transcripted_input.o_blind_claim,
        transcripted_input.O,
        //
        input.input.I_tilde,
        transcripted_input.i_blind_u_claim,
        transcripted_input.I,
        //
        input.input.R,
        transcripted_input.i_blind_v_claim,
        transcripted_input.i_blind_blind_claim,
        //
        input.input.C_tilde,
        transcripted_input.c_blind_claim,
        transcripted_input.C,
        //
        (match branches.root {
          RootBranch::Leaves(_) => &transcripted_branches.root,
          _ => &transcripted_branches.per_input[i].c1[0],
        })
        .chunks(3)
        .map(|chunk| {
          assert_eq!(chunk.len(), 3);
          chunk.to_vec()
        })
        .collect(),
      );

      let commitment_iter = commitments_2.C().iter().cloned().zip(pvc_blinds_2.iter().cloned());
      let mut c1_branches = transcripted_branches.per_input[i].c1[1 ..].to_vec();
      if matches!(&branches.root, RootBranch::C1(_)) {
        c1_branches.push(transcripted_branches.root.clone());
      }
      let branch_iter = c1_branches.into_iter();
      // The following two to_xy calls have negligible probability of failing as they'd require
      // randomly selected blinds be the discrete logarithm of commitments, or one of our own
      // commitments be identity
      for ((mut prior_commitment, prior_blind), branch) in
        commitment_iter.into_iter().zip(branch_iter)
      {
        if c1_dlog_challenge.is_none() {
          c1_dlog_challenge = Some(c1_circuit.additional_layer_discrete_log_challenge(
            &mut transcript,
            &CurveSpec {
              a: <<C::C2 as Ciphersuite>::G as DivisorCurve>::a(),
              b: <<C::C2 as Ciphersuite>::G as DivisorCurve>::b(),
            },
            &params.H_2_table,
          ));
        }

        let prior_blind_opening = transcripted_blinds_c1.next().unwrap();
        prior_commitment += params.curve_2_hash_init;
        let unblinded_hash = prior_commitment - (params.curve_2_generators.h() * prior_blind);
        let (hash_x, hash_y, _) = c1_circuit.mul(
          None,
          None,
          Some(<C::C2 as Ciphersuite>::G::to_xy(unblinded_hash).unwrap()),
        );
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

      let commitment_iter = commitments_1.C().iter().cloned().zip(pvc_blinds_1.iter().cloned());
      let mut c2_branches = transcripted_branches.per_input[i].c2.clone();
      if matches!(&branches.root, RootBranch::C2(_)) {
        c2_branches.push(transcripted_branches.root.clone());
      }
      let branch_iter = c2_branches.into_iter();
      for ((mut prior_commitment, prior_blind), branch) in
        commitment_iter.into_iter().zip(branch_iter)
      {
        if c2_dlog_challenge.is_none() {
          c2_dlog_challenge = Some(c2_circuit.additional_layer_discrete_log_challenge(
            &mut transcript,
            &CurveSpec {
              a: <<C::C1 as Ciphersuite>::G as DivisorCurve>::a(),
              b: <<C::C1 as Ciphersuite>::G as DivisorCurve>::b(),
            },
            &params.H_1_table,
          ));
        }

        let prior_blind_opening = transcripted_blinds_c2.next().unwrap();
        prior_commitment += params.curve_1_hash_init;
        let unblinded_hash = prior_commitment - (params.curve_1_generators.h() * prior_blind);
        // unwrap should be safe as no hash we built should be identity
        let (hash_x, hash_y, _) = c2_circuit.mul(
          None,
          None,
          Some(<C::C1 as Ciphersuite>::G::to_xy(unblinded_hash).unwrap()),
        );
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
    }
    debug_assert!(transcripted_blinds_c1.next().is_none());
    debug_assert!(transcripted_blinds_c2.next().is_none());

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
    let mut c1_tape =
      VectorCommitmentTape { commitment_len: 256, current_j_offset: 0, commitments: vec![] };
    let mut c1_branches = Vec::with_capacity((layer_lens.len() / 2) + (layer_lens.len() % 2));
    let mut c2_tape =
      VectorCommitmentTape { commitment_len: 128, current_j_offset: 0, commitments: vec![] };
    let mut c2_branches = Vec::with_capacity(layer_lens.len() / 2);

    // Append the leaves and the branches to the tape
    for (i, layer_len) in layer_lens.iter().enumerate() {
      if (i % 2) == 0 {
        let branch = c1_tape.append_branch::<C::C1>(*layer_len, None);
        c1_branches.push(branch);
      } else {
        let branch = c2_tape.append_branch::<C::C2>(*layer_len, None);
        c2_branches.push(branch);
      }
    }

    // Accumulate the (partial) opening for the input tuple
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
      Self::transcript(tree, &[input], &self.root_blind_pok[.. 32]),
      &self.proof,
    );
    // TODO: Return an error here
    let proof_1_vcs = transcript.read_commitments::<C::C1>(c1_tape.commitments.len(), 0).unwrap();
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
    if !commitment_blind_claims_1.is_empty() {
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
    if !commitment_blind_claims_2.is_empty() {
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
