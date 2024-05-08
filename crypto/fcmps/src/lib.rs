#![allow(non_snake_case)]

use rand_core::{RngCore, CryptoRng};
use zeroize::Zeroize;

use transcript::Transcript;

use multiexp::multiexp;
use ciphersuite::{
  group::{
    ff::{Field, PrimeField, PrimeFieldBits},
    Group, GroupEncoding,
  },
  Ciphersuite,
};

use ec_divisors::{Poly, DivisorCurve, new_divisor};
use generalized_bulletproofs::{
  Generators, BatchVerifier, arithmetic_circuit_proof::ArithmeticCircuitProof,
};

mod lincomb;
pub(crate) use lincomb::*;
mod gadgets;
pub(crate) use gadgets::*;
mod circuit;
pub(crate) use circuit::*;

pub mod tree;

#[cfg(test)]
mod tests;

/// The variables used for Vector Commitments.
struct VectorCommitmentTape<F: Zeroize + PrimeFieldBits> {
  commitment_len: usize,
  current_j_offset: usize,
  commitments: Vec<(Vec<F>, Vec<F>)>,
}
impl<F: Zeroize + PrimeFieldBits> VectorCommitmentTape<F> {
  /// Append a series of variables to the vector commitment tape.
  fn append(&mut self, variables: Option<Vec<F>>) -> Vec<Variable> {
    // Any chunk of variables should be 256 long.
    if let Some(variables) = &variables {
      assert_eq!(variables.len(), 256);
    }

    #[allow(clippy::unwrap_or_default)]
    let variables = variables
      .map(|mut variables| {
        let h_bold = variables.split_off(128);
        let g_bold = variables;
        (g_bold, h_bold)
      })
      .unwrap_or((vec![], vec![]));

    if self.current_j_offset == 0 {
      self.commitments.push(variables);
    } else {
      let commitment = self.commitments.last_mut().unwrap();
      commitment.0.extend(variables.0);
      commitment.1.extend(variables.1);
    };
    let i = self.commitments.len() - 1;
    let j_range = self.current_j_offset .. (self.current_j_offset + 128);
    let left = j_range.clone().map(|j| Variable::CL(i, j));
    let right = j_range.map(|j| Variable::CR(i, j));
    let res = left.chain(right).collect();

    self.current_j_offset += 128;
    if self.current_j_offset == self.commitment_len {
      self.current_j_offset = 0;
    }
    res
  }

  // This must be called before all other appends
  fn append_branch<C: Ciphersuite>(
    &mut self,
    branch_len: usize,
    branch: Option<Vec<F>>,
  ) -> Vec<Variable>
  where
    C::G: DivisorCurve<Scalar = F>,
  {
    let empty = branch.as_ref().map(|_| vec![F::ZERO; 256]);
    let branch = branch.map(|mut branch| {
      assert_eq!(branch_len, branch.len());
      assert!(branch.len() <= 256);

      // Pad the branch
      while branch.len() < 256 {
        branch.push(F::ZERO);
      }
      branch
    });

    let mut branch = self.append(branch);
    // Append an empty dummy so this hash doesn't have more variables added
    if self.commitment_len == 256 {
      self.append(empty);
    }
    branch.truncate(branch_len);
    branch
  }

  /// Append a discrete logarithm of up to 255 bits, allowing usage of the extra slot for an
  /// arbitrary variable.
  ///
  /// If the discrete logarithm is less than 255 bits, additional extra elements may be provided
  /// (`padding`), yet these are only accessible on certain curves. This function panics if more
  /// elements are provided in `padding` than free spaces remaining.
  fn append_dlog(
    &mut self,
    dlog_bits: usize,
    dlog: Option<Vec<bool>>,
    padding: Option<Vec<F>>,
    extra: Option<F>,
  ) -> (Vec<Variable>, Vec<Variable>, Variable) {
    assert!(dlog_bits <= 255);

    let witness = dlog.map(|dlog| {
      let mut bit_witness = vec![];
      assert_eq!(dlog.len(), dlog_bits);
      for i in 0 .. dlog_bits {
        bit_witness.push(if *dlog.get(i).unwrap_or(&false) { F::ONE } else { F::ZERO });
      }
      let mut witness = bit_witness;

      let padding = padding.unwrap();
      assert!(padding.len() <= (255 - dlog_bits));
      for i in 0 .. (255 - dlog_bits) {
        witness.push(*padding.get(i).unwrap_or(&F::ZERO));
      }
      assert_eq!(witness.len(), 255);

      // Since we have an extra slot, push an extra item
      witness.push(extra.unwrap());
      witness
    });

    let mut variables = self.append(witness);
    let extra = variables.pop().unwrap();
    let padding = variables.drain(dlog_bits .. 255).collect::<Vec<_>>();
    (variables, padding, extra)
  }

  fn append_divisor(&mut self, divisor: Option<Poly<F>>, extra: Option<F>) -> (Divisor, Variable) {
    let witness = divisor.map(|divisor| {
      // Divisor y
      // This takes 1 slot
      let mut divisor_witness = vec![];
      divisor_witness.push(*divisor.y_coefficients.first().unwrap_or(&F::ZERO));

      // Divisor yx
      // We allocate 126 slots for this
      let empty_vec = vec![];
      let yx = divisor.yx_coefficients.first().unwrap_or(&empty_vec);
      assert!(yx.len() <= 126);
      for i in 0 .. 126 {
        divisor_witness.push(*yx.get(i).unwrap_or(&F::ZERO));
      }

      // Divisor x
      assert!(divisor.x_coefficients.len() <= 128);
      assert_eq!(divisor.x_coefficients[0], F::ONE);
      // Transcript from 1 given we expect a normalization of the first coefficient
      // We allocate 127 slots for this
      for i in 1 .. 128 {
        divisor_witness.push(*divisor.x_coefficients.get(i).unwrap_or(&F::ZERO));
      }

      // Divisor 0
      // This takes 1 slot
      divisor_witness.push(divisor.zero_coefficient);

      assert_eq!(divisor_witness.len(), 255);

      // Since we have an extra slot, push an extra item
      let mut witness = divisor_witness;
      witness.push(extra.unwrap());
      witness
    });

    let mut variables = self.append(witness);
    let extra = variables.pop().unwrap();

    let divisor = Divisor {
      y: variables[0],
      yx: variables[1 .. (1 + 126)].to_vec(),
      x_from_power_of_2: variables[(1 + 126) .. (1 + 126 + 127)].to_vec(),
      zero: variables[254],
    };

    (divisor, extra)
  }

  fn append_claimed_point(
    &mut self,
    dlog_bits: usize,
    dlog: Option<Vec<bool>>,
    divisor: Option<Poly<F>>,
    point: Option<(F, F)>,
    padding: Option<Vec<F>>,
  ) -> (ClaimedPointWithDlog, Vec<Variable>) {
    // Append the x coordinate with the discrete logarithm
    let (dlog, padding, x) = self.append_dlog(dlog_bits, dlog, padding, point.map(|point| point.0));
    // Append the y coordinate with the divisor
    let (divisor, y) = self.append_divisor(divisor, point.map(|point| point.1));

    (ClaimedPointWithDlog { divisor, dlog, point: (x, y) }, padding)
  }

  fn commit<T: Transcript, C: Ciphersuite<F = F>>(
    &self,
    generators: &Generators<T, C>,
    blinds: &[C::F],
  ) -> Vec<C::G> {
    assert_eq!(self.commitments.len(), blinds.len());

    let mut res = vec![];
    for (values, blind) in self.commitments.iter().zip(blinds) {
      let g_generators = generators.g_bold_slice()[.. values.0.len()].iter().cloned();
      let h_generators = generators.h_bold_slice()[.. values.1.len()].iter().cloned();
      let mut commitment = g_generators
        .enumerate()
        .map(|(i, g)| (values.0[i], g))
        .chain(h_generators.enumerate().map(|(i, h)| (values.1[i], h)))
        .collect::<Vec<_>>();
      commitment.push((*blind, generators.h()));
      res.push(multiexp(&commitment));
    }
    res
  }
}

/// The blinds used with an output.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct OutputBlinds<F: PrimeFieldBits> {
  o_blind: F,
  i_blind: F,
  i_blind_blind: F,
  c_blind: F,
}

/// A blind, prepared for usage within the circuit.
#[derive(Clone, PartialEq, Eq, Debug)]
struct PreparedBlind<F: PrimeFieldBits> {
  bits: Vec<bool>,
  divisor: Poly<F>,
  x: F,
  y: F,
}

impl<F: PrimeFieldBits> PreparedBlind<F> {
  fn new<C1: Ciphersuite>(blinding_generator: C1::G, blind: C1::F) -> Self
  where
    C1::G: DivisorCurve<FieldElement = F>,
  {
    let mut bits = blind.to_le_bits().into_iter().collect::<Vec<_>>();
    bits.truncate(usize::try_from(C1::F::NUM_BITS).unwrap());

    let res_point = blinding_generator * blind;

    let divisor = {
      let mut gen_pow_2 = blinding_generator;
      let mut points = vec![];
      for bit in &bits {
        if *bit {
          points.push(gen_pow_2);
        }
        gen_pow_2 = gen_pow_2.double();
      }
      points.push(-res_point);
      new_divisor::<C1::G>(&points).unwrap().normalize_x_coefficient()
    };

    let (x, y) = C1::G::to_xy(res_point);
    Self { bits, divisor, x, y }
  }
}

/// A struct representing an output tuple.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Output<OC: Ciphersuite> {
  O: OC::G,
  I: OC::G,
  C: OC::G,
}

/// A struct representing an input tuple.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Input<F: Field> {
  O_tilde: (F, F),
  I_tilde: (F, F),
  R: (F, F),
  C_tilde: (F, F),
}

/// The blinds used for an output, prepared for usage within the circuit.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PreparedBlinds<F: PrimeFieldBits> {
  o_blind: PreparedBlind<F>,
  i_blind_u: PreparedBlind<F>,
  i_blind_v: PreparedBlind<F>,
  i_blind_blind: PreparedBlind<F>,
  c_blind: PreparedBlind<F>,
  pub(crate) input: Input<F>,
}

impl<F: PrimeFieldBits> OutputBlinds<F> {
  pub fn new<R: RngCore + CryptoRng>(rng: &mut R) -> Self {
    let o_blind = F::random(&mut *rng);
    let i_blind = F::random(&mut *rng);
    let i_blind_blind = F::random(&mut *rng);
    let c_blind = F::random(&mut *rng);

    OutputBlinds { o_blind, i_blind, i_blind_blind, c_blind }
  }

  pub fn prepare<C: Ciphersuite<F = F>>(
    &self,
    G: C::G,
    T: C::G,
    U: C::G,
    V: C::G,
    output: Output<C>,
  ) -> PreparedBlinds<<C::G as DivisorCurve>::FieldElement>
  where
    C::G: DivisorCurve,
    <C::G as DivisorCurve>::FieldElement: PrimeFieldBits,
  {
    let O_tilde = output.O + (T * self.o_blind);
    let I_tilde = output.I + (U * self.i_blind);
    let R = (V * self.i_blind) + (T * self.i_blind_blind);
    let C_tilde = output.C + (G * self.c_blind);

    PreparedBlinds {
      // o_blind, i_blind, c_blind are used in-circuit as negative
      o_blind: PreparedBlind::new::<C>(T, -self.o_blind),
      i_blind_u: PreparedBlind::new::<C>(U, -self.i_blind),
      i_blind_v: PreparedBlind::new::<C>(V, -self.i_blind),
      i_blind_blind: PreparedBlind::new::<C>(T, self.i_blind_blind),
      c_blind: PreparedBlind::new::<C>(G, -self.c_blind),
      input: Input {
        O_tilde: C::G::to_xy(O_tilde),
        I_tilde: C::G::to_xy(I_tilde),
        R: C::G::to_xy(R),
        C_tilde: C::G::to_xy(C_tilde),
      },
    }
  }
}

/// A tree root, represented as a point from either curve.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TreeRoot<C1: Ciphersuite, C2: Ciphersuite> {
  C1(C1::G),
  C2(C2::G),
}

/// The parameters for full-chain membership proofs.
#[derive(Clone, Debug)]
pub struct FcmpParams<T: 'static + Transcript, C1: Ciphersuite, C2: Ciphersuite> {
  /// Generators for the first curve.
  curve_1_generators: Generators<T, C1>,
  /// Generators for the second curve.
  curve_2_generators: Generators<T, C2>,

  /// Initialization point for the hash function over the first curve.
  curve_1_hash_init: C1::G,
  /// Initialization point for the hash function over the first curve.
  curve_2_hash_init: C2::G,

  G_table: Vec<(C1::F, C1::F)>,
  T_table: Vec<(C1::F, C1::F)>,
  U_table: Vec<(C1::F, C1::F)>,
  V_table: Vec<(C1::F, C1::F)>,
  H_1_table: Vec<(C2::F, C2::F)>,
  H_2_table: Vec<(C1::F, C1::F)>,
}

impl<T: 'static + Transcript, C1: Ciphersuite, C2: Ciphersuite> FcmpParams<T, C1, C2>
where
  C1::G: DivisorCurve<FieldElement = C2::F>,
  C2::G: DivisorCurve<FieldElement = C1::F>,
{
  #[allow(clippy::too_many_arguments)]
  pub fn new<OC: Ciphersuite>(
    curve_1_generators: Generators<T, C1>,
    curve_2_generators: Generators<T, C2>,
    curve_1_hash_init: C1::G,
    curve_2_hash_init: C2::G,
    G: OC::G,
    T: OC::G,
    U: OC::G,
    V: OC::G,
  ) -> Self
  where
    OC::G: DivisorCurve<FieldElement = C1::F>,
  {
    fn table<C: DivisorCurve>(mut generator: C) -> Vec<(C::FieldElement, C::FieldElement)> {
      let mut table = vec![C::to_xy(generator)];
      for _ in 1 .. C::Scalar::NUM_BITS {
        generator = generator.double();
        table.push(C::to_xy(generator));
      }
      table
    }

    let G_table = table(G);
    let T_table = table(T);
    let U_table = table(U);
    let V_table = table(V);
    let H_1_table = table(curve_1_generators.h());
    let H_2_table = table(curve_2_generators.h());

    Self {
      curve_1_generators,
      curve_2_generators,
      curve_1_hash_init,
      curve_2_hash_init,
      G_table,
      T_table,
      U_table,
      V_table,
      H_1_table,
      H_2_table,
    }
  }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Branches<
  OC: Ciphersuite,
  C1: Ciphersuite<F = <OC::G as DivisorCurve>::FieldElement>,
  C2: Ciphersuite,
> where
  OC::G: DivisorCurve,
{
  leaves: Vec<Output<OC>>,
  curve_2_layers: Vec<Vec<C2::F>>,
  curve_1_layers: Vec<Vec<C1::F>>,
}

/// The full-chain membership proof.
#[derive(Clone)]
pub struct Fcmp<C1: Ciphersuite, C2: Ciphersuite> {
  proof_1: ArithmeticCircuitProof<C1>,
  proof_1_vcs: Vec<C1::G>,
  proof_2: ArithmeticCircuitProof<C2>,
  proof_2_vcs: Vec<C2::G>,
}
impl<C1: Ciphersuite, C2: Ciphersuite> Fcmp<C1, C2>
where
  C1::G: DivisorCurve<FieldElement = C2::F>,
  C2::G: DivisorCurve<FieldElement = C1::F>,
{
  fn transcript<T: Transcript>(
    transcript: &mut T,
    tree: TreeRoot<C1, C2>,
    input: Input<C1::F>,
    commitments_1: &[C1::G],
    commitments_2: &[C2::G],
  ) {
    // Transcript the tree root
    match tree {
      TreeRoot::C1(p) => transcript.append_message(b"root_1", p.to_bytes()),
      TreeRoot::C2(p) => transcript.append_message(b"root_2", p.to_bytes()),
    }
    // Transcript the input tuple
    transcript.append_message(b"O_tilde_x", input.O_tilde.0.to_repr());
    transcript.append_message(b"O_tilde_y", input.O_tilde.1.to_repr());
    transcript.append_message(b"I_tilde_x", input.I_tilde.0.to_repr());
    transcript.append_message(b"I_tilde_y", input.I_tilde.1.to_repr());
    transcript.append_message(b"R_x", input.R.0.to_repr());
    transcript.append_message(b"R_y", input.R.1.to_repr());
    transcript.append_message(b"C_tilde_x", input.C_tilde.0.to_repr());
    transcript.append_message(b"C_tilde_y", input.C_tilde.1.to_repr());

    for commitment in commitments_1 {
      transcript.append_message(b"c1_commitment", commitment.to_bytes());
    }

    for commitment in commitments_2 {
      transcript.append_message(b"c2_commitment", commitment.to_bytes());
    }
  }

  pub fn prove<R: RngCore + CryptoRng, T: Transcript, OC: Ciphersuite>(
    rng: &mut R,
    transcript: &mut T,
    params: &FcmpParams<T, C1, C2>,
    tree: TreeRoot<C1, C2>,
    output: Output<OC>,
    output_blinds: PreparedBlinds<C1::F>,
    branches: Branches<OC, C1, C2>,
  ) -> Self
  where
    OC::G: DivisorCurve<FieldElement = C1::F>,
  {
    // Flatten the leaves for the branch
    let mut flattened_leaves = vec![];
    for leaf in branches.leaves {
      flattened_leaves.extend(&[
        OC::G::to_xy(leaf.O).0,
        OC::G::to_xy(leaf.I).0,
        OC::G::to_xy(leaf.C).0,
      ]);
    }

    // Append the leaves and the rest of the branches to the tape
    let mut c1_tape =
      VectorCommitmentTape { commitment_len: 256, current_j_offset: 0, commitments: vec![] };
    let mut c1_branches = vec![];
    {
      let branch = c1_tape.append_branch::<C1>(flattened_leaves.len(), Some(flattened_leaves));
      c1_branches.push(branch);
    }
    for branch in branches.curve_1_layers {
      let branch = c1_tape.append_branch::<C1>(branch.len(), Some(branch));
      c1_branches.push(branch);
    }

    let mut c2_tape =
      VectorCommitmentTape { commitment_len: 128, current_j_offset: 0, commitments: vec![] };
    let mut c2_branches = vec![];
    for branch in branches.curve_2_layers {
      let branch = c2_tape.append_branch::<C2>(branch.len(), Some(branch));
      c2_branches.push(branch);
    }

    // Decide blinds for each branch
    let mut branches_1_blinds = vec![];
    let mut branches_1_blinds_prepared = vec![];
    for _ in 0 .. c1_branches.len() {
      let blind = C1::F::random(&mut *rng);
      branches_1_blinds.push(blind);
      branches_1_blinds_prepared
        .push(PreparedBlind::<_>::new::<C1>(params.curve_1_generators.h(), -blind));
    }

    let mut branches_2_blinds = vec![];
    let mut branches_2_blinds_prepared = vec![];
    for _ in 0 .. c2_branches.len() {
      let blind = C2::F::random(&mut *rng);
      branches_2_blinds.push(blind);
      branches_2_blinds_prepared
        .push(PreparedBlind::<_>::new::<C2>(params.curve_2_generators.h(), -blind));
    }

    // Accumulate the opening for the leaves
    let append_claimed_point_1 = |c1_tape: &mut VectorCommitmentTape<C1::F>,
                                  dlog_bits,
                                  blind: PreparedBlind<C1::F>,
                                  padding| {
      c1_tape.append_claimed_point(
        dlog_bits,
        Some(blind.bits),
        Some(blind.divisor),
        Some((blind.x, blind.y)),
        Some(padding),
      )
    };

    // Since this is presumed over Ed25519, which has a 253-bit discrete logarithm, we have two
    // items avilable in padding. We use this padding for all the other points we must commit to
    // For o_blind, we use the padding for O
    let (o_blind_claim, O) = {
      let (x, y) = OC::G::to_xy(output.O);

      append_claimed_point_1(
        &mut c1_tape,
        usize::try_from(OC::F::NUM_BITS).unwrap(),
        output_blinds.o_blind.clone(),
        vec![x, y],
      )
    };
    // For i_blind_u, we use the padding for I
    let (i_blind_u_claim, I) = {
      let (x, y) = OC::G::to_xy(output.I);
      append_claimed_point_1(
        &mut c1_tape,
        usize::try_from(OC::F::NUM_BITS).unwrap(),
        output_blinds.i_blind_u,
        vec![x, y],
      )
    };

    // Commit to the divisor for `i_blind V`, which doesn't commit to the point `i_blind V`
    // (annd that still has to be done)
    let (i_blind_v_divisor, _extra) =
      c1_tape.append_divisor(Some(output_blinds.i_blind_v.divisor), Some(C1::F::ZERO));

    // For i_blind_blind, we use the padding for (i_blind V)
    let (i_blind_blind_claim, i_blind_V) = {
      let (x, y) = (output_blinds.i_blind_v.x, output_blinds.i_blind_v.y);
      append_claimed_point_1(
        &mut c1_tape,
        usize::try_from(OC::F::NUM_BITS).unwrap(),
        output_blinds.i_blind_blind,
        vec![x, y],
      )
    };

    let i_blind_v_claim = ClaimedPointWithDlog {
      // This has the same discrete log, i_blind, as i_blind_u
      dlog: i_blind_u_claim.dlog.clone(),
      divisor: i_blind_v_divisor,
      point: (i_blind_V[0], i_blind_V[1]),
    };

    // For c_blind, we use the padding for C
    let (c_blind_claim, C) = {
      let (x, y) = OC::G::to_xy(output.C);
      append_claimed_point_1(
        &mut c1_tape,
        usize::try_from(OC::F::NUM_BITS).unwrap(),
        output_blinds.c_blind,
        vec![x, y],
      )
    };

    // We now have committed to O, I, C, and all interpolated points

    // The first circuit's tape opens the blinds from the second curve
    let mut commitment_blind_claims_1 = vec![];
    for blind in branches_2_blinds_prepared {
      commitment_blind_claims_1.push(
        c1_tape
          .append_claimed_point(
            usize::try_from(C2::F::NUM_BITS).unwrap(),
            Some(blind.bits),
            Some(blind.divisor),
            Some((blind.x, blind.y)),
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
          .append_claimed_point(
            usize::try_from(C1::F::NUM_BITS).unwrap(),
            Some(blind.bits),
            Some(blind.divisor),
            Some((blind.x, blind.y)),
            Some(vec![]),
          )
          .0,
      );
    }

    // We have now committed to the discrete logs, the divisors, and the output points...
    // and the sets, and the set members used within the tuple set membership (as needed)

    // Calculate all of the PVCs and transcript them
    let mut pvc_blinds_1 = branches_1_blinds;
    while pvc_blinds_1.len() < c1_tape.commitments.len() {
      pvc_blinds_1.push(C1::F::random(&mut *rng));
    }
    let commitments_1 = c1_tape.commit(&params.curve_1_generators, &pvc_blinds_1);

    let mut pvc_blinds_2 = branches_2_blinds;
    while pvc_blinds_2.len() < c2_tape.commitments.len() {
      pvc_blinds_2.push(C2::F::random(&mut *rng));
    }
    let commitments_2 = c2_tape.commit(&params.curve_2_generators, &pvc_blinds_2);
    Self::transcript(transcript, tree, output_blinds.input, &commitments_1, &commitments_2);

    // Create the circuits
    let mut c1_circuit = Circuit::<C1>::prove(c1_tape.commitments);
    let mut c2_circuit = Circuit::<C2>::prove(c2_tape.commitments);

    // Perform the layers
    c1_circuit.first_layer(
      transcript,
      &CurveSpec { a: <OC::G as DivisorCurve>::a(), b: <OC::G as DivisorCurve>::b() },
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
    if let Some(blind) = commitment_blind_claims_1.first() {
      c1_dlog_challenge = Some(c1_circuit.additional_layer_discrete_log_challenge(
        transcript,
        &CurveSpec { a: <C2::G as DivisorCurve>::a(), b: <C2::G as DivisorCurve>::b() },
        1 + blind.divisor.x_from_power_of_2.len(),
        blind.divisor.yx.len(),
        &params.H_2_table,
      ));
    }

    assert_eq!(commitments_2.len(), pvc_blinds_2.len());
    // - 1, as the leaves are the first branch
    assert_eq!(c1_branches.len() - 1, commitment_blind_claims_1.len());
    assert!(commitments_2.len() > c1_branches.len());
    let commitment_iter = commitments_2.clone().into_iter().zip(pvc_blinds_2.clone());
    let branch_iter = c1_branches.into_iter().skip(1).zip(commitment_blind_claims_1);
    for ((mut prior_commitment, prior_blind), (branch, prior_blind_opening)) in
      commitment_iter.into_iter().zip(branch_iter)
    {
      prior_commitment += params.curve_2_hash_init;
      let unblinded_hash = prior_commitment - (params.curve_2_generators.h() * prior_blind);
      let (hash_x, hash_y, _) = c1_circuit.mul(None, None, Some(C2::G::to_xy(unblinded_hash)));
      c1_circuit.additional_layer(
        &CurveSpec { a: <C2::G as DivisorCurve>::a(), b: <C2::G as DivisorCurve>::b() },
        c1_dlog_challenge.as_ref().unwrap(),
        C2::G::to_xy(prior_commitment),
        prior_blind_opening,
        (hash_x, hash_y),
        branch,
      );
    }

    let mut c2_dlog_challenge = None;
    if let Some(blind) = commitment_blind_claims_2.first() {
      c2_dlog_challenge = Some(c2_circuit.additional_layer_discrete_log_challenge(
        transcript,
        &CurveSpec { a: <C1::G as DivisorCurve>::a(), b: <C1::G as DivisorCurve>::b() },
        1 + blind.divisor.x_from_power_of_2.len(),
        blind.divisor.yx.len(),
        &params.H_1_table,
      ));
    }

    assert_eq!(commitments_1.len(), pvc_blinds_1.len());
    assert_eq!(c2_branches.len(), commitment_blind_claims_2.len());
    assert!(commitments_1.len() > c2_branches.len());
    let commitment_iter = commitments_1.clone().into_iter().zip(pvc_blinds_1.clone());
    let branch_iter = c2_branches.into_iter().zip(commitment_blind_claims_2);
    for ((mut prior_commitment, prior_blind), (branch, prior_blind_opening)) in
      commitment_iter.into_iter().zip(branch_iter)
    {
      prior_commitment += params.curve_1_hash_init;
      let unblinded_hash = prior_commitment - (params.curve_1_generators.h() * prior_blind);
      let (hash_x, hash_y, _) = c2_circuit.mul(None, None, Some(C1::G::to_xy(unblinded_hash)));
      c2_circuit.additional_layer(
        &CurveSpec { a: <C1::G as DivisorCurve>::a(), b: <C1::G as DivisorCurve>::b() },
        c2_dlog_challenge.as_ref().unwrap(),
        C1::G::to_xy(prior_commitment),
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
    let (c1_statement, c1_witness) = c1_circuit
      .statement(
        params.curve_1_generators.reduce(256).unwrap(),
        commitments_1.clone(),
        pvc_blinds_1,
      )
      .unwrap();
    let c1_proof = c1_statement.clone().prove(rng, transcript, c1_witness.unwrap()).unwrap();

    let (c2_statement, c2_witness) = c2_circuit
      .statement(
        params.curve_2_generators.reduce(128).unwrap(),
        commitments_2.clone(),
        pvc_blinds_2,
      )
      .unwrap();
    let c2_proof = c2_statement.prove(rng, transcript, c2_witness.unwrap()).unwrap();

    Fcmp {
      proof_1: c1_proof,
      proof_2: c2_proof,
      proof_1_vcs: commitments_1,
      proof_2_vcs: commitments_2,
    }
  }

  #[allow(clippy::too_many_arguments)]
  pub fn verify<R: RngCore + CryptoRng, T: Transcript, OC: Ciphersuite>(
    self,
    rng: &mut R,
    transcript: &mut T,
    verifier_1: &mut BatchVerifier<C1>,
    verifier_2: &mut BatchVerifier<C2>,
    params: &FcmpParams<T, C1, C2>,
    tree: TreeRoot<C1, C2>,
    layer_lens: &[usize],
    input: Input<C1::F>,
  ) where
    OC::G: DivisorCurve<FieldElement = C1::F>,
  {
    // TODO: Check the length of the VCs for this proof

    // Append the leaves and the rest of the branches to the tape

    let mut c1_tape = VectorCommitmentTape {
      commitment_len: 256,
      current_j_offset: 0,
      commitments: Vec::with_capacity(self.proof_1_vcs.len()),
    };
    let mut c1_branches = Vec::with_capacity((layer_lens.len() / 2) + (layer_lens.len() % 2));
    let mut c2_tape = VectorCommitmentTape {
      commitment_len: 128,
      current_j_offset: 0,
      commitments: Vec::with_capacity(self.proof_2_vcs.len()),
    };
    let mut c2_branches = Vec::with_capacity(layer_lens.len() / 2);

    for (i, layer_len) in layer_lens.iter().enumerate() {
      if (i % 2) == 0 {
        let branch = c1_tape.append_branch::<C1>(*layer_len, None);
        c1_branches.push(branch);
      } else {
        let branch = c2_tape.append_branch::<C2>(*layer_len, None);
        c2_branches.push(branch);
      }
    }

    // Accumulate the opening for the leaves
    let append_claimed_point_1 = |c1_tape: &mut VectorCommitmentTape<C1::F>, dlog_bits| {
      c1_tape.append_claimed_point(dlog_bits, None, None, None, None)
    };

    // Since this is presumed over Ed25519, which has a 253-bit discrete logarithm, we have two
    // items avilable in padding. We use this padding for all the other points we must commit to
    // For o_blind, we use the padding for O
    let (o_blind_claim, O) =
      { append_claimed_point_1(&mut c1_tape, usize::try_from(OC::F::NUM_BITS).unwrap()) };
    // For i_blind_u, we use the padding for I
    let (i_blind_u_claim, I) =
      { append_claimed_point_1(&mut c1_tape, usize::try_from(OC::F::NUM_BITS).unwrap()) };

    // Commit to the divisor for `i_blind V`, which doesn't commit to the point `i_blind V`
    // (annd that still has to be done)
    let (i_blind_v_divisor, _extra) = c1_tape.append_divisor(None, None);

    // For i_blind_blind, we use the padding for (i_blind V)
    let (i_blind_blind_claim, i_blind_V) =
      { append_claimed_point_1(&mut c1_tape, usize::try_from(OC::F::NUM_BITS).unwrap()) };

    let i_blind_v_claim = ClaimedPointWithDlog {
      // This has the same discrete log, i_blind, as i_blind_u
      dlog: i_blind_u_claim.dlog.clone(),
      divisor: i_blind_v_divisor,
      point: (i_blind_V[0], i_blind_V[1]),
    };

    // For c_blind, we use the padding for C
    let (c_blind_claim, C) =
      { append_claimed_point_1(&mut c1_tape, usize::try_from(OC::F::NUM_BITS).unwrap()) };

    // We now have committed to O, I, C, and all interpolated points

    // The first circuit's tape opens the blinds from the second curve
    let mut commitment_blind_claims_1 = vec![];
    for _ in 0 .. (c1_branches.len() - 1) {
      commitment_blind_claims_1.push(
        c1_tape
          .append_claimed_point(usize::try_from(C2::F::NUM_BITS).unwrap(), None, None, None, None)
          .0,
      );
    }

    // The second circuit's tape opens the blinds from the first curve
    let mut commitment_blind_claims_2 = vec![];
    for _ in 0 .. c2_branches.len() {
      commitment_blind_claims_2.push(
        c2_tape
          .append_claimed_point(usize::try_from(C1::F::NUM_BITS).unwrap(), None, None, None, None)
          .0,
      );
    }

    Self::transcript(transcript, tree, input, &self.proof_1_vcs, &self.proof_2_vcs);

    // Create the circuits
    let mut c1_circuit = Circuit::<C1>::verify();
    let mut c2_circuit = Circuit::<C2>::verify();

    // Perform the layers
    c1_circuit.first_layer(
      transcript,
      &CurveSpec { a: <OC::G as DivisorCurve>::a(), b: <OC::G as DivisorCurve>::b() },
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
    if let Some(blind) = commitment_blind_claims_1.first() {
      c1_dlog_challenge = Some(c1_circuit.additional_layer_discrete_log_challenge(
        transcript,
        &CurveSpec { a: <C2::G as DivisorCurve>::a(), b: <C2::G as DivisorCurve>::b() },
        1 + blind.divisor.x_from_power_of_2.len(),
        blind.divisor.yx.len(),
        &params.H_2_table,
      ));
    }

    // - 1, as the leaves are the first branch
    assert_eq!(c1_branches.len() - 1, commitment_blind_claims_1.len());
    assert!(self.proof_2_vcs.len() > c1_branches.len());
    let commitment_iter = self.proof_2_vcs.clone().into_iter();
    let branch_iter = c1_branches.into_iter().skip(1).zip(commitment_blind_claims_1);
    for (prior_commitment, (branch, prior_blind_opening)) in
      commitment_iter.into_iter().zip(branch_iter)
    {
      let (hash_x, hash_y, _) = c1_circuit.mul(None, None, None);
      c1_circuit.additional_layer(
        &CurveSpec { a: <C2::G as DivisorCurve>::a(), b: <C2::G as DivisorCurve>::b() },
        c1_dlog_challenge.as_ref().unwrap(),
        C2::G::to_xy(params.curve_2_hash_init + prior_commitment),
        prior_blind_opening,
        (hash_x, hash_y),
        branch,
      );
    }

    let mut c2_dlog_challenge = None;
    if let Some(blind) = commitment_blind_claims_2.first() {
      c2_dlog_challenge = Some(c2_circuit.additional_layer_discrete_log_challenge(
        transcript,
        &CurveSpec { a: <C1::G as DivisorCurve>::a(), b: <C1::G as DivisorCurve>::b() },
        1 + blind.divisor.x_from_power_of_2.len(),
        blind.divisor.yx.len(),
        &params.H_1_table,
      ));
    }

    assert_eq!(c2_branches.len(), commitment_blind_claims_2.len());
    assert!(self.proof_1_vcs.len() > c2_branches.len());
    let commitment_iter = self.proof_1_vcs.clone().into_iter();
    let branch_iter = c2_branches.into_iter().zip(commitment_blind_claims_2);
    for (prior_commitment, (branch, prior_blind_opening)) in
      commitment_iter.into_iter().zip(branch_iter)
    {
      let (hash_x, hash_y, _) = c2_circuit.mul(None, None, None);
      c2_circuit.additional_layer(
        &CurveSpec { a: <C1::G as DivisorCurve>::a(), b: <C1::G as DivisorCurve>::b() },
        c2_dlog_challenge.as_ref().unwrap(),
        C1::G::to_xy(params.curve_1_hash_init + prior_commitment),
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
    let (c1_statement, _witness) = c1_circuit
      .statement(params.curve_1_generators.reduce(256).unwrap(), self.proof_1_vcs, vec![])
      .unwrap();
    c1_statement.verify(rng, verifier_1, transcript, self.proof_1).unwrap();

    let (c2_statement, _witness) = c2_circuit
      .statement(params.curve_2_generators.reduce(128).unwrap(), self.proof_2_vcs, vec![])
      .unwrap();
    c2_statement.verify(rng, verifier_2, transcript, self.proof_2).unwrap();

    // TODO: Check the final root matches
  }
}
