#![allow(non_snake_case)]

use core::marker::PhantomData;

use rand_core::{RngCore, CryptoRng};
use zeroize::{Zeroize, Zeroizing};

use generic_array::{typenum::Unsigned, GenericArray};

use blake2::{
  digest::{consts::U32, Digest},
  Blake2b,
};

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
  Generators, BatchVerifier, PedersenVectorCommitment,
  transcript::{Transcript as ProverTranscript, VerifierTranscript},
};

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
    let left = j_range.clone().map(|j| Variable::CG { commitment: i, index: j });
    let right = j_range.map(|j| Variable::CH { commitment: i, index: j });
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
  fn append_dlog<Parameters: DiscreteLogParameters>(
    &mut self,
    dlog: Option<Vec<bool>>,
    padding: Option<Vec<F>>,
    extra: Option<F>,
  ) -> (GenericArray<Variable, Parameters::ScalarBits>, Vec<Variable>, Variable) {
    assert!(Parameters::ScalarBits::USIZE <= 255);
    let dlog_bits = Parameters::ScalarBits::USIZE;

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
    let dlog = GenericArray::from_slice(&variables).clone();
    (dlog, padding, extra)
  }

  fn append_divisor<Parameters: DiscreteLogParameters>(
    &mut self,
    divisor: Option<Poly<F>>,
    extra: Option<F>,
  ) -> (Divisor<Parameters>, Variable) {
    let witness = divisor.map(|divisor| {
      // Divisor y
      // This takes 1 slot
      let mut divisor_witness = vec![];
      divisor_witness.push(*divisor.y_coefficients.first().unwrap_or(&F::ZERO));

      // Divisor yx
      let empty_vec = vec![];
      let yx = divisor.yx_coefficients.first().unwrap_or(&empty_vec);
      assert!(yx.len() <= Parameters::YxCoefficients::USIZE);
      for i in 0 .. Parameters::YxCoefficients::USIZE {
        divisor_witness.push(*yx.get(i).unwrap_or(&F::ZERO));
      }

      // Divisor x
      assert!(divisor.x_coefficients.len() <= Parameters::XCoefficients::USIZE);
      assert_eq!(divisor.x_coefficients[0], F::ONE);
      // Transcript from 1 given we expect a normalization of the first coefficient
      // We allocate 127 slots for this
      for i in 1 .. Parameters::XCoefficients::USIZE {
        divisor_witness.push(*divisor.x_coefficients.get(i).unwrap_or(&F::ZERO));
      }

      // Divisor 0
      // This takes 1 slot
      divisor_witness.push(divisor.zero_coefficient);

      assert!(divisor_witness.len() <= 255);
      while divisor_witness.len() < 255 {
        divisor_witness.push(F::ZERO);
      }

      // Since we have an extra slot, push an extra item
      let mut witness = divisor_witness;
      witness.push(extra.unwrap());
      witness
    });

    let mut variables = self.append(witness);
    let extra = variables.pop().unwrap();

    let mut cursor_start = 1;
    let mut cursor_end = cursor_start + Parameters::YxCoefficients::USIZE;
    let yx = GenericArray::from_slice(&variables[cursor_start .. cursor_end]).clone();
    cursor_start = cursor_end;
    cursor_end += Parameters::XCoefficientsMinusOne::USIZE;
    let x_from_power_of_2 =
      GenericArray::from_slice(&variables[cursor_start .. cursor_end]).clone();
    let divisor = Divisor { y: variables[0], yx, x_from_power_of_2, zero: variables[cursor_end] };

    (divisor, extra)
  }

  fn append_claimed_point<Parameters: DiscreteLogParameters>(
    &mut self,
    dlog: Option<Vec<bool>>,
    divisor: Option<Poly<F>>,
    point: Option<(F, F)>,
    padding: Option<Vec<F>>,
  ) -> (PointWithDlog<Parameters>, Vec<Variable>) {
    // Append the x coordinate with the discrete logarithm
    let (dlog, padding, x) =
      self.append_dlog::<Parameters>(dlog, padding, point.map(|point| point.0));
    // Append the y coordinate with the divisor
    let (divisor, y) = self.append_divisor(divisor, point.map(|point| point.1));

    (PointWithDlog { divisor, dlog, point: (x, y) }, padding)
  }

  fn commit<C: Ciphersuite<F = F>>(
    &self,
    generators: &Generators<C>,
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
  fn new<C1: Ciphersuite>(blinding_generator: C1::G, blind: C1::F) -> Option<Self>
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

    let (x, y) = C1::G::to_xy(res_point)?;
    Some(Self { bits, divisor, x, y })
  }
}

/// A struct representing an output tuple.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Output<OC: Ciphersuite> {
  O: OC::G,
  I: OC::G,
  C: OC::G,
}

impl<OC: Ciphersuite> Output<OC> {
  pub fn new(O: OC::G, I: OC::G, C: OC::G) -> Option<Self> {
    if bool::from(O.is_identity() | I.is_identity() | C.is_identity()) {
      None?;
    }
    Some(Output { O, I, C })
  }
}

/// A struct representing an input tuple.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
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
      // o_blind, i_blind, c_blind are used in-circuit as their negatives
      // These unwraps should be safe as select blinds on our end, uniformly from random
      o_blind: PreparedBlind::new::<C>(T, -self.o_blind).unwrap(),
      i_blind_u: PreparedBlind::new::<C>(U, -self.i_blind).unwrap(),
      i_blind_v: PreparedBlind::new::<C>(V, -self.i_blind).unwrap(),
      i_blind_blind: PreparedBlind::new::<C>(T, self.i_blind_blind).unwrap(),
      c_blind: PreparedBlind::new::<C>(G, -self.c_blind).unwrap(),
      // This unwrap should be safe as else it'd require we randomly selected inverses of discrete
      // logarithms of each other
      input: Input::new::<C::G>(O_tilde, I_tilde, R, C_tilde).unwrap(),
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
pub struct FcmpParams<C: FcmpCurves>
where
  <C::OC as Ciphersuite>::G: DivisorCurve<FieldElement = <C::C1 as Ciphersuite>::F>,
  <C::C1 as Ciphersuite>::G: DivisorCurve<FieldElement = <C::C2 as Ciphersuite>::F>,
  <C::C2 as Ciphersuite>::G: DivisorCurve<FieldElement = <C::C1 as Ciphersuite>::F>,
{
  /// Generators for the first curve.
  curve_1_generators: Generators<C::C1>,
  /// Generators for the second curve.
  curve_2_generators: Generators<C::C2>,

  /// Initialization point for the hash function over the first curve.
  curve_1_hash_init: <C::C1 as Ciphersuite>::G,
  /// Initialization point for the hash function over the first curve.
  curve_2_hash_init: <C::C2 as Ciphersuite>::G,

  G_table: GeneratorTable<<C::C1 as Ciphersuite>::F, C::OcParameters>,
  T_table: GeneratorTable<<C::C1 as Ciphersuite>::F, C::OcParameters>,
  U_table: GeneratorTable<<C::C1 as Ciphersuite>::F, C::OcParameters>,
  V_table: GeneratorTable<<C::C1 as Ciphersuite>::F, C::OcParameters>,
  H_1_table: GeneratorTable<<C::C2 as Ciphersuite>::F, C::C1Parameters>,
  H_2_table: GeneratorTable<<C::C1 as Ciphersuite>::F, C::C2Parameters>,
}

impl<C: FcmpCurves> FcmpParams<C>
where
  <C::OC as Ciphersuite>::G: DivisorCurve<FieldElement = <C::C1 as Ciphersuite>::F>,
  <C::C1 as Ciphersuite>::G: DivisorCurve<FieldElement = <C::C2 as Ciphersuite>::F>,
  <C::C2 as Ciphersuite>::G: DivisorCurve<FieldElement = <C::C1 as Ciphersuite>::F>,
{
  #[allow(clippy::too_many_arguments)]
  pub fn new(
    curve_1_generators: Generators<C::C1>,
    curve_2_generators: Generators<C::C2>,
    curve_1_hash_init: <C::C1 as Ciphersuite>::G,
    curve_2_hash_init: <C::C2 as Ciphersuite>::G,
    G: <<C as FcmpCurves>::OC as Ciphersuite>::G,
    T: <<C as FcmpCurves>::OC as Ciphersuite>::G,
    U: <<C as FcmpCurves>::OC as Ciphersuite>::G,
    V: <<C as FcmpCurves>::OC as Ciphersuite>::G,
  ) -> Self {
    let oc_curve_spec =
      CurveSpec { a: <<C::OC as Ciphersuite>::G>::a(), b: <<C::OC as Ciphersuite>::G>::b() };
    let (g_x, g_y) = <<C as FcmpCurves>::OC as Ciphersuite>::G::to_xy(G).unwrap();
    let G_table = GeneratorTable::new(&oc_curve_spec, g_x, g_y);
    let (t_x, t_y) = <<C as FcmpCurves>::OC as Ciphersuite>::G::to_xy(T).unwrap();
    let T_table = GeneratorTable::new(&oc_curve_spec, t_x, t_y);
    let (u_x, u_y) = <<C as FcmpCurves>::OC as Ciphersuite>::G::to_xy(U).unwrap();
    let U_table = GeneratorTable::new(&oc_curve_spec, u_x, u_y);
    let (v_x, v_y) = <<C as FcmpCurves>::OC as Ciphersuite>::G::to_xy(V).unwrap();
    let V_table = GeneratorTable::new(&oc_curve_spec, v_x, v_y);

    let c1_curve_spec =
      CurveSpec { a: <<C::C1 as Ciphersuite>::G>::a(), b: <<C::C1 as Ciphersuite>::G>::b() };
    let (h_1_x, h_1_y) =
      <<C as FcmpCurves>::C1 as Ciphersuite>::G::to_xy(curve_1_generators.h()).unwrap();
    let H_1_table = GeneratorTable::new(&c1_curve_spec, h_1_x, h_1_y);

    let c2_curve_spec =
      CurveSpec { a: <<C::C2 as Ciphersuite>::G>::a(), b: <<C::C2 as Ciphersuite>::G>::b() };
    let (h_2_x, h_2_y) =
      <<C as FcmpCurves>::C2 as Ciphersuite>::G::to_xy(curve_2_generators.h()).unwrap();
    let H_2_table = GeneratorTable::new(&c2_curve_spec, h_2_x, h_2_y);

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
pub struct Branches<C: FcmpCurves> {
  leaves: Vec<Output<C::OC>>,
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
    output: Output<C::OC>,
    output_blinds: PreparedBlinds<<C::C1 as Ciphersuite>::F>,
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
    let mut branches_1_blinds = vec![];
    let mut branches_1_blinds_prepared = vec![];
    for _ in 0 .. c1_branches.len() {
      let blind = <C::C1 as Ciphersuite>::F::random(&mut *rng);
      branches_1_blinds.push(blind);
      branches_1_blinds_prepared
        .push(PreparedBlind::<_>::new::<C::C1>(params.curve_1_generators.h(), -blind).unwrap());
    }

    let mut branches_2_blinds = vec![];
    let mut branches_2_blinds_prepared = vec![];
    for _ in 0 .. c2_branches.len() {
      let blind = <C::C2 as Ciphersuite>::F::random(&mut *rng);
      branches_2_blinds.push(blind);
      branches_2_blinds_prepared
        .push(PreparedBlind::<_>::new::<C::C2>(params.curve_2_generators.h(), -blind).unwrap());
    }

    // Accumulate the opening for the leaves
    let append_claimed_point_1 = |c1_tape: &mut VectorCommitmentTape<<C::C1 as Ciphersuite>::F>,
                                  blind: PreparedBlind<<C::C1 as Ciphersuite>::F>,
                                  padding| {
      c1_tape.append_claimed_point::<C::OcParameters>(
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
      let (x, y) = <C::OC as Ciphersuite>::G::to_xy(output.O).unwrap();

      append_claimed_point_1(&mut c1_tape, output_blinds.o_blind.clone(), vec![x, y])
    };
    // For i_blind_u, we use the padding for I
    let (i_blind_u_claim, I) = {
      let (x, y) = <C::OC as Ciphersuite>::G::to_xy(output.I).unwrap();
      append_claimed_point_1(&mut c1_tape, output_blinds.i_blind_u, vec![x, y])
    };

    // Commit to the divisor for `i_blind V`, which doesn't commit to the point `i_blind V`
    // (annd that still has to be done)
    let (i_blind_v_divisor, _extra) = c1_tape
      .append_divisor(Some(output_blinds.i_blind_v.divisor), Some(<C::C1 as Ciphersuite>::F::ZERO));

    // For i_blind_blind, we use the padding for (i_blind V)
    let (i_blind_blind_claim, i_blind_V) = {
      let (x, y) = (output_blinds.i_blind_v.x, output_blinds.i_blind_v.y);
      append_claimed_point_1(&mut c1_tape, output_blinds.i_blind_blind, vec![x, y])
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
      append_claimed_point_1(&mut c1_tape, output_blinds.c_blind, vec![x, y])
    };

    // We now have committed to O, I, C, and all interpolated points

    // The first circuit's tape opens the blinds from the second curve
    let mut commitment_blind_claims_1 = vec![];
    for blind in branches_2_blinds_prepared {
      commitment_blind_claims_1.push(
        c1_tape
          .append_claimed_point::<C::C2Parameters>(
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
          .append_claimed_point::<C::C1Parameters>(
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
    // (annd that still has to be done)
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
