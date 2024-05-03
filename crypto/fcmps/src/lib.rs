use rand_core::{RngCore, CryptoRng};

use transcript::Transcript;

use ciphersuite::{
  group::{
    ff::{Field, PrimeField, PrimeFieldBits},
    Group,
  },
  Ciphersuite,
};

use ec_divisors::{Poly, DivisorCurve, new_divisor};
use generalized_bulletproofs::arithmetic_circuit_proof::ArithmeticCircuitProof;

#[allow(unused)] // TODO
mod lincomb;
pub(crate) use lincomb::*;
#[allow(unused)] // TODO
mod gadgets;
pub(crate) use gadgets::*;
#[allow(unused)] // TODO
mod circuit;
pub(crate) use circuit::*;

/// The blinds used with an output.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Blinds<F: PrimeFieldBits> {
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
}

impl<F: PrimeFieldBits> PreparedBlind<F> {
  fn new<C1: Ciphersuite>(blinding_generator: C1::G, blind: C1::F) -> Self
  where
    C1::G: DivisorCurve<FieldElement = F>,
  {
    let bits = blind.to_le_bits().into_iter().collect::<Vec<_>>();
    assert_eq!(u32::try_from(bits.len()).unwrap(), C1::F::NUM_BITS);

    let divisor = {
      let mut gen_pow_2 = blinding_generator;
      let mut points = vec![];
      for bit in &bits {
        if *bit {
          points.push(gen_pow_2);
        }
        gen_pow_2 = gen_pow_2.double();
      }
      points.push(blinding_generator * -blind);
      new_divisor::<C1::G>(&points).unwrap()
    };

    Self { bits, divisor }
  }
}

/// The blinds used for an output, prepared for usage within the circuit.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PreparedBlinds<F: PrimeFieldBits> {
  o_blind: PreparedBlind<F>,
  i_blind: PreparedBlind<F>,
  i_blind_blind: PreparedBlind<F>,
  c_blind: PreparedBlind<F>,
}

impl<F: PrimeFieldBits> Blinds<F> {
  pub fn new<R: RngCore + CryptoRng>(rng: &mut R) -> Self {
    let o_blind = F::random(&mut *rng);
    let i_blind = F::random(&mut *rng);
    let i_blind_blind = F::random(&mut *rng);
    let c_blind = F::random(&mut *rng);

    // o_blind, i_blind, c_blind are used in-circuit as negative
    let o_blind = -o_blind;
    let i_blind = -i_blind;
    let c_blind = -c_blind;

    Blinds { o_blind, i_blind, i_blind_blind, c_blind }
  }

  pub fn prepare(&self) -> PreparedBlinds<F> {
    let prepare = |blind: F| todo!("TODO");
    PreparedBlinds {
      o_blind: prepare(self.o_blind),
      i_blind: prepare(self.i_blind),
      i_blind_blind: prepare(self.i_blind_blind),
      c_blind: prepare(self.c_blind),
    }
  }
}

/// A struct representing an output tuple.
#[allow(non_snake_case)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Output<F: Field> {
  O: (F, F),
  I: (F, F),
  C: (F, F),
}

/// A tree root, represented as a point from either curve.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TreeRoot<C1: Ciphersuite, C2: Ciphersuite> {
  C1(C1::G),
  C2(C2::G),
}

/// A tree, represented as a tree root and its depth.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Tree<C1: Ciphersuite, C2: Ciphersuite> {
  root: TreeRoot<C1, C2>,
  depth: u32,
}

/// The parameters for full-chain membership proofs.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct FcmpParams<C1: Ciphersuite, C2: Ciphersuite> {
  /// The towered curve, defined over the initial curve's scalar field.
  towered: CurveSpec<C1::F>,
  /// The initial curve, defined over the secondary curve's scalar field.
  initial: CurveSpec<C2::F>,
  /// The secondary curve, defined over the initial curve's scalar field.
  secondary: CurveSpec<C1::F>,
  /// The blinding generator for the vector commitments on the initial curve.
  initial_blinding_generator: C1::G,
  /// The blinding generator for the vector commitments on the secondary curve.
  secondary_blinding_generator: C2::G,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Branches<C1: Ciphersuite, C2: Ciphersuite> {
  leaves: Vec<Output<C1::F>>,
  curve_2_layers: Vec<Vec<C2::F>>,
  curve_1_layers: Vec<Vec<C1::F>>,
}

/// The full-chain membership proof.
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
  pub fn prove<R: RngCore + CryptoRng, T: Transcript>(
    rng: &mut R,
    transcript: &mut T,
    params: &FcmpParams<C1, C2>,
    tree: Tree<C1, C2>,
    output: Output<C1::F>,
    output_blinds: PreparedBlinds<C1::F>,
    mut branches: Branches<C1, C2>,
  ) -> Self {
    // Assert the depth is greater than or equal to two, and we'll actually use both proofs
    assert!(tree.depth >= 2);
    // If depth = 1, there's one layer after the leaves
    // That makes the tree root a C1 point
    assert_eq!(tree.depth % 2, u32::from(u8::from(matches!(tree.root, TreeRoot::C1(_)))));

    // Re-format the leaves into the expected branch format
    let mut branches_1 = vec![vec![]];
    for leaf in branches.leaves {
      branches_1[0].extend(&[leaf.O.0, leaf.I.0, leaf.I.1, leaf.C.0]);
    }

    // Append the rest of the branches
    let branches_2 = branches.curve_2_layers;
    branches_1.append(&mut branches.curve_1_layers);

    // Accumulate a blind into a witness vector
    fn accum_blind<C: Ciphersuite>(witness: &mut Vec<C::F>, prepared_blind: PreparedBlind<C::F>) {
      // Bits
      assert_eq!(prepared_blind.bits.len(), usize::try_from(C::F::NUM_BITS).unwrap());
      for bit in &prepared_blind.bits {
        witness.push(if *bit { C::F::ONE } else { C::F::ZERO });
      }

      // Divisor y
      witness.push(*prepared_blind.divisor.y_coefficients.first().unwrap_or(&C::F::ZERO));

      // Divisor yx
      // We have `(p / 2) - 2` yx coeffs, where p is the amount of points
      let p = prepared_blind.bits.len() + 1;
      let empty_vec = vec![];
      let yx = prepared_blind.divisor.yx_coefficients.first().unwrap_or(&empty_vec);
      for i in 0 .. (p / 2).saturating_sub(2) {
        witness.push(*yx.get(i).unwrap_or(&C::F::ZERO));
      }

      // Divisor x
      // We have `p / 2` x coeffs
      assert_eq!(prepared_blind.divisor.x_coefficients[0], C::F::ONE);
      // Transcript from 1 given we expect a normalization of the first coefficient
      for i in 1 .. (p / 2) {
        witness.push(*prepared_blind.divisor.x_coefficients.get(i).unwrap_or(&C::F::ZERO));
      }

      // Divisor 0
      witness.push(prepared_blind.divisor.zero_coefficient);
    }

    // Decide blinds for each branch
    let mut branches_1_blinds = vec![];
    let mut branches_1_blinds_prepared = vec![];
    for _ in 0 .. branches_1.len() {
      let blind = C1::F::random(&mut *rng);
      branches_1_blinds.push(blind);
      branches_1_blinds_prepared
        .push(PreparedBlind::<_>::new::<C1>(params.initial_blinding_generator, blind));
    }

    let mut branches_2_blinds = vec![];
    let mut branches_2_blinds_prepared = vec![];
    for _ in 0 .. branches_2.len() {
      let blind = C2::F::random(&mut *rng);
      branches_2_blinds.push(blind);
      branches_2_blinds_prepared
        .push(PreparedBlind::<_>::new::<C2>(params.secondary_blinding_generator, blind));
    }

    // interactive_witness_1 gets the leaves' openings/divisors, along with the standard witness
    // for the relevant branches
    let mut interactive_witness_1 = vec![];
    accum_blind::<C1>(&mut interactive_witness_1, output_blinds.o_blind);
    accum_blind::<C1>(&mut interactive_witness_1, output_blinds.i_blind);
    accum_blind::<C1>(&mut interactive_witness_1, output_blinds.i_blind_blind);
    accum_blind::<C1>(&mut interactive_witness_1, output_blinds.c_blind);
    for blind in branches_2_blinds_prepared {
      accum_blind::<C1>(&mut interactive_witness_1, blind);
    }

    // interactive_witness_2 gets the witness for the relevant branches
    let mut interactive_witness_2 = vec![];
    for blind in branches_1_blinds_prepared {
      accum_blind::<C2>(&mut interactive_witness_2, blind);
    }

    todo!("TODO")
  }
}
