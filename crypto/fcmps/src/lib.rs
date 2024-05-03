use rand_core::{RngCore, CryptoRng};

use transcript::Transcript;

use ciphersuite::{
  group::ff::{Field, PrimeField, PrimeFieldBits},
  Ciphersuite,
};

use ec_divisors::Poly;
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
struct PreparedBlind<F: PrimeField> {
  bits: Vec<bool>,
  divisor: Poly<F>,
}

/// The blinds used for an output, prepared for usage within the circuit.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PreparedBlinds<F: PrimeField> {
  o_blind: PreparedBlind<F>,
  i_blind: PreparedBlind<F>,
  i_blind_blind: PreparedBlind<F>,
  c_blind: PreparedBlind<F>,
}

impl<F: PrimeFieldBits> Blinds<F> {
  pub fn new<R: RngCore + CryptoRng>(rng: &mut R) -> Self {
    let new_blind = |rng: &mut R| -> F {
      'outer: loop {
        let res = F::random(&mut *rng);
        // If this uses more bits than capacity, re-sample
        for bit in res.to_le_bits().iter().skip(F::CAPACITY.try_into().unwrap()) {
          if *bit {
            continue 'outer;
          }
        }
        return res;
      }
    };

    let o_blind = new_blind(&mut *rng);
    let i_blind = new_blind(&mut *rng);
    let i_blind_blind = new_blind(&mut *rng);
    let c_blind = new_blind(&mut *rng);

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
}

/// The full-chain membership proof.
pub struct Fcmp<C1: Ciphersuite, C2: Ciphersuite> {
  proof_1: ArithmeticCircuitProof<C1>,
  proof_1_vcs: Vec<C1::G>,
  proof_2: ArithmeticCircuitProof<C2>,
  proof_2_vcs: Vec<C2::G>,
}
impl<C1: Ciphersuite, C2: Ciphersuite> Fcmp<C1, C2> {
  pub fn prove<R: RngCore + CryptoRng, T: Transcript>(
    rng: &mut R,
    transcript: &mut T,
    params: &FcmpParams<C1, C2>,
    tree_root: TreeRoot<C1, C2>,
    depth: u32,
    output: Output<C1::F>,
    blinds: PreparedBlinds<C1::F>,
  ) -> Self {
    // If depth = 1, there's one layer after the leaves
    // That makes the tree root a C1 point
    assert_eq!(depth % 2, u32::from(u8::from(matches!(tree_root, TreeRoot::C1(_)))));

    todo!("TODO")
  }
}
