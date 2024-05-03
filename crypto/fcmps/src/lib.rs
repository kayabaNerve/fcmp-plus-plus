use rand_core::{RngCore, CryptoRng};

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
use generalized_bulletproofs::{Generators, arithmetic_circuit_proof::ArithmeticCircuitProof};

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
  x: F,
  y: F,
}

impl<F: PrimeFieldBits> PreparedBlind<F> {
  fn new<C1: Ciphersuite>(blinding_generator: C1::G, blind: C1::F) -> Self
  where
    C1::G: DivisorCurve<FieldElement = F>,
  {
    let bits = blind.to_le_bits().into_iter().collect::<Vec<_>>();
    assert_eq!(u32::try_from(bits.len()).unwrap(), C1::F::NUM_BITS);

    let res_point = blinding_generator * -blind;

    let divisor = {
      let mut gen_pow_2 = blinding_generator;
      let mut points = vec![];
      for bit in &bits {
        if *bit {
          points.push(gen_pow_2);
        }
        gen_pow_2 = gen_pow_2.double();
      }
      points.push(res_point);
      new_divisor::<C1::G>(&points).unwrap()
    };

    let (x, y) = C1::G::to_xy(res_point);
    Self { bits, divisor, x, y }
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

/// A struct representing an input tuple.
#[allow(non_snake_case)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Input<F: Field> {
  O_tilde: (F, F),
  I_tilde: (F, F),
  R: (F, F),
  C_tilde: (F, F),
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
  /// The towered curve, defined over the initial curve's scalar field.
  towered: CurveSpec<C1::F>,
  /// The initial curve, defined over the secondary curve's scalar field.
  initial: CurveSpec<C2::F>,
  /// The secondary curve, defined over the initial curve's scalar field.
  secondary: CurveSpec<C1::F>,

  /// Generators for the first curve.
  curve_one_generators: Generators<T, C1>,
  /// Generators for the second curve.
  curve_two_generators: Generators<T, C2>,
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
  fn transcript<T: Transcript>(
    transcript: &mut T,
    input: Input<C1::F>,
    commitments_1: Vec<C1::G>,
    commitments_2: Vec<C2::G>,
  ) {
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

  pub fn prove<R: RngCore + CryptoRng, T: Transcript>(
    rng: &mut R,
    transcript: &mut T,
    params: &FcmpParams<T, C1, C2>,
    tree: TreeRoot<C1, C2>,
    output: Output<C1::F>,
    output_blinds: PreparedBlinds<C1::F>,
    mut branches: Branches<C1, C2>,
  ) -> Self {
    // Re-format the leaves into the expected branch format
    let mut branches_1 = vec![vec![]];
    for leaf in branches.leaves {
      branches_1[0].extend(&[leaf.O.0, leaf.I.0, leaf.I.1, leaf.C.0]);
    }

    // Append the rest of the branches
    let branches_2 = branches.curve_2_layers;
    branches_1.append(&mut branches.curve_1_layers);

    // Accumulate a blind into a witness vector
    fn accum_blind<C: Ciphersuite>(
      witness: &mut Vec<Vec<C::F>>,
      prepared_blind: PreparedBlind<C::F>,
    ) {
      assert!(C::F::NUM_BITS <= 255);

      // Bits
      let mut bit_witness = vec![];
      assert_eq!(prepared_blind.bits.len(), usize::try_from(C::F::NUM_BITS).unwrap());
      for i in 0 .. 255 {
        bit_witness.push(if *prepared_blind.bits.get(i).unwrap_or(&false) {
          C::F::ONE
        } else {
          C::F::ZERO
        });
      }

      // Divisor y
      // This takes 1 slot
      let mut divisor_witness = vec![];
      divisor_witness.push(*prepared_blind.divisor.y_coefficients.first().unwrap_or(&C::F::ZERO));

      // Divisor yx
      // We allocate 126 slots for this
      let empty_vec = vec![];
      let yx = prepared_blind.divisor.yx_coefficients.first().unwrap_or(&empty_vec);
      assert!(yx.len() <= 126);
      for i in 0 .. 126 {
        divisor_witness.push(*yx.get(i).unwrap_or(&C::F::ZERO));
      }

      // Divisor x
      assert!(prepared_blind.divisor.x_coefficients.len() <= 128);
      assert_eq!(prepared_blind.divisor.x_coefficients[0], C::F::ONE);
      // Transcript from 1 given we expect a normalization of the first coefficient
      // We allocate 127 slots for this
      for i in 1 .. 128 {
        divisor_witness.push(*prepared_blind.divisor.x_coefficients.get(i).unwrap_or(&C::F::ZERO));
      }

      // Divisor 0
      // This takes 1 slot
      divisor_witness.push(prepared_blind.divisor.zero_coefficient);

      assert_eq!(bit_witness.len(), 255);
      assert_eq!(divisor_witness.len(), 255);

      // Because the bit and divisors witnesses are less than 255, we have one slot open
      // Use said slots for the x/y coordinates of the resulting point
      bit_witness.push(prepared_blind.x);
      divisor_witness.push(prepared_blind.y);

      witness.push(bit_witness);
      witness.push(divisor_witness);
    }

    // Decide blinds for each branch
    let mut branches_1_blinds = vec![];
    let mut branches_1_blinds_prepared = vec![];
    for _ in 0 .. branches_1.len() {
      let blind = C1::F::random(&mut *rng);
      branches_1_blinds.push(blind);
      branches_1_blinds_prepared
        .push(PreparedBlind::<_>::new::<C1>(params.curve_one_generators.h(), blind));
    }

    let mut branches_2_blinds = vec![];
    let mut branches_2_blinds_prepared = vec![];
    for _ in 0 .. branches_2.len() {
      let blind = C2::F::random(&mut *rng);
      branches_2_blinds.push(blind);
      branches_2_blinds_prepared
        .push(PreparedBlind::<_>::new::<C2>(params.curve_two_generators.h(), blind));
    }

    // interactive_witness_1 gets the leaves' openings/divisors, along with the standard witness
    // for the relevant branches
    let mut interactive_witness_1 = vec![];
    let mut interactive_witness_1_blinds = vec![];
    accum_blind::<C1>(&mut interactive_witness_1, output_blinds.o_blind);
    accum_blind::<C1>(&mut interactive_witness_1, output_blinds.i_blind);
    accum_blind::<C1>(&mut interactive_witness_1, output_blinds.i_blind_blind);
    accum_blind::<C1>(&mut interactive_witness_1, output_blinds.c_blind);
    // We open the blinds from the other curve
    for blind in branches_2_blinds_prepared {
      accum_blind::<C1>(&mut interactive_witness_1, blind);
    }
    for _ in 0 .. interactive_witness_1_blinds.len() {
      interactive_witness_1_blinds.push(C1::F::random(&mut *rng));
    }

    // interactive_witness_2 gets the witness for the relevant branches
    let mut interactive_witness_2 = vec![];
    let mut interactive_witness_2_blinds = vec![];
    for blind in branches_1_blinds_prepared {
      accum_blind::<C2>(&mut interactive_witness_2, blind);
    }
    for _ in 0 .. interactive_witness_2_blinds.len() {
      interactive_witness_2_blinds.push(C2::F::random(&mut *rng));
    }

    // We have now committed to the discrete logs, the divisors, and the output points...
    // and the sets, yet not the set members (which we need to for the tuple membership gadget)
    //
    // The tuple membership is (O.x, I.x, I.y, C.x) and is deterministic to the output tuple and
    // the output blind/linking tag generator blind/commitment blind
    //
    // Because the output tuple and blinds have been committed to, the set members have also been
    // We accordingly don't need slots in a commitment for them (which would be a new commitment,
    // as all existing commitments are in use)

    // Calculate all of the PVCs and transcript them
    {
      let input = todo!("TODO");

      fn calc_commitments<T: Transcript, C: Ciphersuite>(
        generators: &Generators<T, C>,
        branches: Vec<Vec<C::F>>,
        branch_blinds: Vec<C::F>,
        witness: Vec<Vec<C::F>>,
        witness_blinds: Vec<C::F>,
      ) -> Vec<C::G> {
        assert_eq!(branches.len(), branch_blinds.len());
        assert_eq!(witness.len(), witness_blinds.len());

        let mut res = vec![];
        for (values, blind) in
          branches.into_iter().chain(witness).zip(branch_blinds.into_iter().chain(witness_blinds))
        {
          let g_generators = generators.g_bold_slice()[.. values.len()].iter().cloned();
          let mut commitment =
            g_generators.enumerate().map(|(i, g)| (values[i], g)).collect::<Vec<_>>();
          commitment.push((blind, generators.h()));
          res.push(multiexp(&commitment));
        }
        res
      }
      let commitments_1 = calc_commitments::<T, C1>(
        &params.curve_one_generators,
        branches_1.clone(),
        branches_1_blinds.clone(),
        interactive_witness_1.clone(),
        interactive_witness_1_blinds.clone(),
      );
      let commitments_2 = calc_commitments::<T, C2>(
        &params.curve_two_generators,
        branches_2.clone(),
        branches_2_blinds.clone(),
        interactive_witness_2.clone(),
        interactive_witness_2_blinds.clone(),
      );

      Self::transcript(transcript, input, commitments_1, commitments_2);
    }

    // Create the circuits
    let mut all_commitments_1 = branches_1;
    all_commitments_1.append(&mut interactive_witness_1);
    let c1_circuit = Circuit::<C1>::prove(all_commitments_1);

    let mut all_commitments_2 = branches_2;
    all_commitments_2.append(&mut interactive_witness_2);
    let c2_circuit = Circuit::<C2>::prove(all_commitments_2);

    // Perform the layers
    todo!("TODO");
    /*
    first_layer
      &mut self,
      transcript: &mut T,
      curve: &CurveSpec<C::F>,

      O_tilde: (C::F, C::F),
      o_blind: ClaimedPointWithDlog<C::F>,
      O: (Variable, Variable),

      I_tilde: (C::F, C::F),
      i_blind_u: ClaimedPointWithDlog<C::F>,
      I: (Variable, Variable),

      R: (C::F, C::F),
      i_blind_v: ClaimedPointWithDlog<C::F>,
      i_blind_blind: ClaimedPointWithDlog<C::F>,

      C_tilde: (C::F, C::F),
      c_blind: ClaimedPointWithDlog<C::F>,
      C: (Variable, Variable),

      branch: Vec<Vec<Variable>>,
    )
    */

    // Escape to the raw weights to form a GBP with
    todo!("TODO")
  }
}
