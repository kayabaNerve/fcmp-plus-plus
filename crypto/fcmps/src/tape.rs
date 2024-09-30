use zeroize::Zeroize;

use generic_array::{typenum::Unsigned, GenericArray};

use multiexp::multiexp;
use ciphersuite::{group::ff::PrimeFieldBits, Ciphersuite};

use ec_divisors::{Poly, DivisorCurve};
use generalized_bulletproofs::Generators;

use crate::{
  Variable,
  gadgets::{DiscreteLogParameters, Divisor, PointWithDlog},
};

/// The variables used for elements in Vector Commitments.
pub(crate) struct VectorCommitmentTape<F: Zeroize + PrimeFieldBits> {
  pub(crate) commitment_len: usize,
  pub(crate) current_j_offset: usize,
  pub(crate) commitments: Vec<(Vec<F>, Vec<F>)>,
}

impl<F: Zeroize + PrimeFieldBits> VectorCommitmentTape<F> {
  /// Append a series of variables to the vector commitment tape.
  pub(crate) fn append(&mut self, variables: Option<Vec<F>>) -> Vec<Variable> {
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
  pub(crate) fn append_branch<C: Ciphersuite>(
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

  /// Append a discrete logarithm of up to 255 coefficients, allowing usage of the extra slot for
  /// an arbitrary variable.
  ///
  /// If the discrete logarithm is less than 255 bits, additional extra elements may be provided
  /// (`padding`), yet these are only accessible on certain curves. This function panics if more
  /// elements are provided in `padding` than free spaces remaining.
  pub(crate) fn append_dlog<Parameters: DiscreteLogParameters>(
    &mut self,
    dlog: Option<&[u64]>,
    padding: Option<Vec<F>>,
    extra: Option<F>,
  ) -> (GenericArray<Variable, Parameters::ScalarBits>, Vec<Variable>, Variable) {
    assert!(Parameters::ScalarBits::USIZE <= 255);
    let dlog_bits = Parameters::ScalarBits::USIZE;

    let witness = dlog.map(|dlog| {
      let mut witness = vec![];
      assert_eq!(dlog.len(), dlog_bits);
      for coeff in dlog {
        witness.push(F::from(*coeff));
      }

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

  pub(crate) fn append_divisor<Parameters: DiscreteLogParameters>(
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

  pub(crate) fn append_claimed_point<Parameters: DiscreteLogParameters>(
    &mut self,
    dlog: Option<&[u64]>,
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

  pub(crate) fn commit<C: Ciphersuite<F = F>>(
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
