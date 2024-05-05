use transcript::Transcript;

use ciphersuite::{
  group::ff::{PrimeField, BatchInverter},
  Ciphersuite,
};

use crate::{
  *,
  gadgets::{CurveSpec, OnCurve, incomplete_add},
};

/// A representation of the divisor.
///
/// The coefficient for x**1 is explicitly excluded.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) struct Divisor {
  pub(crate) y: Variable,
  pub(crate) yx: Vec<Variable>,
  pub(crate) x_from_power_of_2: Vec<Variable>,
  pub(crate) zero: Variable,
}

/// A claimed point and associated discrete logarithm claim.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) struct ClaimedPointWithDlog<'a, F: Field> {
  pub(crate) generator: &'a [(F, F)],
  pub(crate) divisor: Divisor,
  pub(crate) dlog: Vec<Variable>,
  pub(crate) point: (Variable, Variable),
}

impl<C: Ciphersuite> Circuit<C> {
  pub(crate) fn tuple_member_of_list<T: Transcript>(
    &mut self,
    transcript: &mut T,
    member: Vec<Variable>,
    list: Vec<Vec<Variable>>,
  ) {
    // Ensure this is being safely called
    for variable in member.iter().chain(list.iter().flatten()) {
      assert!(
        matches!(variable, Variable::C(_, _)),
        "tuple member of set requires all arguments belong to vector commitments"
      );
    }

    // Create challenges which we use to aggregate tuples into LinCombs
    let mut challenges = vec![];
    for _ in 0 .. member.len() {
      challenges
        .push(C::hash_to_F(b"fcmp", transcript.challenge(b"tuple_member_of_list").as_ref()));
    }

    // Aggregate the claimed member
    let member = {
      let mut res = LinComb::empty();
      for (i, member) in member.into_iter().enumerate() {
        res = res + &(LinComb::from(member) * challenges[i]);
      }
      res
    };

    // Aggregate the list members
    let list = {
      let mut res = vec![];
      for list_tuple in list {
        let mut item = LinComb::empty();
        for (i, list_member) in list_tuple.into_iter().enumerate() {
          item = item + &(LinComb::from(list_member) * challenges[i]);
        }
        res.push(item);
      }
      res
    };

    // Run traditional set membership
    self.member_of_list(member, list)
  }

  fn divisor_challenge(
    &mut self,
    curve: &CurveSpec<C::F>,
    divisor: &Divisor,
    slope: C::F,
    c_x: C::F,
    c_y: C::F,
    inv_two_c_y: C::F,
  ) -> Variable {
    let c_x_sq = c_x.square();
    let three_x_sq = c_x_sq.double() + c_x_sq;
    let three_x_sq_plus_a = three_x_sq + curve.a;
    let two_c_y = c_y.double();

    let p_0_n_0 = three_x_sq_plus_a * inv_two_c_y;

    let mut c_yx = Vec::with_capacity(divisor.yx.len());
    c_yx.push(c_y * c_x);
    while c_yx.len() < divisor.yx.len() {
      let last = *c_yx.last().unwrap();
      c_yx.push(last * c_x);
    }

    // The evaluation of the divisor differentiated by y, further multiplied by p_0_n_0
    // Differentation drops everything without a y coefficient, and drops what remains by a power
    // of y
    // (y**1 -> y**0, yx**i -> x**i)
    let p_0_n_1 = {
      let mut p_0_n_1 = LinComb::empty().term(p_0_n_0, divisor.y);
      let mut c_x_eval = p_0_n_0 * c_x;
      for var in &divisor.yx {
        p_0_n_1 = p_0_n_1.term(c_x_eval, *var);
        c_x_eval *= c_x;
      }
      p_0_n_1
    };

    // The evaluation of the divisor differentiated by x
    let p_0_n_2 = {
      // The coefficient for x**1 is 1, so 1 becomes the new zero coefficient
      let mut p_0_n_2 = LinComb::empty().constant(C::F::ONE);

      // Handle the new y coefficient
      p_0_n_2 = p_0_n_2.term(c_y, divisor.yx[0]);

      // Handle the new yx coefficients
      for (j, yx) in divisor.yx.iter().enumerate().skip(1) {
        // For the power which was shifted down, we multiply this coefficient
        // 3 x**2 -> 2 * 3 x**1
        let original_power_of_x = C::F::from(u64::try_from(j + 1).unwrap());
        let this_weight = original_power_of_x * c_yx[j - 1];

        p_0_n_2 = p_0_n_2.term(this_weight, *yx);
      }

      // Handle the x coefficients
      let mut c_x_eval = c_x;
      // We don't skip the first one as `x_from_power_of_2` already omits x**1
      for (i, x) in divisor.x_from_power_of_2.iter().enumerate() {
        let original_power_of_x = C::F::from(u64::try_from(i + 2).unwrap());
        let this_weight = original_power_of_x * c_x_eval;

        p_0_n_2 = p_0_n_2.term(this_weight, *x);

        c_x_eval *= c_x;
      }

      p_0_n_2
    };

    let p_0_n = p_0_n_1 + &p_0_n_2;

    let p_0_d = {
      let mut p_0_d = LinComb::empty().term(c_y, divisor.y);

      for (var, c_yx) in divisor.yx.iter().zip(c_yx) {
        p_0_d = p_0_d.term(c_yx, *var);
      }

      let mut c_x_eval = c_x_sq;
      for var in &divisor.x_from_power_of_2 {
        p_0_d = p_0_d.term(c_x_eval, *var);
        c_x_eval *= c_x;
      }

      // Adding c_x effectively adds a `1 x` term, ensuring the divisor isn't 0
      p_0_d.term(C::F::ONE, divisor.zero).constant(c_x)
    };

    let p_1_n = two_c_y;
    let p_1_d = (-slope * two_c_y) + three_x_sq_plus_a;

    // Calculate the joint numerator
    let p_n = p_0_n * p_1_n;
    // Calculate the joint denominator
    let p_d = p_0_d * p_1_d;

    // We want `n / d = o`
    // `n / d = o` == `n = d * o`
    // This is a safe unwrap as it's solely done by the prover and should always be non-zero
    let witness =
      self.eval(&p_d).map(|p_d| (p_d, self.eval(&p_n).unwrap() * p_d.invert().unwrap()));
    let (_l, o, n_claim) = self.mul(Some(p_d), None, witness);
    self.equality(p_n, &n_claim.into());
    o
  }

  /// Prove the claimed discrete logarithm is a consistent representation of the discrete log
  /// for the specified point over the specified generator.
  ///
  /// The discrete log representation must be treated as a non-canonical, opaque black box. A
  /// discrete log has effectively infinite representations within this black box. The only
  /// guarantee is that the discrete log proven for is always equivalent to any other discrete log
  /// proven for with this exact representation.
  ///
  /// Ensures the point is on-curve.
  pub(crate) fn discrete_log<T: Transcript>(
    &mut self,
    transcript: &mut T,
    curve: &CurveSpec<C::F>,
    claim: ClaimedPointWithDlog<C::F>,
  ) -> OnCurve {
    let ClaimedPointWithDlog { generator, divisor, dlog, point } = claim;
    assert_eq!(generator.len(), dlog.len());

    // Ensure this is being safely called
    let arg_iter = core::iter::once(&divisor.y).chain(divisor.yx.iter());
    let arg_iter =
      arg_iter.chain(divisor.x_from_power_of_2.iter()).chain(core::iter::once(&divisor.zero));
    let arg_iter = arg_iter.chain(dlog.iter());
    for variable in arg_iter.chain([point.0, point.1].iter()) {
      assert!(
        matches!(variable, Variable::C(_, _)),
        "discrete log requires all arguments belong to vector commitments",
      );
    }

    let point = self.on_curve(curve, point);

    // TODO: Implement a proper hash to curve
    let (c0_x, c0_y) = loop {
      let c0_x = C::hash_to_F(b"fcmp", transcript.challenge(b"discrete_log_0").as_ref());
      let Some(c0_y) =
        Option::<C::F>::from(((c0_x.square() * c0_x) + (curve.a * c0_x) + curve.b).sqrt())
      else {
        continue;
      };
      break (c0_x, if bool::from(c0_y.is_odd()) { -c0_y } else { c0_y });
    };
    let (c1_x, c1_y) = loop {
      let c1_x = C::hash_to_F(b"fcmp", transcript.challenge(b"discrete_log_1").as_ref());
      if c0_x == c1_x {
        continue;
      }
      let Some(c1_y) =
        Option::<C::F>::from(((c1_x.square() * c1_x) + (curve.a * c1_x) + curve.b).sqrt())
      else {
        continue;
      };
      break (c1_x, if bool::from(c1_y.is_odd()) { -c1_y } else { c1_y });
    };

    let (c2_x, c2_y) = incomplete_add::<C::F>(c0_x, c0_y, c1_x, c1_y)
      .expect("couldn't perform incomplete addition on two distinct, on curve points");
    let c2_y = -c2_y;

    // This unwrap should be unreachable barring negligible probability
    let slope = (c1_y - c0_y) * (c1_x - c0_x).invert().unwrap();
    let intercept = c0_y - (slope * c0_x);

    // We need the inversions for all of the following
    let mut inverted = {
      let mut need_inversion = Vec::with_capacity(3 + generator.len());
      // Needed for the right-hand side evel
      for generator in generator {
        need_inversion.push(intercept - (generator.1 - (slope * generator.0)));
      }
      // Needed for the left-hand side eval (2 y)
      need_inversion.push(c2_y.double());
      need_inversion.push(c1_y.double());
      need_inversion.push(c0_y.double());
      for need_inversion in &need_inversion {
        // This should be unreachable barring negligible probability
        if need_inversion.is_zero().into() {
          panic!("trying to invert 0");
        }
      }
      let mut scratch = vec![C::F::ZERO; need_inversion.len()];
      let _ = BatchInverter::invert_with_external_scratch(&mut need_inversion, &mut scratch);
      need_inversion
    };
    let inv_two_c0_y = inverted.pop().unwrap();
    let inv_two_c1_y = inverted.pop().unwrap();
    let inv_two_c2_y = inverted.pop().unwrap();

    // lhs from the paper, evaluating the divisor
    let lhs_eval =
      LinComb::from(self.divisor_challenge(curve, &divisor, slope, c0_x, c0_y, inv_two_c0_y)) +
        &LinComb::from(self.divisor_challenge(curve, &divisor, slope, c1_x, c1_y, inv_two_c1_y)) +
        &LinComb::from(self.divisor_challenge(curve, &divisor, slope, c2_x, c2_y, inv_two_c2_y));

    // Interpolate the powers of the generator
    let mut rhs_eval = LinComb::empty();
    for (bit, weight) in dlog.into_iter().zip(inverted) {
      rhs_eval = rhs_eval.term(weight, bit);
    }

    // Interpolate the output point
    // intercept - (y - (slope * x))
    // intercept - y + (slope * x))
    // -y + (slope * x)) + intercept
    // EXCEPT the output point we're proving the discrete log for isn't the one interpolated
    // Its negative is, so -y becomes y
    let output_interpolation =
      LinComb::empty().constant(intercept).term(C::F::ONE, point.y).term(slope, point.x);
    let output_interpolation_eval = self.eval(&output_interpolation);
    let (_output_interpolation, inverse) =
      self.inverse(Some(output_interpolation), output_interpolation_eval);
    rhs_eval = rhs_eval.term(C::F::ONE, inverse);

    self.equality(lhs_eval, &rhs_eval);

    point
  }
}
