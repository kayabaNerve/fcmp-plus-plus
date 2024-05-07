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
pub(crate) struct ClaimedPointWithDlog {
  pub(crate) divisor: Divisor,
  pub(crate) dlog: Vec<Variable>,
  pub(crate) point: (Variable, Variable),
}

#[derive(Clone)]
struct ChallengePoint<F: Field> {
  x: Vec<F>,
  y: F,
  yx: Vec<F>,
  p_0_n_0: F,
  x_p_0_n_0: Vec<F>,
  p_1_n: F,
  p_1_d: F,
}

impl<F: Field> ChallengePoint<F> {
  fn new(
    curve: &CurveSpec<F>,
    divisor_x_len: usize,
    divisor_yx_len: usize,
    slope: F,
    x: F,
    y: F,
    inv_two_y: F,
  ) -> Self {
    // Powers of x
    let mut x_pows = Vec::with_capacity(divisor_x_len);
    x_pows.push(x);
    while x_pows.len() < divisor_x_len {
      let last = *x_pows.last().unwrap();
      x_pows.push(last * x);
    }

    // Powers of x multiplied by y
    let mut yx = Vec::with_capacity(divisor_yx_len);
    yx.push(y * x);
    while yx.len() < divisor_yx_len {
      let last = *yx.last().unwrap();
      yx.push(last * x);
    }

    let x_sq = x.square();
    let three_x_sq = x_sq.double() + x_sq;
    let three_x_sq_plus_a = three_x_sq + curve.a;
    let two_y = y.double();

    let p_0_n_0 = three_x_sq_plus_a * inv_two_y;
    let mut x_p_0_n_0 = Vec::with_capacity(divisor_yx_len);
    for i in 0 .. divisor_yx_len {
      x_p_0_n_0.push(p_0_n_0 * x_pows[i]);
    }

    let p_1_n = two_y;
    let p_1_d = (-slope * two_y) + three_x_sq_plus_a;

    ChallengePoint { x: x_pows, y, yx, p_0_n_0, x_p_0_n_0, p_1_n, p_1_d }
  }
}

pub(crate) struct DiscreteLogChallenge<F: Field> {
  c0: ChallengePoint<F>,
  c1: ChallengePoint<F>,
  c2: ChallengePoint<F>,
  slope: F,
  intercept: F,
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

  /// Prove the claimed discrete logarithm is a consistent representation of the discrete log
  /// for the specified point over the specified generator.
  ///
  /// The discrete log representation must be treated as a non-canonical, opaque black box. A
  /// discrete log has effectively infinite representations within this black box. The only
  /// guarantee is that the discrete log proven for is always equivalent to any other discrete log
  /// proven for with this exact representation.
  ///
  /// Ensures the point is on-curve.
  pub(crate) fn discrete_log_challenges<T: Transcript>(
    &mut self,
    transcript: &mut T,
    curve: &CurveSpec<C::F>,
    divisor_x_len: usize,
    divisor_yx_len: usize,
    generators: &[&[(C::F, C::F)]],
  ) -> (DiscreteLogChallenge<C::F>, Vec<Vec<C::F>>) {
    let amount_of_powers_of_2 =
      generators.first().expect("creating dlog challenges for no dlog claims").len();

    // Get the challenge points
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

    // Calculate the slope and intercept
    let slope = (c1_y - c0_y) * (c1_x - c0_x).invert().unwrap();
    let intercept = c0_y - (slope * c0_x);

    // Calculate the inversions for 2 c_y (for each c) and all of the challenged generators
    let mut inversions = vec![C::F::ZERO; 3 + (generators.len() * amount_of_powers_of_2)];

    // Needed for the left-hand side eval
    {
      inversions[0] = c0_y.double();
      inversions[1] = c1_y.double();
      inversions[2] = c2_y.double();
    }

    // Perform the inversions for the generators
    for (i, generator) in generators.iter().enumerate() {
      // Needed for the right-hand side eval
      debug_assert_eq!(amount_of_powers_of_2, generator.len());
      for (j, generator) in (*generator).iter().enumerate() {
        inversions[3 + (i * amount_of_powers_of_2) + j] =
          intercept - (generator.1 - (slope * generator.0));
      }
    }
    for challenge_inversion in &inversions {
      // This should be unreachable barring negligible probability
      if challenge_inversion.is_zero().into() {
        panic!("trying to invert 0");
      }
    }
    let mut scratch = vec![C::F::ZERO; inversions.len()];
    let _ = BatchInverter::invert_with_external_scratch(&mut inversions, &mut scratch);

    let mut inversions = inversions.into_iter();
    let inv_c0_two_y = inversions.next().unwrap();
    let inv_c1_two_y = inversions.next().unwrap();
    let inv_c2_two_y = inversions.next().unwrap();

    let c0 =
      ChallengePoint::new(curve, divisor_x_len, divisor_yx_len, slope, c0_x, c0_y, inv_c0_two_y);
    let c1 =
      ChallengePoint::new(curve, divisor_x_len, divisor_yx_len, slope, c1_x, c1_y, inv_c1_two_y);
    let c2 =
      ChallengePoint::new(curve, divisor_x_len, divisor_yx_len, slope, c2_x, c2_y, inv_c2_two_y);

    // Fill in the inverted values
    let mut challenged_generators = Vec::with_capacity(generators.len());
    for _ in 0 .. generators.len() {
      let mut challenged_generator = Vec::with_capacity(generators.len());
      for _ in 0 .. amount_of_powers_of_2 {
        challenged_generator.push(inversions.next().unwrap());
      }
      challenged_generators.push(challenged_generator);
    }

    (DiscreteLogChallenge { c0, c1, c2, slope, intercept }, challenged_generators)
  }

  fn divisor_challenge_eval(&mut self, divisor: &Divisor, challenge: &ChallengePoint<C::F>) -> Variable {
    // The evaluation of the divisor differentiated by y, further multiplied by p_0_n_0
    // Differentation drops everything without a y coefficient, and drops what remains by a power
    // of y
    // (y**1 -> y**0, yx**i -> x**i)
    let p_0_n_1 = {
      let mut p_0_n_1 = LinComb::empty().term(challenge.p_0_n_0, divisor.y);
      for (i, var) in divisor.yx.iter().enumerate() {
        p_0_n_1 = p_0_n_1.term(challenge.x_p_0_n_0[i], *var);
      }
      p_0_n_1
    };

    // The evaluation of the divisor differentiated by x
    let p_0_n_2 = {
      // The coefficient for x**1 is 1, so 1 becomes the new zero coefficient
      let mut p_0_n_2 = LinComb::empty().constant(C::F::ONE);

      // Handle the new y coefficient
      p_0_n_2 = p_0_n_2.term(challenge.y, divisor.yx[0]);

      // Handle the new yx coefficients
      for (j, yx) in divisor.yx.iter().enumerate().skip(1) {
        // For the power which was shifted down, we multiply this coefficient
        // 3 x**2 -> 2 * 3 x**1
        let original_power_of_x = C::F::from(u64::try_from(j + 1).unwrap());
        let this_weight = original_power_of_x * challenge.yx[j - 1];

        p_0_n_2 = p_0_n_2.term(this_weight, *yx);
      }

      // Handle the x coefficients
      // We don't skip the first one as `x_from_power_of_2` already omits x**1
      for (i, x) in divisor.x_from_power_of_2.iter().enumerate() {
        let original_power_of_x = C::F::from(u64::try_from(i + 2).unwrap());
        let this_weight = original_power_of_x * challenge.x[i];

        p_0_n_2 = p_0_n_2.term(this_weight, *x);
      }

      p_0_n_2
    };

    let p_0_n = p_0_n_1 + &p_0_n_2;

    // Evaluation of the divisor
    let p_0_d = {
      let mut p_0_d = LinComb::empty().term(challenge.y, divisor.y);

      for (var, c_yx) in divisor.yx.iter().zip(&challenge.yx) {
        p_0_d = p_0_d.term(*c_yx, *var);
      }

      for (i, var) in divisor.x_from_power_of_2.iter().enumerate() {
        p_0_d = p_0_d.term(challenge.x[i + 1], *var);
      }

      // Adding x effectively adds a `1 x` term, ensuring the divisor isn't 0
      p_0_d.term(C::F::ONE, divisor.zero).constant(challenge.x[0])
    };

    // Calculate the joint numerator
    let p_n = p_0_n * challenge.p_1_n;
    // Calculate the joint denominator
    let p_d = p_0_d * challenge.p_1_d;

    // We want `n / d = o`
    // `n / d = o` == `n = d * o`
    // This is a safe unwrap as it's solely done by the prover and should always be non-zero
    let witness =
      self.eval(&p_d).map(|p_d| (p_d, self.eval(&p_n).unwrap() * p_d.invert().unwrap()));
    let (_l, o, n_claim) = self.mul(Some(p_d), None, witness);
    self.equality(p_n, &n_claim.into());
    o
  }

  pub(crate) fn discrete_log(
    &mut self,
    curve: &CurveSpec<C::F>,
    claim: ClaimedPointWithDlog,
    challenge: &DiscreteLogChallenge<C::F>,
    challenged_generator: &[C::F],
  ) -> OnCurve {
    let ClaimedPointWithDlog { divisor, dlog, point } = claim;

    // Ensure this is being safely called
    let arg_iter = [point.0, point.1, divisor.y, divisor.zero];
    let arg_iter = arg_iter.iter().chain(divisor.yx.iter());
    let arg_iter = arg_iter.chain(divisor.x_from_power_of_2.iter());
    let arg_iter = arg_iter.chain(dlog.iter());
    for variable in arg_iter {
      debug_assert!(
        matches!(variable, Variable::C(_, _)),
        "discrete log requires all arguments belong to vector commitments",
      );
    }

    let point = self.on_curve(curve, point);

    // lhs from the paper, evaluating the divisor
    let lhs_eval = LinComb::from(self.divisor_challenge_eval(&divisor, &challenge.c0)) +
      &LinComb::from(self.divisor_challenge_eval(&divisor, &challenge.c1)) +
      &LinComb::from(self.divisor_challenge_eval(&divisor, &challenge.c2));

    // Interpolate the powers of the generator
    debug_assert_eq!(dlog.len(), challenged_generator.len());
    let mut rhs_eval = LinComb::empty();
    for (bit, weight) in dlog.into_iter().zip(challenged_generator) {
      rhs_eval = rhs_eval.term(*weight, bit);
    }

    // Interpolate the output point
    // intercept - (y - (slope * x))
    // intercept - y + (slope * x))
    // -y + (slope * x)) + intercept
    // EXCEPT the output point we're proving the discrete log for isn't the one interpolated
    // Its negative is, so -y becomes y
    let output_interpolation = LinComb::empty()
      .constant(challenge.intercept)
      .term(C::F::ONE, point.y)
      .term(challenge.slope, point.x);
    let output_interpolation_eval = self.eval(&output_interpolation);
    let (_output_interpolation, inverse) =
      self.inverse(Some(output_interpolation), output_interpolation_eval);
    rhs_eval = rhs_eval.term(C::F::ONE, inverse);

    self.equality(lhs_eval, &rhs_eval);

    point
  }
}
