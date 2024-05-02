use ciphersuite::{group::ff::Field, Ciphersuite};

use crate::*;

mod interactive;
pub(crate) use interactive::*;

/// A Short Weierstrass curve specification for a towered curve.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) struct CurveSpec<F> {
  pub(crate) a: F,
  pub(crate) b: F,
}

/// A struct for a point on a towered curve which has been confirmed to be on-curve.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) struct OnCurve {
  pub(crate) x: Variable,
  pub(crate) y: Variable,
}

// mmadd-1998-cmo
fn incomplete_add<F: Field>(x1: F, y1: F, x2: F, y2: F) -> Option<(F, F)> {
  let u = y2 - y1;
  let uu = u * u;
  let v = x2 - x1;
  let vv = v * v;
  let vvv = v * vv;
  let r = vv * x1;
  let a = uu - vvv - r.double();
  let x3 = v * a;
  let y3 = (u * (r - a)) - (vvv * y1);
  let z3 = vvv;

  // Normalize from XYZ to XY
  let z3_inv = Option::<F>::from(z3.invert())?;
  let x3 = x3 * z3_inv;
  let y3 = y3 * z3_inv;

  Some((x3, y3))
}

impl<C: Ciphersuite> Circuit<C> {
  /// Constrain two constrainable items as equal.
  fn equality(&mut self, a: LinComb<C::F>, b: &LinComb<C::F>) {
    self.constraints.push(a - b);
  }

  /// Obtain the inverse of a value. Returns a constrainable reference to the value and its
  /// inverse.
  ///
  /// This will panic if the witness is zero.
  fn inverse(&mut self, a: Option<LinComb<C::F>>, witness: Option<C::F>) -> (Variable, Variable) {
    let (l, r, o) = self.mul(a, None, witness.map(|f| (f, f.invert().unwrap())));
    // The output of a value multiplied by its inverse is 1
    // Constrain `1 o - 1 = 0`
    self.constraints.push(LinComb::from(o).constant(C::F::ONE));
    (l, r)
  }

  /// Constrain two items as inequal.
  fn inequality(&mut self, a: LinComb<C::F>, b: &LinComb<C::F>, witness: Option<(C::F, C::F)>) {
    let l_constraint = a - b;
    // The existence of a multiplicative inverse means a-b != 0, which means a != b
    self.inverse(Some(l_constraint), witness.map(|(a, b)| a - b));
  }

  /// Constrain an item as being a member of a list.
  ///
  /// Panics if the list is empty.
  pub(crate) fn member_of_list(&mut self, member: LinComb<C::F>, list: Vec<LinComb<C::F>>) {
    let mut list = list.into_iter();

    // Initialize the carry to the first list member minus the claimed member
    let mut carry = list.next().unwrap() - &member;

    for list_member in list {
      // Multiply the carry by the next evaluation
      let next = list_member - &member;

      let carry_eval = self.eval(&carry);
      let next_eval = self.eval(&next);
      let witness = carry_eval.map(|carry_eval| (carry_eval, next_eval.unwrap()));

      let (_l, _r, constrainable_carry) = self.mul(Some(carry), Some(next), witness);
      carry = constrainable_carry.into();
    }

    // Constrain the carry to be 0, meaning one of the products multiplied was zero
    self.constraints.push(carry);
  }

  /// Constrain an x and y coordinate as being on curve to a towered elliptic curve.
  pub(crate) fn on_curve(
    &mut self,
    curve: &CurveSpec<C::F>,
    (x, y): (Variable, Variable),
  ) -> OnCurve {
    let x_eval = self.eval(&LinComb::from(x));
    let (_x, _x_2, x2) =
      self.mul(Some(LinComb::from(x)), Some(LinComb::from(x)), x_eval.map(|x| (x, x)));
    let (_x, _x_2, x3) =
      self.mul(Some(LinComb::from(x2)), Some(LinComb::from(x)), x_eval.map(|x| (x * x, x)));
    let expected_y2 = LinComb::from(x3).term(curve.a, x).constant(-curve.b);

    let y_eval = self.eval(&LinComb::from(y));
    let (_y, _y_2, y2) =
      self.mul(Some(LinComb::from(y)), Some(LinComb::from(y)), y_eval.map(|y| (y, y)));

    self.equality(y2.into(), &expected_y2);

    OnCurve { x, y }
  }

  /// Perform checked incomplete addition for a public point and an on-curve point.
  // TODO: Do we need to constrain c on-curve? That may be redundant
  pub(crate) fn incomplete_add_pub(&mut self, a: (C::F, C::F), b: OnCurve, c: OnCurve) -> OnCurve {
    // Check b.x != a.0
    {
      let bx_lincomb = LinComb::from(b.x);
      let bx_eval = self.eval(&bx_lincomb);
      self.inequality(bx_lincomb, &LinComb::empty().constant(-a.0), bx_eval.map(|bx| (bx, a.0)));
    }

    let (x0, y0) = (a.0, a.1);
    let (x1, y1) = (b.x, b.y);
    let (x2, y2) = (c.x, c.y);

    let slope_eval = self.eval(&LinComb::from(x1)).map(|x1| {
      let y1 = self.eval(&LinComb::from(b.y)).unwrap();

      (y1 - y0) * (x1 - x0).invert().unwrap()
    });

    // slope * (x1 - x0) = y1 - y0
    let x1_minus_x0 = LinComb::from(x1).constant(x0);
    let x1_minus_x0_eval = self.eval(&x1_minus_x0);
    let (slope, _r, o) =
      self.mul(None, Some(x1_minus_x0), slope_eval.map(|slope| (slope, x1_minus_x0_eval.unwrap())));
    self.equality(LinComb::from(o), &LinComb::from(y1).constant(y0));

    // slope * (x2 - x0) = -y2 - y0
    let x2_minus_x0 = LinComb::from(x2).constant(x0);
    let x2_minus_x0_eval = self.eval(&x2_minus_x0);
    let (_slope, _x2_minus_x0, o) = self.mul(
      Some(slope.into()),
      Some(x2_minus_x0),
      slope_eval.map(|slope| (slope, x2_minus_x0_eval.unwrap())),
    );
    self.equality(o.into(), &LinComb::empty().term(-C::F::ONE, y2).constant(y0));

    // slope * slope = x0 + x1 + x2
    let (_slope, _slope_2, o) =
      self.mul(Some(slope.into()), Some(slope.into()), slope_eval.map(|slope| (slope, slope)));
    self.equality(o.into(), &LinComb::from(x1).term(C::F::ONE, x2).constant(-x0));

    OnCurve { x: x2, y: y2 }
  }

  /// Constrain a `y` coordinate as being permissible.
  ///
  /// Panics if the prover and the `y` coordinate isn't permissible.
  pub(crate) fn permissible(&mut self, a: C::F, b: C::F, y: Variable) {
    // a y - -b = ay + b
    let p = LinComb::empty().term(a, y).constant(-b);
    let p_eval = self.eval(&p);
    let p_eval_sqrt = p_eval.map(|p_eval| p_eval.sqrt().unwrap());

    let (l, r, o) = self.mul(None, None, p_eval_sqrt.map(|sqrt| (sqrt, sqrt)));
    // Ensure this is actually a sqrt
    self.equality(l.into(), &r.into());
    // Ensure the sq is the y coordinate derivative
    self.equality(p, &o.into());
  }
}
