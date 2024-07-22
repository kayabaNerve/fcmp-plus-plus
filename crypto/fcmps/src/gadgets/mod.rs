use ciphersuite::Ciphersuite;

use crate::*;

mod interactive;
pub(crate) use interactive::*;

impl<C: Ciphersuite> Circuit<C> {
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
    self.constrain_equal_to_zero(carry);
  }

  /// Constrain an x and y coordinate as being on curve to a towered elliptic curve.
  pub(crate) fn on_curve(
    &mut self,
    curve: &CurveSpec<C::F>,
    point: (Variable, Variable),
  ) -> OnCurve {
    self.0.on_curve(curve, point)
  }

  /// Perform checked incomplete addition for a public point and an on-curve point.
  // TODO: Do we need to constrain c on-curve? That may be redundant
  pub(crate) fn incomplete_add_pub(&mut self, a: (C::F, C::F), b: OnCurve, c: OnCurve) -> OnCurve {
    self.0.incomplete_add_fixed(a, b, c)
  }
}
