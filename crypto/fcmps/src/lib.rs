use ciphersuite::{group::ff::Field, Ciphersuite};

mod lincomb;
use lincomb::*;

mod gadgets;

/// The witness for the satisfaction of this circuit.
#[derive(Clone, PartialEq, Eq, Debug)]
#[allow(non_snake_case)]
struct ProverData<F: Field> {
  aL: Vec<F>,
  aR: Vec<F>,
  C: Vec<Vec<F>>,
}

/// A struct representing a circuit.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Circuit<C: Ciphersuite> {
  muls: usize,
  commitments: usize,
  // A series of linear combinations which must evaluate to 0.
  constraints: Vec<LinComb<C::F>>,
  prover: Option<ProverData<C::F>>,
}

impl<C: Ciphersuite> Circuit<C> {
  /// Evaluate a constraint.
  ///
  /// Yields WL aL + WR aR + WO aO + WC C.
  ///
  /// Panics if the constraint references non-existent terms.
  ///
  /// Returns None if not a prover.
  fn eval(&self, constraint: &LinComb<C::F>) -> Option<C::F> {
    self.prover.as_ref().map(|prover| {
      let mut res = -constraint.c;
      for (index, weight) in &constraint.WL {
        res += prover.aL[*index] * weight;
      }
      for (index, weight) in &constraint.WR {
        res += prover.aR[*index] * weight;
      }
      for (index, weight) in &constraint.WO {
        res += prover.aL[*index] * prover.aR[*index] * weight;
      }
      for (i, j, weight) in &constraint.WC {
        res += prover.C[*i][*j] * weight;
      }
      res
    })
  }

  /// Multiply two values, optionally constrained, returning the constrainable left/right/out
  /// terms.
  ///
  /// This will panic if passed a witness when this circuit isn't constructed for proving.
  fn mul(
    &mut self,
    a: Option<LinComb<C::F>>,
    b: Option<LinComb<C::F>>,
    witness: Option<(C::F, C::F)>,
  ) -> (Variable, Variable, Variable) {
    let l = Variable::aL(self.muls);
    let r = Variable::aR(self.muls);
    let o = Variable::aO(self.muls);
    self.muls += 1;

    if let Some(a) = a {
      self.constraints.push(a.term(-C::F::ONE, l));
    }
    if let Some(b) = b {
      self.constraints.push(b.term(-C::F::ONE, r));
    }

    assert_eq!(self.prover.is_some(), witness.is_some());
    if let Some(witness) = witness {
      let prover = self.prover.as_mut().unwrap();
      prover.aL.push(witness.0);
      prover.aR.push(witness.1);
    }

    (l, r, o)
  }
}
