use core::ops::{Add, Sub, Mul};

use ciphersuite::group::ff::Field;

/// A reference to a variable usable within linear combinations.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[allow(non_camel_case_types)]
pub(crate) enum Variable {
  aL(usize),
  aR(usize),
  aO(usize),
  C(usize, usize),
}

/// A linear combination.
///
/// Specifically, this is WL aL + WR aR + WO aO + WC C - c.
// We don't model WV as we don't use Pedersen commitments
#[derive(Clone, PartialEq, Eq, Debug)]
#[must_use]
#[allow(non_snake_case)]
pub(crate) struct LinComb<F: Field> {
  pub(crate) WL: Vec<(usize, F)>,
  pub(crate) WR: Vec<(usize, F)>,
  pub(crate) WO: Vec<(usize, F)>,
  pub(crate) WC: Vec<(usize, usize, F)>,
  pub(crate) c: F,
}

impl<F: Field> From<Variable> for LinComb<F> {
  fn from(constrainable: Variable) -> LinComb<F> {
    LinComb::empty().term(F::ONE, constrainable)
  }
}

impl<F: Field> Add<&LinComb<F>> for LinComb<F> {
  type Output = Self;

  fn add(mut self, constraint: &Self) -> Self {
    self.WL.extend(&constraint.WL);
    self.WR.extend(&constraint.WR);
    self.WO.extend(&constraint.WO);
    self.WC.extend(&constraint.WC);
    self.c += constraint.c;
    self
  }
}

impl<F: Field> Sub<&LinComb<F>> for LinComb<F> {
  type Output = Self;

  fn sub(mut self, constraint: &Self) -> Self {
    self.WL.extend(constraint.WL.iter().map(|(index, weight)| (*index, -*weight)));
    self.WR.extend(constraint.WR.iter().map(|(index, weight)| (*index, -*weight)));
    self.WO.extend(constraint.WO.iter().map(|(index, weight)| (*index, -*weight)));
    self.WC.extend(constraint.WC.iter().map(|(i, j, weight)| (*i, *j, -*weight)));
    self.c -= constraint.c;
    self
  }
}

impl<F: Field> Mul<F> for LinComb<F> {
  type Output = Self;

  fn mul(mut self, scalar: F) -> Self {
    for (_, weight) in self.WL.iter_mut() {
      *weight *= scalar;
    }
    for (_, weight) in self.WR.iter_mut() {
      *weight *= scalar;
    }
    for (_, weight) in self.WO.iter_mut() {
      *weight *= scalar;
    }
    for (_, _, weight) in self.WC.iter_mut() {
      *weight *= scalar;
    }
    self.c *= scalar;
    self
  }
}

impl<F: Field> LinComb<F> {
  /// Create an empty linear combination.
  pub(crate) fn empty() -> Self {
    Self { WL: vec![], WR: vec![], WO: vec![], WC: vec![], c: F::ZERO }
  }

  /// Add a new term to this linear combination.
  pub(crate) fn term(mut self, scalar: F, constrainable: Variable) -> Self {
    match constrainable {
      Variable::aL(i) => self.WL.push((i, scalar)),
      Variable::aR(i) => self.WR.push((i, scalar)),
      Variable::aO(i) => self.WO.push((i, scalar)),
      Variable::C(i, j) => self.WC.push((i, j, scalar)),
    };
    self
  }

  /// Add to the constant c which is subtracted from the rest of the linear combination.
  pub(crate) fn constant(mut self, scalar: F) -> Self {
    self.c += scalar;
    self
  }
}
