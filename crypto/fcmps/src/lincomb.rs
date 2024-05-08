use core::ops::{Add, Sub, Mul};

use ciphersuite::group::ff::Field;

/// A reference to a variable usable within linear combinations.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[allow(non_camel_case_types)]
pub(crate) enum Variable {
  aL(usize),
  aR(usize),
  aO(usize),
  CL(usize, usize),
  CR(usize, usize),
}

/// A linear combination.
///
/// Specifically, this is WL aL + WR aR + WO aO + WC C + c.
// We don't model WV as we don't use Pedersen commitments
#[derive(Clone, PartialEq, Eq, Debug)]
#[must_use]
pub(crate) struct LinComb<F: Field> {
  pub(crate) WL: Vec<(usize, F)>,
  pub(crate) WR: Vec<(usize, F)>,
  pub(crate) WO: Vec<(usize, F)>,
  pub(crate) WCL: Vec<Vec<(usize, F)>>,
  pub(crate) WCR: Vec<Vec<(usize, F)>>,
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
    while self.WCL.len() < constraint.WCL.len() {
      self.WCL.push(vec![]);
    }
    while self.WCR.len() < constraint.WCR.len() {
      self.WCR.push(vec![]);
    }
    for (sWC, cWC) in self.WCL.iter_mut().zip(&constraint.WCL) {
      sWC.extend(cWC);
    }
    for (sWC, cWC) in self.WCR.iter_mut().zip(&constraint.WCR) {
      sWC.extend(cWC);
    }
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
    while self.WCL.len() < constraint.WCL.len() {
      self.WCL.push(vec![]);
    }
    for (sWC, cWC) in self.WCL.iter_mut().zip(&constraint.WCL) {
      sWC.extend(cWC.iter().map(|(j, weight)| (*j, -*weight)));
    }
    while self.WCR.len() < constraint.WCR.len() {
      self.WCR.push(vec![]);
    }
    for (sWC, cWC) in self.WCR.iter_mut().zip(&constraint.WCR) {
      sWC.extend(cWC.iter().map(|(j, weight)| (*j, -*weight)));
    }
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
    for WC in self.WCL.iter_mut() {
      for (_, weight) in WC {
        *weight *= scalar;
      }
    }
    for WC in self.WCR.iter_mut() {
      for (_, weight) in WC {
        *weight *= scalar;
      }
    }
    self.c *= scalar;
    self
  }
}

impl<F: Field> LinComb<F> {
  /// Create an empty linear combination.
  pub(crate) fn empty() -> Self {
    Self { WL: vec![], WR: vec![], WO: vec![], WCL: vec![], WCR: vec![], c: F::ZERO }
  }

  /// Add a new term to this linear combination.
  pub(crate) fn term(mut self, scalar: F, constrainable: Variable) -> Self {
    match constrainable {
      Variable::aL(i) => self.WL.push((i, scalar)),
      Variable::aR(i) => self.WR.push((i, scalar)),
      Variable::aO(i) => self.WO.push((i, scalar)),
      Variable::CL(i, j) => {
        while self.WCL.len() <= i {
          self.WCL.push(vec![]);
        }
        self.WCL[i].push((j, scalar))
      }
      Variable::CR(i, j) => {
        while self.WCR.len() <= i {
          self.WCR.push(vec![]);
        }
        self.WCR[i].push((j, scalar))
      }
    };
    self
  }

  /// Add to the constant c, which is added to the rest of the linear combination.
  pub(crate) fn constant(mut self, scalar: F) -> Self {
    self.c += scalar;
    self
  }
}
