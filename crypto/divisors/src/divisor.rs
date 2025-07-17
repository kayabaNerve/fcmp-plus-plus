use crate::barycentric::Interpolator;
use core::ops::{Div, Mul};
use ff::PrimeField;
use std_shims::alloc::rc::Rc;
use std_shims::{vec, vec::Vec};
use subtle::ConditionallySelectable;

/// Divisor of form f(x,y) = A(x) - yB(x), with A and B
/// represented as enough evaluations for their degree.
#[derive(Debug, Clone)]
pub struct Divisor<F: PrimeField> {
  a: Evals<F>,
  b: Evals<F>,
  // to substitute y^2
  modulus: Rc<Evals<F>>,
}

/// Represented as coefficients as it can be efficiently evaluated
/// in O(n) additions.
#[derive(Debug, Clone, Copy)]
pub struct SmallDivisor<F: PrimeField> {
  // (a,b) for ax + b
  a: (F, F),
  b: F,
}

impl<F> ConditionallySelectable for SmallDivisor<F>
where
  F: PrimeField + ConditionallySelectable,
{
  fn conditional_select(a: &Self, b: &Self, choice: subtle::Choice) -> Self {
    let a0 = <_>::conditional_select(&a.a.0, &b.a.0, choice);
    let a1 = <_>::conditional_select(&a.a.1, &b.a.1, choice);
    let b = <_>::conditional_select(&a.b, &b.b, choice);
    let a = (a0, a1);
    SmallDivisor { a, b }
  }
}

impl<F: PrimeField> Divisor<F> {
  pub fn ab(&self, i: usize) -> (F, F) {
    let a = self.a.evals[i];
    let b = self.b.evals[i];
    (a, b)
  }

  fn ab_mut(&mut self, i: usize) -> (&mut F, &mut F) {
    let a = &mut self.a.evals[i];
    let b = &mut self.b.evals[i];
    (a, b)
  }

  /// New degree after mul.
  fn new_degree(&self, other: &Self) -> (usize, usize) {
    // f1 * f2 = A1A2 - y(A1B2 + A2B1) + (x^3 + ax + b) B1B2
    // A = A1A2 + (x^3 + ax + b) B1B2
    // B = A1B2 + A2B1
    // deg(A) = max(A1 + A2, 3 + B1 + B2)
    // deg(B) = max(A1 + B2, A2 + B1)
    let (a1, b1) = (self.a.degree, self.b.degree);
    let (a2, b2) = (other.a.degree, other.b.degree);
    let a = (a1 + a2).max(3 + b1 + b2);
    let b = (a1 + b2).max(a2 + b1);
    (a, b)
  }

  /// Remove 2 points by dividing by (x - x1) * (x - x2)
  fn remove_diff(self, x1: F, x2: F) -> Self {
    assert_eq!(self.a.len(), self.b.len());
    let mut denominator = Vec::with_capacity(self.a.len());
    let mut x = F::ZERO;
    for _ in 0 .. self.a.len() {
      denominator.push((x - x1) * (x - x2));
      x += F::ONE;
    }
    let denominator = Evals { evals: denominator, degree: 2 };
    self / denominator
  }

  pub fn merge(divisors: [Self; 2], small: SmallDivisor<F>, denom: (F, F)) -> Self {
    let [d1, d2] = divisors;
    let numerator = d1 * &d2;
    //TODO: second operand can be reused for scratch space
    let numerator = numerator * small;
    let (x1, x2) = denom;
    numerator.remove_diff(x1, x2)
  }

  pub fn from_small(small: SmallDivisor<F>, modulus: Rc<Evals<F>>) -> Self {
    let SmallDivisor { a, b } = small;
    let evals = modulus.len();
    let a = Evals::from_degree_1(a.0, a.1, evals);
    let b = Evals::degree_0(b, evals);
    Self { a, b, modulus }
  }

  pub fn compute_modulus(a: F, b: F, evals: usize) -> Rc<Evals<F>> {
    // x^3 * ax + b
    let count = evals;
    let mut evals = Vec::with_capacity(evals);

    for i in 0 .. count {
      let x = F::from(i as u64);
      let cube = x.square() * x;
      let ax = x * a;
      evals.push(cube + ax + b);
    }
    assert_eq!(evals[0], b);
    assert_eq!(evals[1], b + a + F::ONE);
    Rc::new(Evals::new(evals, 3))
  }
  /// Returns [a,b] as coefficient vecs.
  pub fn interpolate(self, interpolator: &Interpolator<F>) -> [Vec<F>; 2] {
    let a = self.a.interpolate(interpolator);
    let b = self.b.interpolate(interpolator);
    [a, b]
  }
}

impl<F: PrimeField> SmallDivisor<F> {
  pub fn new(a: (F, F), b: F) -> Self {
    Self { a, b }
  }
}

#[derive(Debug, Clone)]
pub struct Evals<F: PrimeField> {
  evals: Vec<F>,
  degree: usize,
}

impl<F: PrimeField> Evals<F> {
  pub fn new(evals: Vec<F>, degree: usize) -> Self {
    Self { evals, degree }
  }

  fn len(&self) -> usize {
    self.evals.len()
  }

  fn from_degree_1(coeff: F, constant: F, evals: usize) -> Self {
    let count = evals;
    let mut evals = Vec::with_capacity(evals);
    if count == 0 {
      return Evals { evals, degree: 1 };
    }
    // assmuning domain 0..n
    let mut last_eval = constant;
    for _ in 0 .. count {
      evals.push(last_eval);
      last_eval += coeff;
    }
    Self { evals, degree: 1 }
  }

  fn degree_0(coeff: F, evals: usize) -> Self {
    let evals = vec![coeff; evals];
    Evals { evals, degree: 0 }
  }

  /// interpolate into a vector of coefficients.
  /// O(n^2).
  pub fn interpolate(self, interpolator: &Interpolator<F>) -> Vec<F> {
    let Self { evals, .. } = self;
    interpolator.interpolate(evals).inner()
  }
}

impl<F: PrimeField> Mul<&Self> for Divisor<F> {
  type Output = Self;

  fn mul(mut self, rhs: &Self) -> Self::Output {
    debug_assert_eq!(self.a.len(), rhs.a.len());
    debug_assert_eq!(self.b.len(), rhs.b.len());
    debug_assert_eq!(self.a.len(), self.b.len());
    let len = self.a.len();

    let new_degree = self.new_degree(&rhs);
    // f1 * f2 = A1A2 - y(A1B2 + A2B1) + y^2 B1B2
    // f1 * f2 = A1A2 - y(A1B2 + A2B1) + (x^3 + ax + b) B1B2
    // (A1+B1)(A2+B2)
    // A1A2 + A1B2 + B1A2 + B1B2
    for i in 0 .. len {
      let modulus = self.modulus.evals[i];
      let (a1, b1) = self.ab_mut(i);
      let (a2, b2) = rhs.ab(i);
      let a1a2 = *a1 * a2;
      let b1b2 = *b1 * b2;
      // (A1+B1)(A2+B2)
      let cross = (*a1 + *b1) * (a2 + b2);
      let b = cross - (a1a2 + b1b2);
      let a = a1a2 + b1b2 * modulus;
      *a1 = a;
      *b1 = b;
    }
    let (a, b) = new_degree;
    self.a.degree = a;
    self.b.degree = b;
    self
  }
}

impl<F: PrimeField> Mul<SmallDivisor<F>> for Divisor<F> {
  type Output = Self;

  fn mul(mut self, rhs: SmallDivisor<F>) -> Self::Output {
    debug_assert_eq!(self.a.len(), self.b.len());
    let len = self.a.len();

    // constant term for x = 0
    let mut a2 = rhs.a.1;
    let b2 = rhs.b;
    for i in 0 .. len {
      let modulus = self.modulus.evals[i];
      let (a1, b1) = self.ab_mut(i);
      let a1a2 = *a1 * a2;
      let b1b2 = *b1 * b2;
      // (A1+B1)(A2+B2)
      let cross = (*a1 + *b1) * (a2 + b2);
      let b = cross - (a1a2 + b1b2);
      let a = a1a2 + b1b2 * modulus;
      a2 += rhs.a.0;
      *a1 = a;
      *b1 = b;
    }
    let da = self.a.degree;
    let db = self.b.degree;
    self.a.degree = (da + 1).max(db + 3);
    self.b.degree = da.max(1 + db);
    self
  }
}

impl<F: PrimeField> Div<Evals<F>> for Divisor<F> {
  type Output = Self;

  fn div(mut self, mut rhs: Evals<F>) -> Self::Output {
    let len = rhs.len();
    debug_assert_eq!(self.a.len(), self.b.len());
    debug_assert_eq!(self.a.len(), len);
    // TODO: maybe reuse
    let mut scratch_space: Vec<F> = rhs.evals.clone();
    ff::BatchInverter::invert_with_external_scratch(&mut rhs.evals, &mut scratch_space);
    for i in 0 .. len {
      let denom = rhs.evals[i];
      self.a.evals[i] *= denom;
      self.b.evals[i] *= denom;
    }
    self.a.degree -= rhs.degree;
    self.b.degree -= rhs.degree;
    self
  }
}
