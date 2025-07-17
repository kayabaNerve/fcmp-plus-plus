//! Barycentric evaluation

use core::{iter::successors, ops::AddAssign};
use ff::{Field, PrimeField};
use std_shims::{vec, vec::Vec};
use subtle::CtOption;

pub struct Weights<F: Field> {
  weights: Vec<F>,
  inverted_weights: Vec<F>,
}

#[derive(Debug, Clone)]
pub struct Coeffs<F>(Vec<F>);

impl<F: Field> Coeffs<F> {
  #[cfg(test)]
  fn eval(&self, x: F) -> F {
    self.0.iter().rev().fold(F::ZERO, |acc, coeff| acc * x + coeff)
  }

  /// Mul by (x + c).
  fn simple_mul(&mut self, c: F) {
    let coeffs = &mut self.0;
    coeffs.insert(0, F::ZERO);
    for i in 0 .. (coeffs.len() - 1) {
      let q = coeffs[i + 1];
      coeffs[i] += q * c;
    }
  }

  /// Divides arbitrary polynomial by (x + c) for given c.
  fn synthetic_division(mut self, c: F) -> (Self, F) {
    let coeffs = &mut self.0;
    let len = coeffs.len();
    let c_neg = -c;
    let mut new_coeff = coeffs.pop().unwrap();
    for i in 1 .. len {
      let coeff = coeffs[len - 1 - i];
      coeffs[len - 1 - i] = new_coeff;
      new_coeff = coeff + new_coeff * c_neg;
    }
    let remainder = new_coeff;
    (self, remainder)
  }

  fn scale_in_place(&mut self, scalar: F) {
    for coeff in self.0.iter_mut() {
      coeff.mul_assign(scalar);
    }
  }

  pub fn inner(self) -> Vec<F> {
    self.0
  }
}

impl<F: Field> AddAssign<&Self> for Coeffs<F> {
  fn add_assign(&mut self, rhs: &Self) {
    assert_eq!(self.0.len(), rhs.0.len());
    for i in 0 .. self.0.len() {
      self.0[i] += rhs.0[i];
    }
  }
}

impl<F: PrimeField> Weights<F> {
  pub fn new(domain_size: usize) -> Self {
    let start = Some(F::ZERO - F::ONE);
    let diffs = successors(start, |prev| Some(*prev - F::ONE));
    let diff_products = diffs.scan(F::ONE, |product, diff| {
      *product *= diff;
      Some(*product)
    });
    let mut diff_products: Vec<F> = diff_products.take(domain_size - 1).collect();
    diff_products.reverse();
    diff_products.push(F::ONE);
    let diff_products_right = diff_products.into_iter();

    let diffs = successors(Some(F::ONE), |prev| Some(*prev + F::ONE));
    let diff_products_left = diffs.scan(F::ONE, |product, diff| {
      *product *= diff;
      Some(*product)
    });
    let diff_products_left = [F::ONE].into_iter().chain(diff_products_left);

    let weights: Vec<F> =
      diff_products_left.zip(diff_products_right).map(|(left, right)| left * right).collect();
    Self::from_weights(weights)
  }

  fn from_weights(weights: Vec<F>) -> Self {
    let inverted_weights = weights.iter().map(F::invert).map(CtOption::unwrap).collect();
    Weights { weights, inverted_weights }
  }

  /// P(x) = (x-0)(x-1)(x-2)...(x-domain_size - 1)
  fn l(&self) -> Coeffs<F> {
    let mut poly = Coeffs(vec![F::ONE]);
    let domain_size = self.weights.len();
    for i in 0 .. domain_size {
      let constant: F = F::from(i as u64);
      let c = -constant;
      poly.simple_mul(c);
    }
    poly
  }

  fn li(&self, l: &Coeffs<F>, i: usize) -> Coeffs<F> {
    assert!(i < self.weights.len());
    let weight = self.inverted_weights[i];
    let c = -F::from(i as u64);
    let (mut li, rest) = l.clone().synthetic_division(c);
    assert_eq!(rest, F::ZERO);
    li.scale_in_place(weight);
    li
  }
}

#[test]
fn synthetic_div() {
  use pasta_curves::Fp;

  let coeffs = vec![40_u64, 34, 52, 532, 089];
  let poly: Vec<Fp> = coeffs.into_iter().map(Fp::from).collect();
  let poly = Coeffs(poly);

  println!("poly: {:#?}", poly);
  let c = Fp::from(432);
  let (mut quot, rest) = poly.synthetic_division(c);
  quot.simple_mul(c);
  quot.0[0] += rest;
  let poly = quot;
  println!("poly: {:#?}", poly);
}

#[test]
fn interpolation() {
  use pasta_curves::Fp;

  let evals = vec![40_u64, 34, 52, 532, 089];
  let evals: Vec<Fp> = evals.into_iter().map(Fp::from).collect();

  let weights = Weights::new(5);
  let interpolator = Interpolator::new(4);
  println!("weights: \n {:#?}", weights.weights);

  let coeffs = interpolator.interpolate(evals.clone());
  let mut evals2 = vec![];
  let l = weights.l();
  for i in 0 .. 5 {
    let li = weights.li(&l, i);
    let li_eval = li.eval(Fp::from(i as u64));
    println!("L_{}({}): {:?}", i, i, li_eval);
    let e = coeffs.eval(Fp::from(i as u64));
    evals2.push(e);
  }
  assert_eq!(evals, evals2);
}

/// All precomputation necessary to optimally interpolate polynomials
/// of a given degree.
pub struct Interpolator<F: Field> {
  /// maximal degree expected
  degree: usize,
  lagrange_polys: Vec<Coeffs<F>>,
}

impl<F: PrimeField> Interpolator<F> {
  pub fn new(degree: usize) -> Self {
    let domain_size = degree + 1;
    let weights = Weights::new(domain_size);
    let mut lagrange_polys = vec![];
    let l = weights.l();
    for i in 0 .. (domain_size) {
      let li = weights.li(&l, i);
      lagrange_polys.push(li);
    }
    Self { degree, lagrange_polys }
  }

  pub fn interpolate(&self, mut evals: Vec<F>) -> Coeffs<F> {
    assert!(evals.len() > self.degree);
    evals.truncate(self.degree + 1);
    let len = evals.len();

    let poly = vec![F::ZERO; len];
    let mut poly = Coeffs(poly);
    for i in 0 .. len {
      let mut li = self.lagrange_polys[i].clone();
      li.scale_in_place(evals[i]);
      poly += &li;
    }
    poly
  }
}

// (Xi - X0)(Xi - X1)(Xi - X2)(Xi - X3)
// i = 1 (X1 - X0)(X1 - X2)(X1 - X3)
// i = 2 (X2 - X0)(X2 - X1)(X2 - X3)
//
// (Xi - 0)(Xi - 1)(Xi - 2)(Xi - 3)
// i = 1 (1 - 0)(1 - 2)(1 - 3)
// i = 2 (2 - 0)(2 - 1)(2 - 3)
//
// i = 1 : 1 * -1 * -2
// i = 1 : 2 * 1 * -2
// (Xi - 0)(Xi - 1)(Xi - 2)(Xi - 3)
// !(0 - 0)(0 - 1)(0 - 2)(0 - 3) = (1) * -1 * -2 * -3
// (1 - 0)!(1 - 1)(1 - 2)(1 - 3) = 1 * (1) * -1 * -2
// (2 - 0)(2 - 1)!(2 - 2)(2 - 3) = 2 * 1 * (1) * -1
// (3 - 0)(3 - 1)(3 - 2)!(3 - 3) = 3 * 2 * 1 * (1)
