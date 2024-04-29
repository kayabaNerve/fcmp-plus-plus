use core::ops::{Add, Neg, Sub, Mul, Rem};

use group::ff::PrimeField;

/// A structure representing a Polynomial with x and y terms.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Poly<F: PrimeField + From<u64>> {
  /// c[i] * y ** (i + 1)
  pub y_coefficients: Vec<F>,
  /// c[i][j] * y ** (i + 1) x ** (j + 1)
  pub yx_coefficients: Vec<Vec<F>>,
  /// c[i] * x ** (i + 1)
  pub x_coefficients: Vec<F>,
  /// Coefficient for x ** 0, y ** 0, and x ** 0 y ** 0 (the coefficient for 1)
  pub zero_coefficient: F,
}

impl<F: PrimeField + From<u64>> Poly<F> {
  /// A polynomial for zero.
  pub(crate) fn zero() -> Self {
    Poly {
      y_coefficients: vec![],
      yx_coefficients: vec![],
      x_coefficients: vec![],
      zero_coefficient: F::ZERO,
    }
  }

  /// The amount of non-zero terms in the polynomial.
  #[allow(clippy::len_without_is_empty)]
  pub fn len(&self) -> usize {
    self.y_coefficients.len() +
      self.yx_coefficients.iter().map(Vec::len).sum::<usize>() +
      self.x_coefficients.len() +
      usize::from(u8::from(self.zero_coefficient != F::ZERO))
  }

  // Remove high-order zero terms, allowing the length of the vectors to equal the amount of terms.
  pub(crate) fn tidy(&mut self) {
    let tidy = |vec: &mut Vec<F>| {
      while vec.last() == Some(&F::ZERO) {
        vec.pop();
      }
    };

    tidy(&mut self.y_coefficients);
    for vec in self.yx_coefficients.iter_mut() {
      tidy(vec);
    }
    while self.yx_coefficients.last() == Some(&vec![]) {
      self.yx_coefficients.pop();
    }
    tidy(&mut self.x_coefficients);
  }
}

impl<F: PrimeField + From<u64>> Add<&Self> for Poly<F> {
  type Output = Self;

  fn add(mut self, other: &Self) -> Self {
    // Expand to be the neeeded size
    while self.y_coefficients.len() < other.y_coefficients.len() {
      self.y_coefficients.push(F::ZERO);
    }
    while self.yx_coefficients.len() < other.yx_coefficients.len() {
      self.yx_coefficients.push(vec![]);
    }
    for i in 0 .. other.yx_coefficients.len() {
      while self.yx_coefficients[i].len() < other.yx_coefficients[i].len() {
        self.yx_coefficients[i].push(F::ZERO);
      }
    }
    while self.x_coefficients.len() < other.x_coefficients.len() {
      self.x_coefficients.push(F::ZERO);
    }

    // Perform the addition
    for (i, coeff) in other.y_coefficients.iter().enumerate() {
      self.y_coefficients[i] += coeff;
    }
    for (i, coeffs) in other.yx_coefficients.iter().enumerate() {
      for (j, coeff) in coeffs.iter().enumerate() {
        self.yx_coefficients[i][j] += coeff;
      }
    }
    for (i, coeff) in other.x_coefficients.iter().enumerate() {
      self.x_coefficients[i] += coeff;
    }
    self.zero_coefficient += other.zero_coefficient;

    self.tidy();
    self
  }
}

impl<F: PrimeField + From<u64>> Neg for Poly<F> {
  type Output = Self;

  fn neg(mut self) -> Self {
    for y_coeff in self.y_coefficients.iter_mut() {
      *y_coeff = -*y_coeff;
    }
    for yx_coeffs in self.yx_coefficients.iter_mut() {
      for yx_coeff in yx_coeffs.iter_mut() {
        *yx_coeff = -*yx_coeff;
      }
    }
    for x_coeff in self.x_coefficients.iter_mut() {
      *x_coeff = -*x_coeff;
    }
    self.zero_coefficient = -self.zero_coefficient;

    self
  }
}

impl<F: PrimeField + From<u64>> Sub for Poly<F> {
  type Output = Self;

  fn sub(self, other: Self) -> Self {
    self + &-other
  }
}

impl<F: PrimeField + From<u64>> Mul<F> for Poly<F> {
  type Output = Self;

  fn mul(mut self, scalar: F) -> Self {
    if scalar == F::ZERO {
      return Poly::zero();
    }

    for y_coeff in self.y_coefficients.iter_mut() {
      *y_coeff *= scalar;
    }
    for coeffs in self.yx_coefficients.iter_mut() {
      for coeff in coeffs.iter_mut() {
        *coeff *= scalar;
      }
    }
    for x_coeff in self.x_coefficients.iter_mut() {
      *x_coeff *= scalar;
    }
    self.zero_coefficient *= scalar;
    self
  }
}

impl<F: PrimeField + From<u64>> Poly<F> {
  fn shift_by_x(mut self, power_of_x: usize) -> Self {
    debug_assert_ne!(power_of_x, 0);
    // Shift up every x coefficient
    for _ in 0 .. power_of_x {
      self.x_coefficients.insert(0, F::ZERO);
      for yx_coeffs in &mut self.yx_coefficients {
        yx_coeffs.insert(0, F::ZERO);
      }
    }

    // Move the zero coefficient
    self.x_coefficients[power_of_x - 1] = self.zero_coefficient;
    self.zero_coefficient = F::ZERO;

    // Move the y coefficients
    // Start by creating yx coefficients with the necessary powers of x
    let mut yx_coefficients_to_push = vec![];
    while yx_coefficients_to_push.len() < power_of_x {
      yx_coefficients_to_push.push(F::ZERO);
    }
    // Now, ensure the yx coefficients has the slots for the y coefficients we're moving
    while self.yx_coefficients.len() < self.y_coefficients.len() {
      self.yx_coefficients.push(yx_coefficients_to_push.clone());
    }
    // Perform the move
    for (i, y_coeff) in self.y_coefficients.drain(..).enumerate() {
      self.yx_coefficients[i][power_of_x - 1] = y_coeff;
    }

    self
  }

  fn shift_by_y(mut self, power_of_y: usize) -> Self {
    debug_assert_ne!(power_of_y, 0);
    // Shift up every y coefficient
    for _ in 0 .. power_of_y {
      self.y_coefficients.insert(0, F::ZERO);
      self.yx_coefficients.insert(0, vec![]);
    }

    // Move the zero coefficient
    self.y_coefficients[power_of_y - 1] = self.zero_coefficient;
    self.zero_coefficient = F::ZERO;

    // Move the x coefficients
    self.yx_coefficients[power_of_y - 1] = self.x_coefficients;
    self.x_coefficients = vec![];

    self
  }
}

impl<F: PrimeField + From<u64>> Mul for Poly<F> {
  type Output = Self;

  fn mul(self, other: Self) -> Self {
    let mut res = self.clone() * other.zero_coefficient;

    for (i, y_coeff) in other.y_coefficients.iter().enumerate() {
      let scaled = self.clone() * *y_coeff;
      res = res + &scaled.shift_by_y(i + 1);
    }

    for (y_i, yx_coeffs) in other.yx_coefficients.iter().enumerate() {
      for (x_i, yx_coeff) in yx_coeffs.iter().enumerate() {
        let scaled = self.clone() * *yx_coeff;
        res = res + &scaled.shift_by_y(y_i + 1).shift_by_x(x_i + 1);
      }
    }

    for (i, x_coeff) in other.x_coefficients.iter().enumerate() {
      let scaled = self.clone() * *x_coeff;
      res = res + &scaled.shift_by_x(i + 1);
    }

    res.tidy();
    res
  }
}

impl<F: PrimeField + From<u64>> Poly<F> {
  // Perform multiplication mod `modulus`
  pub(crate) fn mul_mod(self, other: Self, modulus: &Self) -> Self {
    ((self % modulus) * (other % modulus)) % modulus
  }

  /// Perform division, returning the result and remainder.
  pub fn div_rem(self, denominator: &Self) -> (Self, Self) {
    let leading_y = |poly: &Self| -> (_, _) {
      if poly.y_coefficients.len() > poly.yx_coefficients.len() {
        (poly.y_coefficients.len(), 0)
      } else if !poly.yx_coefficients.is_empty() {
        (poly.yx_coefficients.len(), poly.yx_coefficients.last().unwrap().len())
      } else {
        (0, poly.x_coefficients.len())
      }
    };

    let leading_x = |poly: &Self| -> (_, _) {
      if poly.yx_coefficients.is_empty() {
        if !poly.x_coefficients.is_empty() {
          return (0, poly.x_coefficients.len());
        }
        return (poly.y_coefficients.len(), 0);
      }

      let mut longest_yx = 0;
      for i in 0 .. poly.yx_coefficients.len() {
        if poly.yx_coefficients[i].len() > poly.yx_coefficients[longest_yx].len() {
          longest_yx = i;
        }
      }

      if poly.x_coefficients.len() > poly.yx_coefficients[longest_yx].len() {
        (0, poly.x_coefficients.len())
      } else {
        (longest_yx + 1, poly.yx_coefficients[longest_yx].len())
      }
    };

    let y_denom = leading_y(denominator).0 != 0;

    let mut q = Poly::zero();
    let mut r = self;
    while {
      let ((y_a, x_a), (y_b, x_b)) = if y_denom {
        (leading_y(&r), leading_y(denominator))
      } else {
        (leading_x(&r), leading_x(denominator))
      };
      (r != Poly::zero()) && (y_a >= y_b) && (x_a >= x_b)
    } {
      let ((y_a, x_a), (y_b, x_b)) = if y_denom {
        (leading_y(&r), leading_y(denominator))
      } else {
        (leading_x(&r), leading_x(denominator))
      };

      let coeff = |poly: &Self, y: usize, x: usize| -> F {
        if (y == 0) && (x == 0) {
          poly.zero_coefficient
        } else if x == 0 {
          poly.y_coefficients[y - 1]
        } else if y == 0 {
          poly.x_coefficients[x - 1]
        } else {
          poly.yx_coefficients[y - 1][x - 1]
        }
      };

      let coeff_a = coeff(&r, y_a, x_a);
      let coeff_b = coeff(denominator, y_b, x_b);
      let coeff = coeff_a * Option::<F>::from(coeff_b.invert()).expect("denominator wasn't tidy");
      let y_c = y_a - y_b;
      let x_c = x_a - x_b;

      let mut t = Poly::zero();
      if (y_c == 0) && (x_c == 0) {
        t.zero_coefficient = coeff;
      } else if x_c == 0 {
        t.y_coefficients = vec![F::ZERO; y_c];
        t.y_coefficients[y_c - 1] = coeff;
      } else if y_c == 0 {
        t.x_coefficients = vec![F::ZERO; x_c];
        t.x_coefficients[x_c - 1] = coeff;
      } else {
        t.yx_coefficients = vec![vec![]; y_c];
        t.yx_coefficients[y_c - 1] = vec![F::ZERO; x_c];
        t.yx_coefficients[y_c - 1][x_c - 1] = coeff;
      }
      q = q + &t;
      r = r.sub(t * denominator.clone());
    }

    (q, r)
  }
}

impl<F: PrimeField + From<u64>> Rem<&Self> for Poly<F> {
  type Output = Self;

  fn rem(self, modulus: &Self) -> Self {
    self.div_rem(modulus).1
  }
}

impl<F: PrimeField + From<u64>> Poly<F> {
  /// Evaluate this polynomial with the specified x/y values.
  pub fn eval(&self, x: F, y: F) -> F {
    let mut res = self.zero_coefficient;
    for (pow, coeff) in
      self.y_coefficients.iter().enumerate().map(|(i, v)| (u64::try_from(i + 1).unwrap(), v))
    {
      res += y.pow([pow]) * coeff;
    }
    for (y_pow, coeffs) in
      self.yx_coefficients.iter().enumerate().map(|(i, v)| (u64::try_from(i + 1).unwrap(), v))
    {
      let y_pow = y.pow([y_pow]);
      for (x_pow, coeff) in
        coeffs.iter().enumerate().map(|(i, v)| (u64::try_from(i + 1).unwrap(), v))
      {
        res += y_pow * x.pow([x_pow]) * coeff;
      }
    }
    for (pow, coeff) in
      self.x_coefficients.iter().enumerate().map(|(i, v)| (u64::try_from(i + 1).unwrap(), v))
    {
      res += x.pow([pow]) * coeff;
    }
    res
  }

  /// Differentiate a polynomial, reduced y**2, by x and y.
  pub fn differentiate(&self) -> (Poly<F>, Poly<F>) {
    assert!(self.yx_coefficients.len() <= 1);
    assert!(self.y_coefficients.len() <= 1);

    // Differentation by x practically involves:
    // - Dropping everything without an x component
    // - Shifting everything down a power of x
    // - If the x power is greater than 2, multiplying the new term's coefficient by the x power in
    //   question
    let mut diff_x = Poly {
      y_coefficients: vec![],
      yx_coefficients: vec![],
      x_coefficients: vec![],
      zero_coefficient: F::ZERO,
    };
    diff_x.zero_coefficient = self.x_coefficients.first().cloned().unwrap_or(F::ZERO);
    for i in 1 .. self.x_coefficients.len() {
      let power = i + 1;
      diff_x.x_coefficients.push(self.x_coefficients[i] * F::from(u64::try_from(power).unwrap()));
    }

    for (i, yx_coeff) in
      self.yx_coefficients.first().cloned().unwrap_or(vec![]).into_iter().enumerate()
    {
      // Keep the y power, reduce an x power
      let power = i + 1;
      if i == 0 {
        diff_x.y_coefficients.push(yx_coeff);
      } else {
        if diff_x.yx_coefficients.is_empty() {
          diff_x.yx_coefficients.push(vec![]);
        }
        diff_x.yx_coefficients[0].push(yx_coeff * F::from(u64::try_from(power).unwrap()));
      }
    }

    // Differentation by y is trivial
    // It's the y coefficient as the zero coefficient, and the yx coefficients as the x
    // coefficients
    // This is thanks to any y term over y^2 being reduced out
    assert!(self.y_coefficients.len() <= 1);
    assert!(self.yx_coefficients.len() <= 1);
    let diff_y = Poly {
      y_coefficients: vec![],
      yx_coefficients: vec![],
      x_coefficients: self.yx_coefficients.first().cloned().unwrap_or(vec![]),
      zero_coefficient: self.y_coefficients.first().cloned().unwrap_or(F::ZERO),
    };

    (diff_x, diff_y)
  }

  /// Normalize the x coefficient to 1.
  pub fn normalize_x_coefficient(self) -> Self {
    let scalar = self.x_coefficients[0].invert().unwrap();
    self * scalar
  }
}
