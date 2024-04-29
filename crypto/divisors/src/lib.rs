#![allow(non_snake_case)]

use group::{
  ff::{Field, PrimeField},
  Group,
};

mod poly;
pub use poly::*;

#[cfg(test)]
pub(crate) mod tests;

/// A curve usable with this library.
pub trait DivisorCurve: Group
where
  Self::Scalar: PrimeField,
{
  /// An element of the field this curve is defined over.
  type FieldElement: PrimeField;

  /// The A in the curve equation y^2 = x^3 + A x^2 + B x + C.
  const A: u64;
  /// The B in the curve equation y^2 = x^3 + A x^2 + B x + C.
  const B: u64;
  /// The C in the curve equation y^2 = x^3 + A x^2 + B x + C.
  const C: u64;

  /// y^2 - x^3 - A x^2 - B x - C
  fn divisor_modulus() -> Poly<Self::FieldElement> {
    Poly {
      y_coefficients: vec![Self::FieldElement::ZERO, Self::FieldElement::ONE],
      yx_coefficients: vec![],
      x_coefficients: vec![
        -Self::FieldElement::from(Self::B),
        -Self::FieldElement::from(Self::A),
        -Self::FieldElement::ONE,
      ],
      zero_coefficient: -Self::FieldElement::from(Self::C),
    }
  }

  /// Convert a point to its x and y coordinates.
  fn to_xy(point: Self) -> (Self::FieldElement, Self::FieldElement);
}

// Calculate the slope and intercept for two points.
fn slope_intercept<C: DivisorCurve>(a: C, b: C) -> (C::FieldElement, C::FieldElement) {
  let (ax, ay) = C::to_xy(a);
  let (bx, by) = C::to_xy(b);
  let slope = (by - ay) *
    Option::<C::FieldElement>::from((bx - ax).invert())
      .expect("trying to get slope/intercept of points sharing an x coordinate");
  let intercept = by - (slope * bx);
  debug_assert!(bool::from((ay - (slope * ax) - intercept).is_zero()));
  debug_assert!(bool::from((by - (slope * bx) - intercept).is_zero()));
  (slope, intercept)
}

// The line interpolating two points.
fn line<C: DivisorCurve>(a: C, mut b: C) -> Poly<C::FieldElement> {
  // If these are additive inverses, the line is 1 * x - x
  if (a + b) == C::identity() {
    let (ax, _) = C::to_xy(a);
    return Poly {
      y_coefficients: vec![],
      yx_coefficients: vec![],
      x_coefficients: vec![C::FieldElement::ONE],
      zero_coefficient: -ax,
    };
  }

  // If the points are equal, we use the line interpolating the sum of these points with identity.
  if a == b {
    b = -a.double();
  }

  let (slope, intercept) = slope_intercept::<C>(a, b);

  // y - (slope * x) - intercept
  Poly {
    y_coefficients: vec![C::FieldElement::ONE],
    yx_coefficients: vec![],
    x_coefficients: vec![-slope],
    zero_coefficient: -intercept,
  }
}

/// Create a divisor interpolating the following points.
///
/// Returns None if:
///   - No points were passed in
///   - The points don't sum to identity
///   - A passed in point was identity
#[allow(clippy::new_ret_no_self)]
pub fn new_divisor<C: DivisorCurve>(points: &[C]) -> Option<Poly<C::FieldElement>> {
  // A single point is either identity, or this doesn't sum to identity
  // Both cause us to return None
  if points.len() < 2 {
    None?;
  }
  if points.iter().sum::<C>() != C::identity() {
    None?;
  }

  // Create the initial set of divisors
  let mut divs = vec![];
  let mut iter = points.iter().copied();
  while let Some(a) = iter.next() {
    if a == C::identity() {
      None?;
    }

    let b = iter.next();
    if b == Some(C::identity()) {
      None?;
    }

    // Draw the line between those points
    divs.push((a + b.unwrap_or(C::identity()), line::<C>(a, b.unwrap_or(-a))));
  }

  let modulus = C::divisor_modulus();

  // Pair them off until only one remains
  while divs.len() > 1 {
    let mut next_divs = vec![];
    // If there's an odd amount of divisors, carry the odd one out to the next iteration
    if (divs.len() % 2) == 1 {
      next_divs.push(divs.pop().unwrap());
    }

    while let Some((a, a_div)) = divs.pop() {
      let (b, b_div) = divs.pop().unwrap();

      // Merge the two divisors
      let numerator = a_div.mul_mod(b_div, &modulus).mul_mod(line::<C>(a, b), &modulus);
      let denominator = line::<C>(a, -a).mul_mod(line::<C>(b, -b), &modulus);
      let (q, r) = numerator.div_rem(&denominator);
      assert_eq!(r, Poly::zero());

      next_divs.push((a + b, q));
    }

    divs = next_divs;
  }

  // Return the unified divisor
  Some(divs.remove(0).1)
}
