#![allow(non_snake_case)]

use group::{
ff::{Field, PrimeField},
Group,
};

mod poly;
pub use poly::*;

#[cfg(test)]
pub(crate) mod tests;

pub trait DivisorCurve: Group {
  type FieldElement: PrimeField;

  const A: u64;
  const B: u64;

  fn to_xy(point: Self) -> (Self::FieldElement, Self::FieldElement);
}

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

/// Constructor of a divisor (represented via a Poly) for a set of elliptic curve point.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Divisor<C: DivisorCurve> {
  pub numerator: Poly<C::FieldElement>,
  pub denominator: Poly<C::FieldElement>,
}

impl<C: DivisorCurve> Divisor<C> {
  // TODO: Is this complete? Or will it return garbage in some cases?
  fn line(a: C, mut b: C) -> Self {
    let (ax, _) = C::to_xy(a);

    if (a + b) == C::identity() {
      return Divisor {
        numerator: Poly {
          y_coefficients: vec![],
          yx_coefficients: vec![],
          x_coefficients: vec![C::FieldElement::ONE],
          zero_coefficient: -ax,
        },
        denominator: Poly {
          y_coefficients: vec![],
          yx_coefficients: vec![],
          x_coefficients: vec![],
          zero_coefficient: C::FieldElement::ONE,
        },
      };
    }

    if a == b {
      b = -a.double();
    }

    let (slope, intercept) = slope_intercept::<C>(a, b);

    // y - (slope * x) - intercept
    Divisor {
      numerator: Poly {
        y_coefficients: vec![C::FieldElement::ONE],
        yx_coefficients: vec![],
        x_coefficients: vec![-slope],
        zero_coefficient: -intercept,
      },
      denominator: Poly {
        y_coefficients: vec![],
        yx_coefficients: vec![],
        x_coefficients: vec![],
        zero_coefficient: C::FieldElement::ONE,
      },
    }
  }

  fn mul(self, other: Self, modulus: &Poly<C::FieldElement>) -> Self {
    let Divisor { numerator, denominator } = self;
    Self {
      numerator: numerator.mul_mod(other.numerator, modulus),
      denominator: denominator.mul_mod(other.denominator, modulus),
    }
  }

  fn div(self, other: Self, modulus: &Poly<C::FieldElement>) -> Self {
    let Divisor { numerator, denominator } = self;
    Self {
      numerator: numerator.mul_mod(other.denominator, modulus),
      denominator: denominator.mul_mod(other.numerator, modulus),
    }
  }

  /// Create a divisor interpolating the following points.
  #[allow(clippy::new_ret_no_self)]
  pub fn new(points: &[C]) -> Poly<C::FieldElement> {
    assert!(points.len() > 1);
    assert_eq!(points.len() % 2, 0); // TODO: Support odd numbers of points
    assert_eq!(points.iter().sum::<C>(), C::identity());

    let mut divs = vec![];
    let mut iter = points.iter().copied();
    while let Some(a) = iter.next() {
      let b = iter.next();

      assert!(a != C::identity());
      if let Some(b) = b {
        assert!(b != C::identity());
      }

      divs.push((a + b.unwrap_or(C::identity()), Self::line(a, b.unwrap_or(-a))));
    }

    // y^2 - x^3 - Ax - B
    let modulus = Poly {
      y_coefficients: vec![C::FieldElement::ZERO, C::FieldElement::ONE],
      yx_coefficients: vec![],
      x_coefficients: vec![
        -C::FieldElement::from(C::A),
        C::FieldElement::ZERO,
        -C::FieldElement::ONE,
      ],
      zero_coefficient: -C::FieldElement::from(C::B),
    };

    while divs.len() > 1 {
      let mut next_divs = vec![];
      if (divs.len() % 2) == 1 {
        next_divs.push(divs.pop().unwrap());
      }

      while let Some((a, a_div)) = divs.pop() {
        let (b, b_div) = divs.pop().unwrap();

        next_divs.push((
          a + b,
          a_div
            .mul(b_div, &modulus)
            .mul(Self::line(a, b), &modulus)
            .div(Self::line(a, -a).mul(Self::line(b, -b), &modulus), &modulus),
        ));
      }

      divs = next_divs;
    }

    let Divisor { numerator, denominator } = divs.remove(0).1;
    let (res, rem) = numerator.div_rem(&denominator);
    debug_assert_eq!(rem, Poly::zero());

    // This has to be asserted in circuit
    assert_eq!(*res.x_coefficients.last().unwrap(), C::FieldElement::ONE);

    res
  }
}

#[cfg(test)]
mod pasta {
  use group::{ff::Field, Curve};
  use pasta_curves::{arithmetic::{Coordinates, CurveAffine}, Ep, Fp};

  use crate::DivisorCurve;

  impl DivisorCurve for Ep {
    type FieldElement = Fp;

    const A: u64 = 0;
    const B: u64 = 5;

    fn to_xy(point: Self) -> (Self::FieldElement, Self::FieldElement) {
      Option::<Coordinates<_>>::from(point.to_affine().coordinates())
        .map(|coords| (*coords.x(), *coords.y()))
        .unwrap_or((Fp::ZERO, Fp::ZERO))
    }
  }
}
