use rand_core::OsRng;

use group::{ff::Field, Group, Curve};
use pasta_curves::{
  arithmetic::{Coordinates, CurveAffine},
  Ep, Fp,
};

use crate::{DivisorCurve, Poly, new_divisor};

impl DivisorCurve for Ep {
  type FieldElement = Fp;

  const A: u64 = 0;
  const B: u64 = 0;
  const C: u64 = 5;

  fn to_xy(point: Self) -> (Self::FieldElement, Self::FieldElement) {
    Option::<Coordinates<_>>::from(point.to_affine().coordinates())
      .map(|coords| (*coords.x(), *coords.y()))
      .unwrap_or((Fp::ZERO, Fp::ZERO))
  }
}

type F = <Ep as DivisorCurve>::FieldElement;

#[test]
fn test_divisor() {
  for i in 1 ..= 255 {
    dbg!(i);

    // Select points
    let mut points = vec![];
    for _ in 0 .. i {
      points.push(Ep::random(&mut OsRng));
    }
    points.push(-points.iter().sum::<Ep>());

    // Create the divisor
    let divisor = new_divisor::<Ep>(&points).unwrap();

    // Decide challgenges
    let c0 = Ep::random(&mut OsRng);
    let c1 = Ep::random(&mut OsRng);
    let c2 = -(c0 + c1);
    let (slope, intercept) = crate::slope_intercept::<Ep>(c0, c1);

    // Perform the original check
    {
      let eval = |c| {
        let (x, y) = Ep::to_xy(c);
        divisor.eval(x, y)
      };

      let mut rhs = F::ONE;
      for point in &points {
        let (x, y) = Ep::to_xy(*point);
        rhs *= intercept - (y - (slope * x));
      }
      assert_eq!(eval(c0) * eval(c1) * eval(c2), rhs);
    }

    // Perform the Logarithmic derivative check
    {
      let dx_over_dz = {
        let dx = Poly {
          y_coefficients: vec![],
          yx_coefficients: vec![],
          x_coefficients: vec![F::ZERO, F::from(3)],
          zero_coefficient: F::from(<Ep as DivisorCurve>::A),
        };

        let dy = Poly {
          y_coefficients: vec![F::from(2)],
          yx_coefficients: vec![],
          x_coefficients: vec![],
          zero_coefficient: F::ZERO,
        };

        let dz = (dy.clone() * -slope) + &dx;

        // We want dx/dz, and dz/dx is equal to dy/dx - slope
        // Sagemath claims this, dy / dz, is the proper inverse
        (dy, dz)
      };

      {
        let sanity_eval = |c| {
          let (x, y) = Ep::to_xy(c);
          dx_over_dz.0.eval(x, y) * dx_over_dz.1.eval(x, y).invert().unwrap()
        };
        let sanity = sanity_eval(c0) + sanity_eval(c1) + sanity_eval(c2);
        // This verifies the dx/dz polynomial is correct
        assert_eq!(sanity, F::ZERO);
      }

      // Logarithmic derivative check
      let test = |divisor: Poly<_>| {
        let (dx, dy) = divisor.differentiate();

        let lhs = |c| {
          let (x, y) = Ep::to_xy(c);

          let n_0 = (F::from(3) * (x * x)) + F::from(<Ep as DivisorCurve>::A);
          let d_0 = (F::from(2) * y).invert().unwrap();
          let nd_0 = n_0 * d_0;

          let n_1 = dy.eval(x, y);
          let first = nd_0 * n_1;

          let second = dx.eval(x, y);

          let d_1 = divisor.eval(x, y);
          let fraction_1 = (first + second) * d_1.invert().unwrap();

          let fraction_2 = dx_over_dz.0.eval(x, y) * dx_over_dz.1.eval(x, y).invert().unwrap();
          fraction_1 * fraction_2
        };
        let lhs = lhs(c0) + lhs(c1) + lhs(c2);

        let mut rhs = F::ZERO;
        for point in &points {
          let (x, y) = <Ep as DivisorCurve>::to_xy(*point);
          rhs += (intercept - (y - (slope * x))).invert().unwrap();
        }

        assert_eq!(lhs, rhs);
      };
      // Test the divisor and the divisor with a normalized x coefficient
      test(divisor.clone());
      test(divisor.normalize_x_coefficient());
    }
  }
}

#[test]
fn test_same_point() {
  let mut points = vec![Ep::random(&mut OsRng)];
  points.push(points[0]);
  points.push(-points.iter().sum::<Ep>());

  let divisor = new_divisor::<Ep>(&points).unwrap();
  let eval = |c| {
    let (x, y) = Ep::to_xy(c);
    divisor.eval(x, y)
  };

  let c0 = Ep::random(&mut OsRng);
  let c1 = Ep::random(&mut OsRng);
  let c2 = -(c0 + c1);
  let (slope, intercept) = crate::slope_intercept::<Ep>(c0, c1);

  let mut rhs = F::ONE;
  for point in points {
    let (x, y) = Ep::to_xy(point);
    rhs *= intercept - (y - (slope * x));
  }
  assert_eq!(eval(c0) * eval(c1) * eval(c2), rhs);
}
