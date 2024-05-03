use rand_core::OsRng;

use group::{
  ff::{Field, PrimeField},
  Group, GroupEncoding, Curve,
};
use dalek_ff_group::EdwardsPoint;
use pasta_curves::{
  arithmetic::{Coordinates, CurveAffine},
  Ep, Fp,
};

use crate::{DivisorCurve, Poly, new_divisor};

impl DivisorCurve for Ep {
  type FieldElement = Fp;

  fn a() -> Self::FieldElement {
    Self::FieldElement::ZERO
  }
  fn b() -> Self::FieldElement {
    Self::FieldElement::from(5u64)
  }

  fn to_xy(point: Self) -> (Self::FieldElement, Self::FieldElement) {
    Option::<Coordinates<_>>::from(point.to_affine().coordinates())
      .map(|coords| (*coords.x(), *coords.y()))
      .unwrap_or((Fp::ZERO, Fp::ZERO))
  }
}

impl DivisorCurve for EdwardsPoint {
  type FieldElement = dalek_ff_group::FieldElement;

  // Wei25519 a/b
  // https://www.ietf.org/archive/id/draft-ietf-lwig-curve-representations-02.pdf E.3
  fn a() -> Self::FieldElement {
    let mut be_bytes =
      hex::decode("2aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa984914a144").unwrap();
    be_bytes.reverse();
    let le_bytes = be_bytes;
    Self::FieldElement::from_repr(le_bytes.try_into().unwrap()).unwrap()
  }
  fn b() -> Self::FieldElement {
    let mut be_bytes =
      hex::decode("7b425ed097b425ed097b425ed097b425ed097b425ed097b4260b5e9c7710c864").unwrap();
    be_bytes.reverse();
    let le_bytes = be_bytes;

    Self::FieldElement::from_repr(le_bytes.try_into().unwrap()).unwrap()
  }

  // https://www.ietf.org/archive/id/draft-ietf-lwig-curve-representations-02.pdf E.2
  fn to_xy(point: Self) -> (Self::FieldElement, Self::FieldElement) {
    // Extract the y coordinate from the compressed point
    let mut edwards_y = point.to_bytes();
    let x_is_odd = edwards_y[31] >> 7;
    edwards_y[31] &= (1 << 7) - 1;
    let edwards_y = Self::FieldElement::from_repr(edwards_y).unwrap();

    // Recover the x coordinate
    let edwards_y_sq = edwards_y * edwards_y;
    let D =
      -Self::FieldElement::from(121665u64) * Self::FieldElement::from(121666u64).invert().unwrap();
    let mut edwards_x = ((edwards_y_sq - Self::FieldElement::ONE) *
      ((D * edwards_y_sq) + Self::FieldElement::ONE).invert().unwrap())
    .sqrt()
    .unwrap();
    if u8::from(bool::from(edwards_x.is_odd())) != x_is_odd {
      edwards_x = -edwards_x;
    }

    // Calculate the x and y coordinates for Wei25519
    let edwards_y_plus_one = Self::FieldElement::ONE + edwards_y;
    let one_minus_edwards_y = Self::FieldElement::ONE - edwards_y;
    let wei_x = (edwards_y_plus_one * one_minus_edwards_y.invert().unwrap()) +
      (Self::FieldElement::from(486662u64) * Self::FieldElement::from(3u64).invert().unwrap());
    let c =
      (-(Self::FieldElement::from(486662u64) + Self::FieldElement::from(2u64))).sqrt().unwrap();
    let wei_y = c * edwards_y_plus_one * (one_minus_edwards_y * edwards_x).invert().unwrap();
    (wei_x, wei_y)
  }
}

fn test_divisor<C: DivisorCurve>() {
  for i in 1 ..= 255 {
    println!("Test iteration {i}");

    // Select points
    let mut points = vec![];
    for _ in 0 .. i {
      points.push(C::random(&mut OsRng));
    }
    points.push(-points.iter().sum::<C>());
    println!("Points {}", points.len());

    // Create the divisor
    let divisor = new_divisor::<C>(&points).unwrap();

    // For a divisor interpolating 256 points, as one does when interpreting a 255-bit discrete log
    // with the result of its scalar multiplication against a fixed generator, the lengths of the
    // yx/x coefficients shouldn't supersede the following bounds
    assert!((divisor.yx_coefficients.first().unwrap_or(&vec![]).len()) <= 126);
    assert!((divisor.x_coefficients.len() - 1) <= 127);
    assert!(
      (1 + divisor.yx_coefficients.first().unwrap_or(&vec![]).len() +
        (divisor.x_coefficients.len() - 1) +
        1) <=
        255
    );

    // Decide challgenges
    let c0 = C::random(&mut OsRng);
    let c1 = C::random(&mut OsRng);
    let c2 = -(c0 + c1);
    let (slope, intercept) = crate::slope_intercept::<C>(c0, c1);

    // Perform the original check
    {
      let eval = |c| {
        let (x, y) = C::to_xy(c);
        divisor.eval(x, y)
      };

      let mut rhs = C::FieldElement::ONE;
      for point in &points {
        let (x, y) = C::to_xy(*point);
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
          x_coefficients: vec![C::FieldElement::ZERO, C::FieldElement::from(3)],
          zero_coefficient: C::a(),
        };

        let dy = Poly {
          y_coefficients: vec![C::FieldElement::from(2)],
          yx_coefficients: vec![],
          x_coefficients: vec![],
          zero_coefficient: C::FieldElement::ZERO,
        };

        let dz = (dy.clone() * -slope) + &dx;

        // We want dx/dz, and dz/dx is equal to dy/dx - slope
        // Sagemath claims this, dy / dz, is the proper inverse
        (dy, dz)
      };

      {
        let sanity_eval = |c| {
          let (x, y) = C::to_xy(c);
          dx_over_dz.0.eval(x, y) * dx_over_dz.1.eval(x, y).invert().unwrap()
        };
        let sanity = sanity_eval(c0) + sanity_eval(c1) + sanity_eval(c2);
        // This verifies the dx/dz polynomial is correct
        assert_eq!(sanity, C::FieldElement::ZERO);
      }

      // Logarithmic derivative check
      let test = |divisor: Poly<_>| {
        let (dx, dy) = divisor.differentiate();

        let lhs = |c| {
          let (x, y) = C::to_xy(c);

          let n_0 = (C::FieldElement::from(3) * (x * x)) + C::a();
          let d_0 = (C::FieldElement::from(2) * y).invert().unwrap();
          let p_0_n_0 = n_0 * d_0;

          let n_1 = dy.eval(x, y);
          let first = p_0_n_0 * n_1;

          let second = dx.eval(x, y);

          let d_1 = divisor.eval(x, y);

          let fraction_1_n = first + second;
          let fraction_1_d = d_1;

          let fraction_2_n = dx_over_dz.0.eval(x, y);
          let fraction_2_d = dx_over_dz.1.eval(x, y);

          fraction_1_n * fraction_2_n * (fraction_1_d * fraction_2_d).invert().unwrap()
        };
        let lhs = lhs(c0) + lhs(c1) + lhs(c2);

        let mut rhs = C::FieldElement::ZERO;
        for point in &points {
          let (x, y) = <C as DivisorCurve>::to_xy(*point);
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

fn test_same_point<C: DivisorCurve>() {
  let mut points = vec![C::random(&mut OsRng)];
  points.push(points[0]);
  points.push(-points.iter().sum::<C>());

  let divisor = new_divisor::<C>(&points).unwrap();
  let eval = |c| {
    let (x, y) = C::to_xy(c);
    divisor.eval(x, y)
  };

  let c0 = C::random(&mut OsRng);
  let c1 = C::random(&mut OsRng);
  let c2 = -(c0 + c1);
  let (slope, intercept) = crate::slope_intercept::<C>(c0, c1);

  let mut rhs = <C as DivisorCurve>::FieldElement::ONE;
  for point in points {
    let (x, y) = C::to_xy(point);
    rhs *= intercept - (y - (slope * x));
  }
  assert_eq!(eval(c0) * eval(c1) * eval(c2), rhs);
}

#[test]
fn test_divisor_pallas() {
  test_divisor::<Ep>();
  test_same_point::<Ep>();
}

#[test]
fn test_divisor_ed25519() {
  // Since we're implementing Wei25519 ourselves, check the isomorphism works as expected
  {
    let incomplete_add = |p1, p2| {
      let (x1, y1) = EdwardsPoint::to_xy(p1);
      let (x2, y2) = EdwardsPoint::to_xy(p2);

      // mmadd-1998-cmo
      let u = y2 - y1;
      let uu = u * u;
      let v = x2 - x1;
      let vv = v * v;
      let vvv = v * vv;
      let R = vv * x1;
      let A = uu - vvv - R.double();
      let x3 = v * A;
      let y3 = (u * (R - A)) - (vvv * y1);
      let z3 = vvv;

      // Normalize from XYZ to XY
      let x3 = x3 * z3.invert().unwrap();
      let y3 = y3 * z3.invert().unwrap();

      // Edwards addition -> Wei25519 coordinates should be equivalent to Wei25519 addition
      assert_eq!(EdwardsPoint::to_xy(p1 + p2), (x3, y3));
    };

    for _ in 0 .. 256 {
      incomplete_add(EdwardsPoint::random(&mut OsRng), EdwardsPoint::random(&mut OsRng));
    }
  }

  test_divisor::<EdwardsPoint>();
  test_same_point::<EdwardsPoint>();
}
