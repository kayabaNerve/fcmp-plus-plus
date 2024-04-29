use group::ff::Field;
use pasta_curves::Ep;

use crate::{DivisorCurve, Poly};

type F = <Ep as DivisorCurve>::FieldElement;

#[test]
fn test_poly() {
  let zero = F::ZERO;
  let one = F::ONE;

  {
    let mut poly = Poly::zero();
    poly.y_coefficients = vec![zero, one];

    let mut modulus = Poly::zero();
    modulus.y_coefficients = vec![one];
    assert_eq!(poly % &modulus, Poly::zero());
  }

  {
    let mut poly = Poly::zero();
    poly.y_coefficients = vec![zero, one];

    let mut squared = Poly::zero();
    squared.y_coefficients = vec![zero, zero, zero, one];
    assert_eq!(poly.clone() * poly.clone(), squared);
  }

  {
    let mut a = Poly::zero();
    a.zero_coefficient = F::from(2u64);

    let mut b = Poly::zero();
    b.zero_coefficient = F::from(3u64);

    let mut res = Poly::zero();
    res.zero_coefficient = F::from(6u64);
    assert_eq!(a.clone() * b.clone(), res);

    b.y_coefficients = vec![F::from(4u64)];
    res.y_coefficients = vec![F::from(8u64)];
    assert_eq!(a.clone() * b.clone(), res);
    assert_eq!(b.clone() * a.clone(), res);

    a.x_coefficients = vec![F::from(5u64)];
    res.x_coefficients = vec![F::from(15u64)];
    res.yx_coefficients = vec![vec![F::from(20u64)]];
    assert_eq!(a.clone() * b.clone(), res);
    assert_eq!(b * a.clone(), res);

    // res is now 20xy + 8*y + 15*x + 6
    // res ** 2 =
    //   400*x^2*y^2 + 320*x*y^2 + 64*y^2 + 600*x^2*y + 480*x*y + 96*y + 225*x^2 + 180*x + 36

    let mut squared = Poly::zero();
    squared.y_coefficients = vec![F::from(96u64), F::from(64u64)];
    squared.yx_coefficients =
      vec![vec![F::from(480u64), F::from(600u64)], vec![F::from(320u64), F::from(400u64)]];
    squared.x_coefficients = vec![F::from(180u64), F::from(225u64)];
    squared.zero_coefficient = F::from(36u64);
    assert_eq!(res.clone() * res, squared);
  }
}
