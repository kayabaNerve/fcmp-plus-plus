use rand_core::OsRng;

use group::{ff::Field, Group};
use pasta_curves::Ep;

use crate::{DivisorCurve, Poly, Divisor};

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

#[test]
fn test_divisor() {
  for i in 1 ..= 255 {
    if (i % 2) == 0 {
      continue;
    }
    dbg!("divisor", i);

    let mut points = vec![];
    for _ in 0 .. i {
      points.push(Ep::random(&mut OsRng));
    }
    points.push(-points.iter().sum::<Ep>());

    let divisor = Divisor::<Ep>::new(&points);

    let challenge = Ep::random(&mut OsRng);
    let (x, y) = Ep::to_xy(challenge);

    let mut rhs = F::ONE;
    for point in points {
      rhs *= x - Ep::to_xy(point).0;
    }
    assert_eq!(divisor.eval(x, y) * divisor.eval(x, -y), rhs);
  }
}

#[test]
fn test_same_point() {
  let mut points = vec![Ep::random(&mut OsRng)];
  points.push(points[0]);
  // Pad so there's an even number of points
  points.push(Ep::random(&mut OsRng));
  points.push(-points.iter().sum::<Ep>());

  let divisor = Divisor::<Ep>::new(&points);

  let challenge = Ep::random(&mut OsRng);
  let (x, y) = Ep::to_xy(challenge);

  let mut rhs = F::ONE;
  for point in points {
    rhs *= x - Ep::to_xy(point).0;
  }
  assert_eq!(divisor.eval(x, y) * divisor.eval(x, -y), rhs);
}

#[test]
fn test_differentation() {
  let random = || F::random(&mut OsRng);

  let input = Poly {
    y_coefficients: vec![random()],
    yx_coefficients: vec![vec![random()]],
    x_coefficients: vec![random(), random(), random()],
    zero_coefficient: random(),
  };
  let (diff_x, diff_y) = input.differentiate();
  assert_eq!(
    diff_x,
    Poly {
      y_coefficients: vec![input.yx_coefficients[0][0]],
      yx_coefficients: vec![],
      x_coefficients: vec![
        F::from(2) * input.x_coefficients[1],
        F::from(3) * input.x_coefficients[2]
      ],
      zero_coefficient: input.x_coefficients[0],
    }
  );
  assert_eq!(
    diff_y,
    Poly {
      y_coefficients: vec![],
      yx_coefficients: vec![],
      x_coefficients: vec![input.yx_coefficients[0][0]],
      zero_coefficient: input.y_coefficients[0],
    }
  );

  let input = Poly {
    y_coefficients: vec![random()],
    yx_coefficients: vec![vec![random(), random()]],
    x_coefficients: vec![random(), random(), random(), random()],
    zero_coefficient: random(),
  };
  let (diff_x, diff_y) = input.differentiate();
  assert_eq!(
    diff_x,
    Poly {
      y_coefficients: vec![input.yx_coefficients[0][0]],
      yx_coefficients: vec![vec![F::from(2) * input.yx_coefficients[0][1]]],
      x_coefficients: vec![
        F::from(2) * input.x_coefficients[1],
        F::from(3) * input.x_coefficients[2],
        F::from(4) * input.x_coefficients[3],
      ],
      zero_coefficient: input.x_coefficients[0],
    }
  );
  assert_eq!(
    diff_y,
    Poly {
      y_coefficients: vec![],
      yx_coefficients: vec![],
      x_coefficients: vec![input.yx_coefficients[0][0], input.yx_coefficients[0][1]],
      zero_coefficient: input.y_coefficients[0],
    }
  );
}

#[test]
fn test_log_deriv_eval() {
  for i in 0 .. 256 {
    if (i % 2) != 1 {
      continue;
    }
    dbg!("log_deriv_eval", i);

    let mut points = vec![];
    for _ in 0 .. i {
      points.push(Ep::random(&mut OsRng));
    }
    points.push(-points.iter().sum::<Ep>());
    let divisor = Divisor::<Ep>::new(&points);

    let challenge = Ep::random(&mut OsRng);

    // Classic check
    {
      let (x, y) = <Ep as DivisorCurve>::to_xy(challenge);
      let lhs = divisor.eval(x, y) * divisor.eval(x, -y);
      let mut rhs = F::ONE;
      for point in &points {
        rhs *= x - <Ep as DivisorCurve>::to_xy(*point).0;
      }
      assert_eq!(lhs, rhs);
    }

    let test = |divisor: Poly<_>| {
      let (x, y) = <Ep as DivisorCurve>::to_xy(challenge);

      // (dx(x, y) / D(x, y)) + (dy(x, y) * ((3x**2 + A) / 2y) / D(x, y)) =
      // eval of logarithmic derivative

      let log_deriv = {
        let (dx, dy) = divisor.differentiate();

        // Dz = Dx + (Dy * ((3*x^2 + A) / (2*y)))

        let dy_numerator = dy.clone() *
          Poly {
            y_coefficients: vec![],
            yx_coefficients: vec![],
            x_coefficients: vec![F::ZERO, F::from(3)],
            zero_coefficient: F::from(<Ep as DivisorCurve>::A),
          };

        let denominator = Poly {
          y_coefficients: vec![F::from(2)],
          yx_coefficients: vec![],
          x_coefficients: vec![],
          zero_coefficient: F::ZERO,
        };

        let numerator = (dx * denominator.clone()) + &dy_numerator;

        // Dz is numerator / denominator
        // Dz / D
        let denominator = denominator * divisor;

        let modulus = Poly {
          y_coefficients: vec![F::ZERO, F::ONE],
          yx_coefficients: vec![],
          x_coefficients: vec![-F::from(<Ep as DivisorCurve>::A), F::ZERO, -F::ONE],
          zero_coefficient: -F::from(<Ep as DivisorCurve>::B),
        };

        let numerator = numerator % &modulus;
        let denominator = denominator % &modulus;

        assert_eq!(numerator.y_coefficients.len(), 1);
        assert_eq!(denominator.y_coefficients.len(), 1);

        Divisor::<Ep> { numerator, denominator }
      };
      let lhs = (log_deriv.numerator.eval(x, y) *
        log_deriv.denominator.eval(x, y).invert().unwrap()) +
        (log_deriv.numerator.eval(x, -y) * log_deriv.denominator.eval(x, -y).invert().unwrap());

      let mut rhs = F::ZERO;
      for point in &points {
        rhs += (x - <Ep as DivisorCurve>::to_xy(*point).0).invert().unwrap();
      }

      assert_eq!(lhs, rhs);
    };
    test(divisor.clone());
    test(divisor.normalize_x_coefficient());
  }
}

#[test]
fn test_log_deriv_z_eval() {
  for i in 0 .. 256 {
    dbg!("log_deriv_z_eval", i);

    if (i % 2) != 1 {
      continue;
    }
    let mut points = vec![];
    for _ in 0 .. i {
      points.push(Ep::random(&mut OsRng));
    }
    points.push(-points.iter().sum::<Ep>());
    let divisor = Divisor::<Ep>::new(&points);

    let challenge_0 = Ep::random(&mut OsRng);
    let challenge_1 = Ep::random(&mut OsRng);
    let challenge_2 = -(challenge_0 + challenge_1);
    let (slope, intercept) = crate::slope_intercept::<Ep>(challenge_0, challenge_1);
    // Z = y - slope x
    // z = intercept

    let c0_xy = <Ep as DivisorCurve>::to_xy(challenge_0);
    let c1_xy = <Ep as DivisorCurve>::to_xy(challenge_1);
    let c2_xy = <Ep as DivisorCurve>::to_xy(challenge_2);

    // Classic check
    {
      let lhs = divisor.eval(c0_xy.0, c0_xy.1) *
        divisor.eval(c1_xy.0, c1_xy.1) *
        divisor.eval(c2_xy.0, c2_xy.1);
      let mut rhs = F::ONE;
      for point in &points {
        let (x, y) = <Ep as DivisorCurve>::to_xy(*point);
        rhs *= intercept - (y - (slope * x));
      }
      assert_eq!(lhs, rhs);
    }

    let dx_slope_over_dz = {
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

      Divisor::<Ep> { numerator: dy, denominator: dz }
    };

    {
      let sanity = (dx_slope_over_dz.numerator.eval(c0_xy.0, c0_xy.1) *
        dx_slope_over_dz.denominator.eval(c0_xy.0, c0_xy.1).invert().unwrap()) +
        (dx_slope_over_dz.numerator.eval(c1_xy.0, c1_xy.1) *
          dx_slope_over_dz.denominator.eval(c1_xy.0, c1_xy.1).invert().unwrap()) +
        (dx_slope_over_dz.numerator.eval(c2_xy.0, c2_xy.1) *
          dx_slope_over_dz.denominator.eval(c2_xy.0, c2_xy.1).invert().unwrap());
      assert_eq!(sanity, F::ZERO);
    }

    // Logarithmic derivative check
    let test = |divisor: Poly<_>| {
      let (dx, dy) = divisor.differentiate();

      let lhs = |c: (F, F)| {
        let n_0 = (F::from(3) * (c.0 * c.0)) + F::from(<Ep as DivisorCurve>::A);
        let d_0 = (F::from(2) * c.1).invert().unwrap();
        let nd_0 = n_0 * d_0;

        let n_1 = dy.eval(c.0, c.1);
        let first = nd_0 * n_1;

        let second = dx.eval(c.0, c.1);

        let d_1 = divisor.eval(c.0, c.1);
        let fraction_1 = (first + second) * d_1.invert().unwrap();

        let fraction_2 = dx_slope_over_dz.numerator.eval(c.0, c.1) *
          dx_slope_over_dz.denominator.eval(c.0, c.1).invert().unwrap();
        fraction_1 * fraction_2
      };
      let lhs = lhs(c0_xy) + lhs(c1_xy) + lhs(c2_xy);

      let mut rhs = F::ZERO;
      for point in &points {
        let (x, y) = <Ep as DivisorCurve>::to_xy(*point);
        rhs += (intercept - (y - (slope * x))).invert().unwrap();
      }

      assert_eq!(lhs, rhs);
    };
    test(divisor.clone());
    test(divisor.normalize_x_coefficient());
  }
}
