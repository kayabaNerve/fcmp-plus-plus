use group::{
  ff::{Field, PrimeField},
  Group, GroupEncoding,
};
use dalek_ff_group::FieldElement;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum TorsionCheck {
  /// Invalid encoding or low order
  Invalid,
  /// Torsioned
  Torsioned,
  /// Free of torsion
  TorsionFree,
}

fn torsion_check_vartime(point: [u8; 32]) -> TorsionCheck {
  // These are constants of the elliptic curve
  let a = -FieldElement::ONE;
  let D = -FieldElement::from(121665u64) * FieldElement::from(121666u64).invert().unwrap();
  let a_minus_D = a - D;
  let A = (a + D).double();
  let B = a_minus_D.square();
  let Ap = -A.double();
  let Bp = A.square() - B.double().double();
  // let As = -Ap.double();
  // let Bs = Ap.square() - Bp.double().double();

  // Decompress the point
  let (edwards_x, edwards_y) = {
    // Extract the y coordinate from the compressed point
    let x_is_odd = point[31] >> 7;
    let mut edwards_y = point;
    edwards_y[31] &= (1 << 7) - 1;
    let Some(edwards_y) = Option::<FieldElement>::from(FieldElement::from_repr(edwards_y)) else {
      // Invalid y coordinate
      return TorsionCheck::Invalid;
    };

    // Recover the x coordinate
    let edwards_y_sq = edwards_y * edwards_y;
    let Some(denominator) =
      Option::<FieldElement>::from(((D * edwards_y_sq) + FieldElement::ONE).invert())
    else {
      // Off-curve point
      return TorsionCheck::Invalid;
    };
    let Some(mut edwards_x) =
      Option::<FieldElement>::from(((edwards_y_sq - FieldElement::ONE) * denominator).sqrt())
    else {
      // Off-curve point
      return TorsionCheck::Invalid;
    };
    if u8::from(bool::from(edwards_x.is_odd())) != x_is_odd {
      edwards_x = -edwards_x;
    }
    (edwards_x, edwards_y)
  };

  // Check the point isn't low-order (which is exceptional or will resolve as identity, which we
  // ban in this context)
  {
    // The above is the Edwards x and y, enabling creating an Edwards point
    // Dalek doesn't let us specify the x/y coordinates and forces us to decompress the point again
    let point = curve25519_dalek::edwards::CompressedEdwardsY(point)
      .decompress()
      .expect("we decompressed what dalek refused to decompress");
    if bool::from(point.mul_by_cofactor().is_identity()) {
      // Low order
      return TorsionCheck::Invalid;
    }
  }

  let ed_to_wei = |edwards_x: FieldElement, edwards_y: FieldElement| {
    let edwards_y_plus_one = FieldElement::ONE + edwards_y;
    let one_minus_edwards_y = FieldElement::ONE - edwards_y;
    let u = a_minus_D * edwards_y_plus_one * one_minus_edwards_y.invert().unwrap();
    let w = edwards_x.invert().unwrap().double();
    assert_eq!(u * w.square(), u.square() + (A * u) + B, "wei mapping wrong");
    (u, w)
  };

  let wei_to_ed = |u: FieldElement, w: FieldElement| {
    let edwards_x = w.invert().unwrap().double();
    let edwards_y_intermediary = u * a_minus_D.invert().unwrap();
    let edwards_y = (edwards_y_intermediary - FieldElement::ONE) *
      (edwards_y_intermediary + FieldElement::ONE).invert().unwrap();
    (edwards_x, edwards_y)
  };

  let (u, w) = ed_to_wei(edwards_x, edwards_y);
  assert_eq!(wei_to_ed(u, w), (edwards_x, edwards_y), "ed mapping wrong");

  let iso = |u: FieldElement, w: FieldElement| {
    (u * FieldElement::from(4u64).invert().unwrap(), w * FieldElement::from(2u64).invert().unwrap())
  };
  let psi1 = |u: FieldElement, w: FieldElement| {
    (w.square(), -(u - (B * u.invert().unwrap())) * w.invert().unwrap())
  };
  let psi2 = |u: FieldElement, w: FieldElement| {
    (w.square(), -(u - (Bp * u.invert().unwrap())) * w.invert().unwrap())
  };

  let inv_iso = |u: FieldElement, w: FieldElement| {
    let (u_res, w_res) = (u.double().double(), w.double());
    assert_eq!(iso(u_res, w_res), (u, w));
    (u_res, w_res)
  };
  let inv_psi1 = |u: FieldElement, w: FieldElement| {
    let w_res = Option::<FieldElement>::from(u.sqrt()).unwrap();
    let u_res = (u - A - (w_res * w)) * FieldElement::from(2u64).invert().unwrap();
    assert_eq!(psi1(u_res, w_res), (u, w));
    (u_res, w_res)
  };
  let inv_psi2 = |u: FieldElement, w: FieldElement| {
    let mut w_res = Option::<FieldElement>::from(u.sqrt())?;
    let mut u_res = (u - Ap - (w_res * w)) * FieldElement::from(2u64).invert().unwrap();
    if bool::from(u_res.sqrt().is_none()) {
      w_res = -w_res;
      u_res = Bp * u_res.invert().unwrap();
    }
    assert_eq!(psi2(u_res, w_res), (u, w));
    Some((u_res, w_res))
  };

  let (u, w) = inv_iso(u, w);
  let Some((u, w)) = inv_psi2(u, w) else { return TorsionCheck::Torsioned };
  let (u, w) = inv_psi1(u, w);

  let (u, w) = inv_iso(u, w);
  let Some((u, w)) = inv_psi2(u, w) else { return TorsionCheck::Torsioned };
  let (u, w) = inv_psi1(u, w);

  let (u, w) = inv_iso(u, w);
  let Some(_) = inv_psi2(u, w) else { return TorsionCheck::Torsioned };

  TorsionCheck::TorsionFree
}

#[test]
fn test_torsion_check_vartime() {
  for point in curve25519_dalek::constants::EIGHT_TORSION {
    assert_eq!(torsion_check_vartime(point.to_bytes()), TorsionCheck::Invalid);
  }

  {
    let torsion_free =
      curve25519_dalek::EdwardsPoint::random(&mut rand_core::OsRng).mul_by_cofactor();
    for torsion in &curve25519_dalek::constants::EIGHT_TORSION[1 ..] {
      assert_eq!(
        torsion_check_vartime((torsion_free + torsion).to_bytes()),
        TorsionCheck::Torsioned
      );
    }
  }

  {
    let torsion_free =
      curve25519_dalek::EdwardsPoint::random(&mut rand_core::OsRng).mul_by_cofactor();
    assert_eq!(torsion_check_vartime(torsion_free.to_bytes()), TorsionCheck::TorsionFree);
  }
}
