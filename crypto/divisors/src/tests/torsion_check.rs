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

/*
  https://eprint.iacr.org/2022/1164.pdf

  Implementation derived from Thomas Pornin's crrl.

  MIT License

  Copyright (c) 2022 Thomas Pornin

  Permission is hereby granted, free of charge, to any person obtaining a copy
  of this software and associated documentation files (the "Software"), to deal
  in the Software without restriction, including without limitation the rights
  to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
  copies of the Software, and to permit persons to whom the Software is
  furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in all
  copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.
*/
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
  let mod_5_8 = (-FieldElement::from(5u64)) * FieldElement::from(8u64).invert().unwrap();
  let sqrt_m1 = (-FieldElement::ONE).sqrt().unwrap();
  let neg_sqrt_2b = -Bp.double().sqrt().unwrap();
  // This is used to halve elements. A dedicated halving function is likely better
  let inv_two = FieldElement::from(2u64).invert().unwrap();

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
    let z = FieldElement::ONE;
    let z_plus_edwards_y = z + edwards_y;
    let z_minus_edwards_y = z - edwards_y;
    let e = edwards_x * z_minus_edwards_y;
    let u = a_minus_D * z_plus_edwards_y * edwards_x * e;
    // This is actually z * (z - y), yet our z=1
    let w = z_minus_edwards_y.double();
    assert_eq!(
      u * w.square(),
      u.square() + ((A * u) * e.square()) + (B * e.square().square()),
      "wei mapping wrong"
    );
    (e, u, w)
  };

  /*
  let wei_to_ed = |e: FieldElement, u: FieldElement, w: FieldElement| {
    let edwards_x = w.invert().unwrap().double();
    let edwards_y_intermediary = u * a_minus_D.invert().unwrap();
    let edwards_y = (edwards_y_intermediary - FieldElement::ONE) *
      (edwards_y_intermediary + FieldElement::ONE).invert().unwrap();
    (edwards_x, edwards_y)
  };
  */

  let (mut e, u, w) = ed_to_wei(edwards_x, edwards_y);
  // assert_eq!(wei_to_ed(e, u, w), (edwards_x, edwards_y), "ed mapping wrong");

  let iso = |u: FieldElement, w: FieldElement| {
    (u * FieldElement::from(4u64).invert().unwrap(), w * inv_two)
  };
  /*
  let psi1 = |u: FieldElement, w: FieldElement| {
    (w.square(), -(u - (B * u.invert().unwrap())) * w.invert().unwrap())
  };
  let psi2 = |u: FieldElement, w: FieldElement| {
    (w.square(), -(u - (Bp * u.invert().unwrap())) * w.invert().unwrap())
  };
  */

  let inv_iso = |u: FieldElement, w: FieldElement| {
    let (u_res, w_res) = (u.double().double(), w.double());
    assert_eq!(iso(u_res, w_res), (u, w));
    (u_res, w_res)
  };
  let sqrt_ext = |x: FieldElement| -> (FieldElement, bool) {
    let two_x = x.double();
    let b = two_x.pow(mod_5_8);
    let mut c = two_x * b.square();
    if (c == FieldElement::ONE) || (c == -FieldElement::ONE) {
      c = FieldElement::from(3u64);
    }
    let mut y = x * b * (c - FieldElement::ONE);

    if bool::from(y.is_odd()) {
      y = -y;
    }
    (y, y.square() == x)
  };
  let inv_psi1 = |e: &mut FieldElement, u: FieldElement, mut w: FieldElement| {
    let (mut tt, cc) = sqrt_ext(u);
    let mut w_res = tt;
    if (!cc) && (tt.square() == -u.double()) {
      tt *= sqrt_m1;
    }
    if !cc {
      w = w * tt;
      w_res = neg_sqrt_2b * e.square();
      *e *= tt;
    }
    let u_res = (w_res.square() - (A * e.square()) - (w_res * w)) * inv_two;
    (u_res, w_res)
  };
  let inv_psi2 = |e: FieldElement, u: FieldElement, w: FieldElement| {
    let w_res = Option::<FieldElement>::from(u.sqrt())?;
    let u_res = (u - (Ap * e.square()) - (w_res * w)) * inv_two;
    /*
    //assert_eq!(u * w.square(), u.square() + (u * Ap * e.square()) + (Bp * e.square().square()));
    if bool::from(u_res.sqrt().is_none()) {
      w_res = -w_res;
      u_res = Bp * u_res.invert().unwrap();
    }
    */
    //assert_eq!(psi2(u_res, w_res), (u, w));
    Some((u_res, w_res))
  };

  assert_eq!(
    u * w.square(),
    u.square() + ((A * u) * e.square()) + (B * e.square().square()),
    "loop invariant broken"
  );

  let (u, w) = inv_iso(u, w);
  let Some((u, w)) = inv_psi2(e, u, w) else { return TorsionCheck::Torsioned };
  let (u, w) = inv_psi1(&mut e, u, w);

  assert_eq!(
    u * w.square(),
    u.square() + ((A * u) * e.square()) + (B * e.square().square()),
    "loop invariant broken"
  );

  let (u, w) = inv_iso(u, w);
  let Some((u, w)) = inv_psi2(e, u, w) else { return TorsionCheck::Torsioned };
  let (u, w) = inv_psi1(&mut e, u, w);

  assert_eq!(
    u * w.square(),
    u.square() + ((A * u) * e.square()) + (B * e.square().square()),
    "loop invariant broken"
  );

  let (u, w) = inv_iso(u, w);
  // This can be optimized to checking if u is square via its legendre symbol
  let Some(_) = inv_psi2(e, u, w) else { return TorsionCheck::Torsioned };

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
