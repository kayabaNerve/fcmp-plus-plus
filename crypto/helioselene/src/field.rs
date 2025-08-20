#![allow(clippy::needless_range_loop)]

use core::{
  iter::{Product, Sum},
  ops::*,
};

use subtle::*;
use zeroize::{DefaultIsZeroes, Zeroize};

use rand_core::RngCore;

use crypto_bigint::{Encoding, Limb, U128, U256};

use group::ff::{Field, FieldBits, PrimeField, PrimeFieldBits};

/// The field novel to Helios/Selene.
#[derive(Clone, Copy, PartialEq, Eq, Default, Debug)]
#[repr(C)]
pub struct HelioseleneField(pub(crate) U256);

/// The modulus of the field.
const MODULUS: U256 =
  U256::from_be_hex("7fffffffffffffffffffffffffffffffbf7f782cb7656b586eb6d2727927c79f");
/// The distance between the modulus and 2**255.
const MODULUS_255_DISTANCE: U128 = U128::from_le_hex("6138d8868d2d4991a7949a48d3878040");
/// Twice the distance from the modulus to 2**255.
const TWO_MODULUS_255_DISTANCE: U128 = U128::from_le_hex("c270b00d1b5b92224f293591a60f0181");
/*
/// The modulus, minus two, as used for calculating modular inverses.
const MODULUS_MINUS_TWO: HelioseleneField = HelioseleneField(U256::from_be_hex(
  "7fffffffffffffffffffffffffffffffbf7f782cb7656b586eb6d2727927c79d",
));
*/
/// The modulus, plus one, divided by four, as used for calculating square roots.
const MODULUS_PLUS_ONE_DIV_FOUR: HelioseleneField = HelioseleneField(U256::from_le_hex(
  "e8f1499e9cb4ad1bd65ad92d0bdedfefffffffffffffffffffffffffffffff1f",
));

impl From<u8> for HelioseleneField {
  fn from(a: u8) -> HelioseleneField {
    HelioseleneField(U256::from(a))
  }
}
impl From<u16> for HelioseleneField {
  fn from(a: u16) -> HelioseleneField {
    HelioseleneField(U256::from(a))
  }
}
impl From<u32> for HelioseleneField {
  fn from(a: u32) -> HelioseleneField {
    HelioseleneField(U256::from(a))
  }
}
impl From<u64> for HelioseleneField {
  fn from(a: u64) -> HelioseleneField {
    HelioseleneField(U256::from(a))
  }
}

impl DefaultIsZeroes for HelioseleneField {}

impl ConstantTimeEq for HelioseleneField {
  #[inline(always)]
  fn ct_eq(&self, b: &Self) -> Choice {
    self.0.ct_eq(&b.0)
  }
}

impl ConditionallySelectable for HelioseleneField {
  #[inline(always)]
  fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
    Self(<_>::conditional_select(&a.0, &b.0, choice))
  }
}

// Perform an add with carry, bounding the overflow to be zero or one.
#[inline(always)]
fn add_with_bounded_overflow(a: Limb, b: Limb, c: Limb) -> (Limb, Limb) {
  let (limb, carry1) = a.0.overflowing_add(b.0);
  let (limb, carry2) = limb.overflowing_add(c.0);
  (Limb(limb), Limb((carry1 | carry2) as _))
}

// Perform a sub with underflow, bounding the underflow to be zero or one.
//
// Unlike `sbb`, this returns `0` or `1`, not `0` or `Limb::MAX`.
#[inline(always)]
fn sub_with_bounded_overflow(a: Limb, b: Limb, c: Limb) -> (Limb, Limb) {
  let (limb, borrow1) = a.0.overflowing_sub(b.0);
  let (limb, borrow2) = limb.overflowing_sub(c.0);
  (Limb(limb), Limb((borrow1 | borrow2) as _))
}

/// Subtract a value (`b`) from another value (`a`).
///
/// Returns `(result, 0)` if successful, or  `(wrapped value, 255)` otherwise.
#[inline(always)]
fn sub_value(a: U256, b: U256) -> (U256, Limb) {
  a.sbb(&b, Limb::ZERO)
}

// This selection formula is inherited from subtle
#[inline(always)]
fn select_word(a: Limb, b: Limb, choice: Limb) -> Limb {
  a ^ ((a ^ b) & choice)
}

/// Reduce once if appropriate
#[inline(always)]
fn red1(a: U256) -> U256 {
  let (reduced, borrow) = sub_value(a, MODULUS);
  let mut out = U256::ZERO;
  for j in 0 .. U256::LIMBS {
    out.as_limbs_mut()[j] = select_word(reduced.as_limbs()[j], a.as_limbs()[j], borrow);
  }
  out
}

/// Reduce any 256-bit value
#[inline(always)]
fn red256(mut a: U256) -> HelioseleneField {
  // If the highest bit is set, we clear it and add the distance to the modulus
  let high_bit = (a.as_limbs()[U256::LIMBS - 1] >> (Limb::BITS - 1)).wrapping_neg();
  a.as_limbs_mut()[U256::LIMBS - 1] = a.as_limbs()[U256::LIMBS - 1] & (Limb::MAX >> 1);
  let mut carry = Limb::ZERO;
  for j in 0 .. U128::LIMBS {
    (a.as_limbs_mut()[j], carry) = add_with_bounded_overflow(
      a.as_limbs()[j],
      high_bit & MODULUS_255_DISTANCE.as_limbs()[j],
      carry,
    );
  }
  for j in U128::LIMBS .. U256::LIMBS {
    let (limb, carry_bool) = a.as_limbs()[j].0.overflowing_add(carry.0);
    (a.as_limbs_mut()[j], carry) = (Limb(limb), Limb(carry_bool as _));
  }

  // The resulting value is either reduced or within one reduction step as `3 * MODULUS > 2**256`
  HelioseleneField(red1(a))
}

impl Add for HelioseleneField {
  type Output = Self;
  #[inline(always)]
  fn add(self, b: Self) -> Self::Output {
    HelioseleneField(red1(self.0.wrapping_add(&b.0)))
  }
}
impl Add<&HelioseleneField> for HelioseleneField {
  type Output = Self;
  #[inline(always)]
  fn add(self, b: &Self) -> Self::Output {
    self + *b
  }
}
impl AddAssign for HelioseleneField {
  #[inline(always)]
  fn add_assign(&mut self, b: Self) {
    *self = *self + b;
  }
}
impl AddAssign<&HelioseleneField> for HelioseleneField {
  #[inline(always)]
  fn add_assign(&mut self, b: &Self) {
    *self = *self + b;
  }
}
impl Sum for HelioseleneField {
  fn sum<I: Iterator<Item = HelioseleneField>>(iter: I) -> HelioseleneField {
    let mut res = HelioseleneField::ZERO;
    for item in iter {
      res += item;
    }
    res
  }
}
impl<'a> Sum<&'a HelioseleneField> for HelioseleneField {
  fn sum<I: Iterator<Item = &'a HelioseleneField>>(iter: I) -> HelioseleneField {
    iter.copied().sum()
  }
}

impl Neg for HelioseleneField {
  type Output = Self;
  #[inline(always)]
  fn neg(self) -> Self::Output {
    <_>::conditional_select(
      &HelioseleneField(MODULUS.wrapping_sub(&self.0)),
      &Self::ZERO,
      self.is_zero(),
    )
  }
}

impl Neg for &HelioseleneField {
  type Output = HelioseleneField;
  #[inline(always)]
  fn neg(self) -> Self::Output {
    -*self
  }
}

impl Sub for HelioseleneField {
  type Output = Self;
  #[inline(always)]
  fn sub(self, b: Self) -> Self::Output {
    let (candidate, underflowed) = sub_value(self.0, b.0);
    let plus_modulus = candidate.wrapping_add(&MODULUS);
    let mut out = U256::ZERO;
    for j in 0 .. U256::LIMBS {
      out.as_limbs_mut()[j] =
        select_word(candidate.as_limbs()[j], plus_modulus.as_limbs()[j], underflowed);
    }
    Self(out)
  }
}
impl Sub<&HelioseleneField> for HelioseleneField {
  type Output = Self;
  #[inline(always)]
  fn sub(self, b: &Self) -> Self::Output {
    self - *b
  }
}
impl SubAssign for HelioseleneField {
  #[inline(always)]
  fn sub_assign(&mut self, b: Self) {
    *self = *self - b;
  }
}
impl SubAssign<&HelioseleneField> for HelioseleneField {
  #[inline(always)]
  fn sub_assign(&mut self, b: &Self) {
    *self = *self - b;
  }
}

#[inline(always)]
fn red512(wide: (U256, U256)) -> HelioseleneField {
  /*
    The premise of the Crandall reduction is how the modulus is equivalent to
    2**255 - MODULUS_255_DISTANCE, where MODULUS_255_DISTANCE is short (only two words). This means
    2**255 is congruent to MODULUS_255_DISTANCE modulo the modulus, and subtraction of 2**255 is
    congruent to subtracting MODULUS_255_DISTANCE.
  */

  let mut limbs = [Limb::ZERO; 2 * U256::LIMBS];
  limbs[.. U256::LIMBS].copy_from_slice(wide.0.as_limbs());
  limbs[U256::LIMBS ..].copy_from_slice(wide.1.as_limbs());

  /*
    Perform a 128-bit multiplication with the highest bits, producing a 256-bit value which must
    be further shifted by 128 bits.
  */
  let mut carries = [Limb::ZERO; U256::LIMBS + U128::LIMBS];
  let mut carry;
  for i in U128::LIMBS .. U256::LIMBS {
    (limbs[i], carry) =
      limbs[i].mac(limbs[U256::LIMBS + i], TWO_MODULUS_255_DISTANCE.as_limbs()[0], Limb::ZERO);
    for j in 1 .. U128::LIMBS {
      (limbs[i + j], carry) =
        limbs[i + j].mac(limbs[U256::LIMBS + i], TWO_MODULUS_255_DISTANCE.as_limbs()[j], carry);
    }
    carries[i + U128::LIMBS] = carry;
  }
  carry = Limb::ZERO;
  for j in U256::LIMBS .. (U256::LIMBS + U128::LIMBS) {
    (limbs[j], carry) = add_with_bounded_overflow(limbs[j], carries[j], carry);
  }

  /*
    The 384th bit may be set, despite just multiplying those limbs out. We resolve this by
    explicitly reducing the 384th bit out with the addition of `(2**256 % MODULUS) << 128`. The
    resulting carry is guaranteed to be non-zero as
    ```
    (2**384 - 1) + # The maximum value present in limbs
      (((2**128 - 1) * (2 * (2**255 - MODULUS))) << 128) - # Reduce out the maximum highest bits
      2**384 + # Subtract the 384th bit, if set
      ((2 * (2**255 - MODULUS)) << 128) < # The corresponding reduction for the 384th bit
      2**384 # The bound representable by the remaining limbs
    ```
  */
  let three_eighty_four_carry = carry.wrapping_neg();
  let mut carry = Limb::ZERO;
  for j in 0 .. U128::LIMBS {
    (limbs[U128::LIMBS + j], carry) = add_with_bounded_overflow(
      limbs[U128::LIMBS + j],
      (three_eighty_four_carry & TWO_MODULUS_255_DISTANCE.as_limbs()[j]).wrapping_add(carry),
      Limb::ZERO,
    );
  }
  for j in U128::LIMBS .. U256::LIMBS {
    (limbs[U128::LIMBS + j], carry) =
      add_with_bounded_overflow(limbs[U128::LIMBS + j], Limb::ZERO, carry);
  }

  // Perform the 128-bit multiplication with the next highest bits
  for i in 0 .. U128::LIMBS {
    (limbs[i], carry) =
      limbs[i].mac(limbs[U256::LIMBS + i], TWO_MODULUS_255_DISTANCE.as_limbs()[0], Limb::ZERO);
    for j in 1 .. U128::LIMBS {
      (limbs[i + j], carry) =
        limbs[i + j].mac(limbs[U256::LIMBS + i], TWO_MODULUS_255_DISTANCE.as_limbs()[j], carry);
    }
    carries[i + U128::LIMBS] = carry;
  }
  carry = Limb::ZERO;
  for j in U128::LIMBS .. U256::LIMBS {
    (limbs[j], carry) = add_with_bounded_overflow(limbs[j], carries[j], carry);
  }

  // As with the 384th bit, we now reduce out the 256th bit if set, which again won't overflow
  let two_fifty_six_carry = carry.wrapping_neg();
  let mut carry = Limb::ZERO;
  for i in 0 .. U128::LIMBS {
    (limbs[i], carry) = add_with_bounded_overflow(
      limbs[i],
      (two_fifty_six_carry & TWO_MODULUS_255_DISTANCE.as_limbs()[i]).wrapping_add(carry),
      Limb::ZERO,
    );
  }
  for i in U128::LIMBS .. U256::LIMBS {
    let (limb, carry_bool) = limbs[i].0.overflowing_add(carry.0);
    (limbs[i], carry) = (Limb(limb), Limb(carry_bool as _));
  }

  let mut res = U256::ZERO;
  res.as_limbs_mut().copy_from_slice(&limbs[.. U256::LIMBS]);
  // Convert `res` to a valid scalar
  red256(res)
}

impl Mul for HelioseleneField {
  type Output = Self;
  #[inline(always)]
  fn mul(self, b: Self) -> Self::Output {
    red512(self.0.mul_wide(&b.0))
  }
}
impl Mul<&HelioseleneField> for HelioseleneField {
  type Output = Self;
  #[inline(always)]
  fn mul(self, b: &Self) -> Self::Output {
    self * *b
  }
}
impl MulAssign for HelioseleneField {
  #[inline(always)]
  fn mul_assign(&mut self, b: Self) {
    *self = *self * b;
  }
}
impl MulAssign<&HelioseleneField> for HelioseleneField {
  #[inline(always)]
  fn mul_assign(&mut self, b: &Self) {
    *self = *self * b;
  }
}
impl Product<HelioseleneField> for HelioseleneField {
  fn product<I: Iterator<Item = HelioseleneField>>(iter: I) -> HelioseleneField {
    let mut res = HelioseleneField::ONE;
    for item in iter {
      res *= item;
    }
    res
  }
}
impl<'a> Product<&'a HelioseleneField> for HelioseleneField {
  fn product<I: Iterator<Item = &'a HelioseleneField>>(iter: I) -> HelioseleneField {
    iter.copied().product()
  }
}

impl HelioseleneField {
  /// Perform an exponentation.
  pub fn pow(&self, exp: Self) -> Self {
    let mut table = [Self::ONE; 16];
    table[1] = *self;
    table[2] = self.square();
    table[3] = table[2] * self;
    table[4] = table[2].square();
    table[5] = table[4] * self;
    table[6] = table[3].square();
    table[7] = table[6] * self;
    table[8] = table[4].square();
    table[9] = table[8] * self;
    table[10] = table[5].square();
    table[11] = table[10] * self;
    table[12] = table[6].square();
    table[13] = table[12] * self;
    table[14] = table[7].square();
    table[15] = table[14] * self;

    let mut res = Self::ONE;
    let mut bits = 0;
    for (i, mut bit) in exp.to_le_bits().iter_mut().rev().enumerate() {
      bits <<= 1;
      let mut bit = crate::u8_from_bool(bit.deref_mut());
      bits |= bit;
      bit.zeroize();

      if ((i + 1) % 4) == 0 {
        if i != 3 {
          for _ in 0 .. 4 {
            res = res.square();
          }
        }

        let mut factor = table[0];
        for (j, candidate) in table[1 ..].iter().enumerate() {
          let j = j + 1;
          factor = Self::conditional_select(&factor, candidate, usize::from(bits).ct_eq(&j));
        }
        res *= factor;
        bits = 0;
      }
    }
    res
  }

  /// Perform a wide reduction, presumably to obtain a non-biased Helioselene field element.
  pub fn wide_reduce(bytes: [u8; 64]) -> HelioseleneField {
    red512((U256::from_le_slice(&bytes[.. 32]), U256::from_le_slice(&bytes[32 ..])))
  }
}

impl Field for HelioseleneField {
  const ZERO: Self = Self(U256::ZERO);
  const ONE: Self = Self(U256::ONE);

  #[inline(always)]
  fn is_zero(&self) -> Choice {
    let mut all = Limb::ZERO;
    for l in 0 .. U256::LIMBS {
      all = all | self.0.as_limbs()[l];
    }
    all.ct_eq(&Limb::ZERO)
  }

  fn random(mut rng: impl RngCore) -> Self {
    let mut a = [0; 32];
    rng.fill_bytes(&mut a);
    let mut b = [0; 32];
    rng.fill_bytes(&mut b);
    red512((U256::from_le_slice(&a), U256::from_le_slice(&b)))
  }

  fn double(&self) -> Self {
    HelioseleneField(red1(self.0.shl_vartime(1)))
  }

  #[inline(always)]
  fn square(&self) -> Self {
    red512(self.0.square_wide())
  }

  // Binary GCD Algorithm 1, https://eprint.iacr.org/2020/972
  #[inline(always)]
  fn invert(&self) -> CtOption<Self> {
    let mut a = self.0;
    let mut b = MODULUS;
    let mut u = U256::ONE;
    let mut v = U256::ZERO;

    #[inline(always)]
    fn step(a: &mut U256, b: &mut U256, u: &mut U256, v: &mut U256, limbs: usize) {
      let a_is_odd = a.as_limbs()[0].0 & 1;
      let a_is_odd = Limb(a_is_odd).wrapping_neg();

      // Calculate `a - b`, which also yields if `a < b` by if it underflows
      let mut borrow = Limb::ZERO;
      let mut a_sub_b = U256::ZERO;
      for l in 0 .. limbs {
        (a_sub_b.as_limbs_mut()[l], borrow) =
          sub_with_bounded_overflow(a.as_limbs()[l], b.as_limbs()[l], borrow);
      }
      let a_lt_b = borrow.wrapping_neg();

      let both = a_is_odd & a_lt_b;

      #[inline(always)]
      fn select(a: &U256, b: &U256, choice: Limb, limbs: usize) -> U256 {
        let mut res = U256::ZERO;
        for l in 0 .. limbs {
          res.as_limbs_mut()[l] = select_word(a.as_limbs()[l], b.as_limbs()[l], choice);
        }
        res
      }

      // Set `b` to `a` (part of the swap defined on line 8 of the algorithm's description)
      *b = select(b, a, both, limbs);

      // Negate `a_sub_b` to obtain `a_diff_b` if `a_lt_b`
      let a_diff_b = {
        // Negation is applying the logical NOT to every word while adding 1
        let mut carry = Limb::ONE & a_lt_b;
        let mut a_diff_b = U256::ZERO;
        for l in 0 .. limbs {
          // (a ^ x) is a logical NOT if `x` is set and a NOP if `x` is 0
          let limb;
          let carry_bool;
          (limb, carry_bool) = (a_sub_b.as_limbs()[l] ^ a_lt_b).0.overflowing_add(carry.0);
          (a_diff_b.as_limbs_mut()[l], carry) = (Limb(limb), Limb(carry_bool as _));
        }
        a_diff_b
      };
      // Leave `a` untouched if `a` is even, else set `a` to the difference of `a` and `b`
      *a = select(a, &a_diff_b, a_is_odd, limbs);

      /*
        The following code immediately takes the difference of `u - v`, before negating to
        obtain `v - u` if necessary. The advantage to this methodology, compared to swapping
        `u, v` and then peforming the subtraction, is how during the negation any required
        additions of the modulus can be performed.
      */

      let u_start = *u;

      // Calculate `v` or `v - u` depending on if `a & 1`
      let mut borrow = Limb::ZERO;
      let mut u_sub_v = U256::ZERO;
      for l in 0 .. U256::LIMBS {
        (u_sub_v.as_limbs_mut()[l], borrow) =
          sub_with_bounded_overflow(u.as_limbs()[l], v.as_limbs()[l] & a_is_odd, borrow);
      }
      let u_sub_v_neg = borrow.wrapping_neg();

      // Negate in the case `(a & 1) & (a < b)`
      let should_negate = both;
      /*
        Whether the resulting number will be negative, with the exceptional case of if the
        resulting number is 0, in which case this iteration will terminate with `u = MODULUS`.
        `u, v` being not in the range `0 .. MODULUS` yet `0 ..= MODULUS` does not affect this
        algorithm at all, until the very end when we do expect the value to be in-range. The
        worst case, we calculate `0 - MODULUS -> -MODULUS`, will cause addition of the `MODULUS`
        (due to the underflow) and a result of `0`.

        One final reduction, outside of this loop, is cheaper than checking if the number is
        -0 on every loop iteration.
      */
      let v_u_sub_u_v_neg = u_sub_v_neg ^ should_negate;

      // Negation is the logical NOT *and* the addition of the constant `1`, so this is the
      // parity regardless of if we're about to perform a negation
      let result_is_odd = (u_sub_v.as_limbs()[0] & Limb::ONE).wrapping_neg();

      /*
        This is a XOR as to allow `add_one_modulus` and `add_two_modulus` to be simultaneously
        set and achieve the desired result. If it is modified to the modulus directly, then we'd
        require `add_one_modulus` and `add_two_modulus` be exclusive which may enable the
        compiler to be intelligent enough to insert a branch.

        This pattern does allow the compiler to, if it realizes `add_two_modulus` is only set
        when `add_one_modulus` is, create the XOR'd constant and compress to a branch, yet that
        should be much tricker for an optimization pass.
      */
      const MODULUS_XOR_TWO_MODULUS: U256 =
        U256::from_be_hex("80000000000000000000000000000000c1818875d9afbde8b3db76968b6848a1");
      /*
        Add two instances of the modulus if:
        - We must add one instance due to the current number being negative
        - Adding one instance will cause the result to be odd
      */
      let add_two_modulus = v_u_sub_u_v_neg & (!result_is_odd);
      // Add one instance if negative/currently odd but not both
      let add_one_modulus = v_u_sub_u_v_neg | result_is_odd;

      // This is the starting carry for the negation algorithm
      let mut carry = Limb::ONE & should_negate;
      for l in 0 .. U128::LIMBS {
        // The modulus to add in, to correct for underflow/enable halving
        let modulus_instances = (MODULUS.as_limbs()[l] & add_one_modulus) ^
          (MODULUS_XOR_TWO_MODULUS.as_limbs()[l] & add_two_modulus);

        /*
          Instead of adding the 255-bit modulus, it would appear more efficient to subtract out the
          distance from 2**255, which is only 127 bits. This is non-trivial however due to needing
          to add 1 upon negation, which can currently be chained with the addition of the modulus,
          but could not be if we subtracted the distance from the modulus.
        */
        // The carry is bounded to be `<= 1` and the low 128-bits of the modulus aren't full
        let (limb, carry_bool) = (u_sub_v.as_limbs()[l] ^ should_negate)
          .0
          .overflowing_add(modulus_instances.wrapping_add(carry).0);
        (u.as_limbs_mut()[l], carry) = (Limb(limb), Limb(carry_bool as _));
      }
      // Unroll the later iterations due to the structure of the XOR
      for l in U128::LIMBS .. U256::LIMBS {
        let modulus_instances = MODULUS.as_limbs()[l] & add_one_modulus;

        (u.as_limbs_mut()[l], carry) = add_with_bounded_overflow(
          u_sub_v.as_limbs()[l] ^ should_negate,
          modulus_instances,
          carry,
        );
      }
      // This is a DISJOINT OR and we _can_ use `core::intrinsics::disjoint_bitor` here
      u.as_limbs_mut()[U256::LIMBS - 1] =
        u.as_limbs()[U256::LIMBS - 1] | (add_two_modulus << (Limb::BITS - 1));

      // Set `v` to the `u` from the start if `(a & 1) & (a < b)`
      *v = select(v, &u_start, both, U256::LIMBS);

      // Divide by 2
      for l in 0 .. (limbs - 1) {
        a.as_limbs_mut()[l] = (a.as_limbs()[l] >> 1) | (a.as_limbs()[l + 1] << (Limb::BITS - 1));
      }
      a.as_limbs_mut()[limbs - 1] >>= 1;

      for l in 0 .. (U256::LIMBS - 1) {
        u.as_limbs_mut()[l] = (u.as_limbs()[l] >> 1) | (u.as_limbs()[l + 1] << (Limb::BITS - 1));
      }
      u.as_limbs_mut()[U256::LIMBS - 1] >>= 1;
    }

    // Note the limbs still in use so we don't apply operations over unused limbs
    for limbs in (2 ..= U256::LIMBS).rev() {
      for _ in 0 .. (2 * Limb::BITS) {
        step(&mut a, &mut b, &mut u, &mut v, limbs);
      }
    }
    for _ in 0 .. ((2 * Limb::BITS) - 2) {
      step(&mut a, &mut b, &mut u, &mut v, 1);
    }

    CtOption::new(Self(red1(v)), !self.is_zero())
  }

  fn sqrt(&self) -> CtOption<Self> {
    let mut table = [Self::ONE; 16];
    table[1] = *self;
    table[2] = self.square();
    table[3] = table[2] * self;
    table[4] = table[2].square();
    table[5] = table[4] * self;
    table[6] = table[3].square();
    table[7] = table[6] * self;
    table[8] = table[4].square();
    table[9] = table[8] * self;
    table[10] = table[5].square();
    table[11] = table[10] * self;
    table[12] = table[6].square();
    table[13] = table[12] * self;
    table[14] = table[7].square();
    table[15] = table[14] * self;

    // The first 128 bits are all set, hence this ladder to produce the value
    let mut res = table[15];
    let four_zero = res.square();
    let four_zero_zero = four_zero.square();
    res = four_zero_zero.square();
    res = res.square();
    res *= &table[15];
    let old_res = res;

    for _ in 0 .. 8 {
      res = res.square();
    }
    res *= &old_res;
    let old_res = res;

    for _ in 0 .. 16 {
      res = res.square();
    }
    res *= old_res;
    let old_res = res;

    for _ in 0 .. 32 {
      res = res.square();
    }
    res *= old_res;
    let old_res = res;

    for _ in 0 .. 64 {
      res = res.square();
    }
    res *= old_res;

    // Then the bits have 0111111 twice
    let six = four_zero_zero * table[3];
    for _ in 0 .. 7 {
      res = res.square();
    }
    res *= six;
    for _ in 0 .. 7 {
      res = res.square();
    }
    res *= six;

    let mut bits = 0;
    for bit in MODULUS_PLUS_ONE_DIV_FOUR.to_le_bits().iter().take(253).rev().skip(142) {
      bits <<= 1;
      let bit = (*bit) as u8;
      bits |= bit;

      res = res.square();

      if (bits & (1 << 3)) != 0 {
        res *= table[usize::from(bits)];
        bits = 0;
      }
    }

    // We don't handle the final bit window as it's zero

    CtOption::new(res, res.square().ct_eq(self))
  }

  fn sqrt_ratio(num: &Self, div: &Self) -> (Choice, Self) {
    ff::helpers::sqrt_ratio_generic(num, div)
  }
}

impl PrimeField for HelioseleneField {
  type Repr = [u8; 32];

  const MODULUS: &'static str =
    "0x7fffffffffffffffffffffffffffffffbf7f782cb7656b586eb6d2727927c79f";

  const NUM_BITS: u32 = 255;
  const CAPACITY: u32 = 254;

  const TWO_INV: Self =
    Self(U256::from_le_hex("d0e3933c39695b37acb5b25b16bcbfdfffffffffffffffffffffffffffffff3f"));

  const MULTIPLICATIVE_GENERATOR: Self = Self(U256::from_u8(5));
  const S: u32 = 1;

  const ROOT_OF_UNITY: Self =
    Self(U256::from_be_hex("7fffffffffffffffffffffffffffffffbf7f782cb7656b586eb6d2727927c79e"));
  const ROOT_OF_UNITY_INV: Self =
    Self(U256::from_le_hex("9ec7277972d2b66e586b65b72c787fbfffffffffffffffffffffffffffffff7f"));

  const DELTA: Self = Self(U256::from_u8(25));

  fn from_repr(bytes: Self::Repr) -> CtOption<Self> {
    let res = U256::from_le_slice(&bytes);

    // Check if a U256 contains a value less than the modulus.
    #[inline(always)]
    fn reduced(a: U256) -> Choice {
      let mut b_limbs = MODULUS_255_DISTANCE.as_limbs().iter();
      let mut last = Limb::ZERO;
      let mut carry = Limb::ZERO;
      for a in a.as_limbs() {
        let b = b_limbs.next().unwrap_or(&Limb::ZERO);
        (last, carry) = add_with_bounded_overflow(*a, *b, carry);
      }
      ((last & (Limb::ONE << (Limb::BITS - 1))) | carry).ct_eq(&Limb::ZERO)
    }

    let reduced = reduced(res);
    CtOption::new(HelioseleneField(res), reduced)
  }

  fn to_repr(&self) -> Self::Repr {
    self.0.to_le_bytes()
  }

  fn is_odd(&self) -> Choice {
    Choice::from((self.0.as_limbs()[0].0 & 1) as u8)
  }
}

impl PrimeFieldBits for HelioseleneField {
  type ReprBits = [u8; 32];

  fn to_le_bits(&self) -> FieldBits<Self::ReprBits> {
    self.to_repr().into()
  }

  fn char_le_bits() -> FieldBits<Self::ReprBits> {
    MODULUS.to_le_bytes().into()
  }
}

// The following tests assume a 64-bit host as it uses crypto-bigint's limbs directly
#[cfg(test)]
#[cfg(target_pointer_width = "64")]
mod tests_assuming_64_bits {
  use super::*;

  #[inline(always)]
  fn lo_hi_split<T, S: crypto_bigint::Split<Output = T>>(a: S) -> (T, T) {
    let (hi, lo) = a.split();
    (lo, hi)
  }

  #[inline(always)]
  fn lo_hi_concat<T, S: crypto_bigint::Concat<Output = T>>(a: &S, b: &S) -> T {
    S::concat(b, a)
  }

  #[test]
  fn test_reduction_of_each_bit() {
    for b in 0 .. 512usize {
      let to_reduce = crypto_bigint::U512::ONE << b;
      let reduced = to_reduce.checked_rem(&lo_hi_concat(&MODULUS, &U256::ZERO)).unwrap();

      if b < 256 {
        let reduced_apo = red256(lo_hi_split(to_reduce).0);
        assert_eq!(
          &reduced.as_limbs()[.. 4],
          reduced_apo.0.as_limbs(),
          "failed to reduce the 256-bit 1 << {b}"
        );
      }

      let reduced_apo = red512(lo_hi_split(to_reduce));
      assert_eq!(
        &reduced.as_limbs()[.. 4],
        reduced_apo.0.as_limbs(),
        "failed to reduce the 512-bit 1 << {b}"
      );
    }
  }

  #[test]
  fn test_wide_reduction() {
    use crypto_bigint::Random;
    for _ in 0 .. 1000 {
      let to_reduce = crypto_bigint::U512::random(&mut rand_core::OsRng);
      let reduced = to_reduce.checked_rem(&lo_hi_concat(&MODULUS, &U256::ZERO)).unwrap();
      let reduced_apo = HelioseleneField::wide_reduce(to_reduce.to_le_bytes());
      assert_eq!(
        &reduced.as_limbs()[.. 4],
        reduced_apo.0.as_limbs(),
        "failed to reduce {:?}",
        to_reduce.to_words(),
      );
    }

    let to_reduce = crypto_bigint::U512::MAX;
    let reduced = to_reduce.checked_rem(&lo_hi_concat(&MODULUS, &U256::ZERO)).unwrap();
    let reduced_apo = HelioseleneField::wide_reduce(to_reduce.to_le_bytes());
    assert_eq!(
      &reduced.as_limbs()[.. 4],
      reduced_apo.0.as_limbs(),
      "failed to reduce {:?}",
      to_reduce.to_words(),
    );
  }
}

#[test]
fn test_helioselene_field() {
  ff_group_tests::prime_field::test_prime_field_bits::<_, HelioseleneField>(&mut rand_core::OsRng);
}
