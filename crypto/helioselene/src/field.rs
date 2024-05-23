use zeroize::{DefaultIsZeroes, Zeroize};

use crypto_bigint::{
  U256, U512,
  modular::constant_mod::{ResidueParams, Residue},
};

const MODULUS_STR: &str = "7fffffffffffffffffffffffffffffffbf7f782cb7656b586eb6d2727927c79f";

impl_modulus!(HelioseleneQ, U256, MODULUS_STR);
type ResidueType = Residue<HelioseleneQ, { HelioseleneQ::LIMBS }>;

/// The field novel to Helios/Selene.
#[derive(Clone, Copy, PartialEq, Eq, Default, Debug)]
#[repr(C)]
pub struct HelioseleneField(pub(crate) ResidueType);

impl DefaultIsZeroes for HelioseleneField {}

pub(crate) const MODULUS: U256 = U256::from_be_hex(MODULUS_STR);

const WIDE_MODULUS: U512 = U512::from_be_hex(concat!(
  "0000000000000000000000000000000000000000000000000000000000000000",
  "7fffffffffffffffffffffffffffffffbf7f782cb7656b586eb6d2727927c79f",
));

field!(
  HelioseleneField,
  ResidueType,
  MODULUS_STR,
  MODULUS,
  WIDE_MODULUS,
  5,
  1,
  "7fffffffffffffffffffffffffffffffbf7f782cb7656b586eb6d2727927c79e",
  "0000000000000000000000000000000000000000000000000000000000000019",
);

impl HelioseleneField {
  /// Perform a wide reduction, presumably to obtain a non-biased Helioselene field element.
  pub fn wide_reduce(bytes: [u8; 64]) -> HelioseleneField {
    HelioseleneField(Residue::new(&reduce(U512::from_le_slice(bytes.as_ref()))))
  }
}

#[test]
fn test_helioselene_field() {
  ff_group_tests::prime_field::test_prime_field_bits::<_, HelioseleneField>(&mut rand_core::OsRng);
}
