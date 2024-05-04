use zeroize::Zeroize;

use blake2::{Digest, Blake2b512};

use group::Group;

use helioselene::{Field25519, HelioseleneField, HeliosPoint, SelenePoint};

use crate::Ciphersuite;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Zeroize)]
pub struct Helios;
impl Ciphersuite for Helios {
  type F = HelioseleneField;
  type G = HeliosPoint;
  type H = Blake2b512;

  const ID: &'static [u8] = b"Helios";

  fn generator() -> Self::G {
    <HeliosPoint as Group>::generator()
  }

  fn hash_to_F(dst: &[u8], msg: &[u8]) -> Self::F {
    let mut uniform = [0; 64];
    let mut hash = Blake2b512::digest([dst, msg].concat());
    uniform.copy_from_slice(hash.as_ref());
    let hash_as_mut: &mut [u8] = hash.as_mut();
    hash_as_mut.zeroize();
    let res = HelioseleneField::wide_reduce(uniform);
    uniform.zeroize();
    res
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Zeroize)]
pub struct Selene;
impl Ciphersuite for Selene {
  type F = Field25519;
  type G = SelenePoint;
  type H = Blake2b512;

  const ID: &'static [u8] = b"Selene";

  fn generator() -> Self::G {
    <SelenePoint as Group>::generator()
  }

  fn hash_to_F(dst: &[u8], msg: &[u8]) -> Self::F {
    let mut uniform = [0; 64];
    let mut hash = Blake2b512::digest([dst, msg].concat());
    uniform.copy_from_slice(hash.as_ref());
    let hash_as_mut: &mut [u8] = hash.as_mut();
    hash_as_mut.zeroize();
    let res = Field25519::wide_reduce(uniform);
    uniform.zeroize();
    res
  }
}

#[test]
fn test_helioselene() {
  ff_group_tests::group::test_prime_group_bits::<_, HeliosPoint>(&mut rand_core::OsRng);
  ff_group_tests::group::test_prime_group_bits::<_, SelenePoint>(&mut rand_core::OsRng);
}
