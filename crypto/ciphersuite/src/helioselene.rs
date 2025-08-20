#[cfg(any(feature = "alloc", feature = "std"))]
#[allow(unused_imports)]
use std_shims::prelude::*;
#[cfg(any(feature = "alloc", feature = "std"))]
use std_shims::io::{self, Read};

use zeroize::Zeroize;

use blake2::{Digest, Blake2b512};

use group::{Group, GroupEncoding};
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

  fn reduce_512(mut scalar: [u8; 64]) -> Self::F {
    let res = HelioseleneField::wide_reduce(scalar);
    scalar.zeroize();
    res
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

  // We override the provided impl, which compares against the reserialization, because
  // Helios::G::from_bytes already enforces canonically encoded points
  #[cfg(any(feature = "alloc", feature = "std"))]
  #[allow(non_snake_case)]
  fn read_G<R: Read>(reader: &mut R) -> io::Result<Self::G> {
    let mut encoding = <Self::G as GroupEncoding>::Repr::default();
    reader.read_exact(encoding.as_mut())?;

    let point = Option::<Self::G>::from(Self::G::from_bytes(&encoding))
      .ok_or_else(|| io::Error::other("invalid point"))?;
    Ok(point)
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

  fn reduce_512(mut scalar: [u8; 64]) -> Self::F {
    let res = Field25519::wide_reduce(scalar);
    scalar.zeroize();
    res
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

  // We override the provided impl, which compares against the reserialization, because
  // Selene::G::from_bytes already enforces canonically encoded points
  #[cfg(any(feature = "alloc", feature = "std"))]
  #[allow(non_snake_case)]
  fn read_G<R: Read>(reader: &mut R) -> io::Result<Self::G> {
    let mut encoding = <Self::G as GroupEncoding>::Repr::default();
    reader.read_exact(encoding.as_mut())?;

    let point = Option::<Self::G>::from(Self::G::from_bytes(&encoding))
      .ok_or_else(|| io::Error::other("invalid point"))?;
    Ok(point)
  }
}

#[test]
fn test_helioselene() {
  ff_group_tests::group::test_prime_group_bits::<_, HeliosPoint>(&mut rand_core::OsRng);
  ff_group_tests::group::test_prime_group_bits::<_, SelenePoint>(&mut rand_core::OsRng);
}
