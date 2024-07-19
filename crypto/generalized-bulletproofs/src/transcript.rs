use std::io;

use blake2::{Digest, Blake2b512};

use ciphersuite::{
  group::{ff::PrimeField, GroupEncoding},
  Ciphersuite,
};

const SCALAR: u8 = 0;
const POINT: u8 = 1;
const CHALLENGE: u8 = 2;

fn challenge<F: PrimeField>(digest: &mut Blake2b512) -> F {
  digest.update([CHALLENGE]);
  let chl = digest.clone().finalize();

  let mut res = F::ZERO;
  for (i, mut byte) in chl.iter().cloned().enumerate() {
    for j in 0 .. 8 {
      let lsb = byte & 1;
      let mut bit = F::from(u64::from(lsb));
      for _ in 0 .. ((i * 8) + j) {
        bit = bit.double();
      }
      res += bit;

      byte >>= 1;
    }
  }

  // Negligible probability
  if bool::from(res.is_zero()) {
    panic!("zero challenge");
  }

  res
}

pub struct Transcript {
  digest: Blake2b512,
  transcript: Vec<u8>,
}

/*
  We define our proofs as Vec<u8> and derive our transcripts from the values we deserialize from
  them. This format assumes the order of the values read, their size, and their quantity are
  constant to the context.
*/
impl Transcript {
  pub fn new(context: [u8; 32]) -> Self {
    let mut digest = Blake2b512::new();
    digest.update(context);
    Self { digest, transcript: Vec::with_capacity(1024) }
  }

  pub(crate) fn push_scalar(&mut self, scalar: impl PrimeField) {
    self.digest.update([SCALAR]);
    let bytes = scalar.to_repr();
    self.digest.update(bytes);
    self.transcript.extend(bytes.as_ref());
  }

  pub(crate) fn push_point(&mut self, point: impl GroupEncoding) {
    self.digest.update([POINT]);
    let bytes = point.to_bytes();
    self.digest.update(bytes);
    self.transcript.extend(bytes.as_ref());
  }

  pub fn write_commitments<G: Copy + GroupEncoding>(&mut self, C: &[G], V: &[G]) {
    for C in C {
      self.push_point(*C);
    }
    for V in V {
      self.push_point(*V);
    }
  }

  pub fn challenge<F: PrimeField>(&mut self) -> F {
    challenge(&mut self.digest)
  }

  pub fn complete(self) -> Vec<u8> {
    self.transcript
  }
}

pub struct VerifierTranscript<'a> {
  digest: Blake2b512,
  transcript: &'a [u8],
}

impl<'a> VerifierTranscript<'a> {
  pub fn new(context: [u8; 32], transcript: &'a [u8]) -> Self {
    let mut digest = Blake2b512::new();
    digest.update(context);
    Self { digest, transcript }
  }

  pub(crate) fn read_scalar<C: Ciphersuite>(&mut self) -> io::Result<C::F> {
    let scalar = C::read_F(&mut self.transcript)?;
    self.digest.update([SCALAR]);
    let bytes = scalar.to_repr();
    self.digest.update(bytes);
    Ok(scalar)
  }

  pub(crate) fn read_point<C: Ciphersuite>(&mut self) -> io::Result<C::G> {
    let point = C::read_G(&mut self.transcript)?;
    self.digest.update([POINT]);
    let bytes = point.to_bytes();
    self.digest.update(bytes);
    Ok(point)
  }

  #[allow(clippy::type_complexity)]
  pub fn read_commitments<C: Ciphersuite>(
    &mut self,
    C: usize,
    V: usize,
  ) -> io::Result<(Vec<C::G>, Vec<C::G>)> {
    let mut C_vec = Vec::with_capacity(C);
    for _ in 0 .. C {
      C_vec.push(self.read_point::<C>()?);
    }
    let mut V_vec = Vec::with_capacity(V);
    for _ in 0 .. V {
      V_vec.push(self.read_point::<C>()?);
    }
    Ok((C_vec, V_vec))
  }

  pub fn challenge<F: PrimeField>(&mut self) -> F {
    challenge(&mut self.digest)
  }
}
