#![cfg_attr(docsrs, feature(doc_auto_cfg))]
#![doc = include_str!("../README.md")]
#![cfg_attr(not(feature = "std"), no_std)]
#![allow(non_snake_case)]

use core::ops::Deref;
#[cfg(not(feature = "std"))]
#[macro_use]
extern crate alloc;
use std_shims::io::{self, Read, Write};

use rand_core::{RngCore, CryptoRng};

use zeroize::{Zeroize, Zeroizing};

use transcript::Transcript;

use ciphersuite::{
  group::{
    ff::{Field, PrimeField},
    Group, GroupEncoding,
  },
  Ciphersuite,
};
use multiexp::{multiexp_vartime, BatchVerifier};

#[cfg(test)]
mod tests;

/// A Generalized Schnorr Proof.
#[derive(Clone, PartialEq, Eq, Debug, Zeroize)]
pub struct GeneralizedSchnorr<
  C: Ciphersuite,
  const OUTPUTS: usize,
  const SCALARS: usize,
  const SCALARS_PLUS_TWO: usize,
> {
  pub R: [C::G; OUTPUTS],
  pub s: [C::F; SCALARS],
}

impl<C: Ciphersuite, const OUTPUTS: usize, const SCALARS: usize, const SCALARS_PLUS_TWO: usize>
  GeneralizedSchnorr<C, OUTPUTS, SCALARS, SCALARS_PLUS_TWO>
{
  /// Read a GeneralizedSchnorr from something implementing Read.
  pub fn read<R: Read>(reader: &mut R) -> io::Result<Self> {
    let mut R = [C::G::identity(); OUTPUTS];
    for R in &mut R {
      *R = C::read_G(reader)?;
    }
    let mut s = [C::F::ZERO; SCALARS];
    for s in &mut s {
      *s = C::read_F(reader)?;
    }
    Ok(Self { R, s })
  }

  /// Write a GeneralizedSchnorr to something implementing Read.
  pub fn write<W: Write>(&self, writer: &mut W) -> io::Result<()> {
    for R in self.R {
      writer.write_all(R.to_bytes().as_ref())?;
    }
    for s in self.s {
      writer.write_all(s.to_repr().as_ref())?;
    }
    Ok(())
  }

  fn challenge(
    transcript: &mut impl Transcript,
    matrix: [[C::G; SCALARS]; OUTPUTS],
    outputs: [C::G; OUTPUTS],
    nonces: [C::G; OUTPUTS],
  ) -> C::F {
    transcript.domain_separate(b"generalized_schnorr");
    transcript.append_message(
      b"scalars",
      u32::try_from(SCALARS).expect("passed 2**32 scalars").to_le_bytes(),
    );
    transcript.append_message(
      b"outputs",
      u32::try_from(OUTPUTS).expect("passed 2**32 outputs").to_le_bytes(),
    );
    for row in matrix {
      for generator in row {
        transcript.append_message(b"generator", generator.to_bytes());
      }
    }
    for output in outputs {
      transcript.append_message(b"output", output.to_bytes());
    }
    for nonce in nonces {
      transcript.append_message(b"nonce", nonce.to_bytes());
    }
    C::hash_to_F(b"generalized_schnorr", transcript.challenge(b"c").as_ref())
  }

  /// Serialize a GeneralizedSchnorr, returning a `Vec<u8>`.
  #[cfg(feature = "std")]
  pub fn serialize(&self) -> Vec<u8> {
    let mut buf = vec![];
    self.write(&mut buf).unwrap();
    buf
  }

  /// Prove a Generalized Schnorr statement.
  ///
  /// Returns the outputs and the proof for them.
  pub fn prove(
    rng: &mut (impl RngCore + CryptoRng),
    transcript: &mut impl Transcript,
    matrix: [[C::G; SCALARS]; OUTPUTS],
    scalars: [&Zeroizing<C::F>; SCALARS],
  ) -> ([C::G; OUTPUTS], Self) {
    let outputs: [C::G; OUTPUTS] = core::array::from_fn(|i| {
      matrix[i].iter().zip(scalars.iter()).map(|(generator, scalar)| *generator * ***scalar).sum()
    });

    let nonces: [Zeroizing<C::F>; SCALARS] =
      core::array::from_fn(|_| Zeroizing::new(C::F::random(&mut *rng)));
    let R = core::array::from_fn(|i| {
      matrix[i].iter().zip(nonces.iter()).map(|(generator, nonce)| *generator * **nonce).sum()
    });

    let c = Self::challenge(transcript, matrix, outputs, R);
    (outputs, Self { R, s: core::array::from_fn(|i| c * scalars[i].deref() + nonces[i].deref()) })
  }

  /// Return the series of pairs whose products sum to zero for a valid signature.
  ///
  /// This is intended to be used with a multiexp for efficient batch verification.
  fn batch_statements(
    &self,
    transcript: &mut impl Transcript,
    matrix: [[C::G; SCALARS]; OUTPUTS],
    outputs: [C::G; OUTPUTS],
  ) -> [[(C::F, C::G); SCALARS_PLUS_TWO]; OUTPUTS] {
    assert_eq!(SCALARS_PLUS_TWO, SCALARS + 2);
    let c = Self::challenge(transcript, matrix, outputs, self.R);
    core::array::from_fn(|i| {
      core::array::from_fn(|j| {
        if j == SCALARS {
          (-C::F::ONE, self.R[i])
        } else if j == (SCALARS + 1) {
          (-c, outputs[i])
        } else {
          (self.s[j], matrix[i][j])
        }
      })
    })
  }

  /// Verify a Generalized Schnorr proof.
  #[must_use]
  pub fn verify(
    &self,
    transcript: &mut impl Transcript,
    matrix: [[C::G; SCALARS]; OUTPUTS],
    outputs: [C::G; OUTPUTS],
  ) -> bool {
    for statements in self.batch_statements(transcript, matrix, outputs) {
      if !bool::from(multiexp_vartime(statements.as_slice()).is_identity()) {
        return false;
      }
    }
    true
  }

  /// Queue a proof for batch verification.
  pub fn batch_verify<R: RngCore + CryptoRng, I: Copy + Zeroize>(
    &self,
    rng: &mut R,
    transcript: &mut impl Transcript,
    batch: &mut BatchVerifier<I, C::G>,
    id: I,
    matrix: [[C::G; SCALARS]; OUTPUTS],
    outputs: [C::G; OUTPUTS],
  ) {
    for statements in self.batch_statements(transcript, matrix, outputs) {
      batch.queue(rng, id, statements);
    }
  }
}
