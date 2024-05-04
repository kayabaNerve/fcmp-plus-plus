#![allow(non_snake_case)]

use core::fmt;
use std::collections::HashSet;

use zeroize::Zeroize;

use transcript::Transcript;

use multiexp::multiexp;
use ciphersuite::{
  group::{Group, GroupEncoding},
  Ciphersuite,
};

mod scalar_vector;
pub use scalar_vector::ScalarVector;
mod scalar_matrix;
pub use scalar_matrix::ScalarMatrix;
mod point_vector;
pub use point_vector::PointVector;

pub mod inner_product;

pub mod arithmetic_circuit_proof;

#[cfg(any(test, feature = "tests"))]
pub mod tests;

/// Calculate the nearest power of two greater than or equivalent to the argument.
pub(crate) fn padded_pow_of_2(i: usize) -> usize {
  let mut next_pow_of_2 = 1;
  while next_pow_of_2 < i {
    next_pow_of_2 <<= 1;
  }
  next_pow_of_2
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum GeneratorsError {
  GBoldEmpty,
  DifferingGhBoldLengths,
  NotPowerOfTwo,
  DuplicatedGenerator,
}

/// A full set of generators.
#[derive(Clone)]
pub struct Generators<T: 'static + Transcript, C: Ciphersuite> {
  g: C::G,
  h: C::G,

  g_bold: Vec<C::G>,
  h_bold: Vec<C::G>,
  h_sum: Vec<C::G>,

  transcript: T,
}

impl<T: 'static + Transcript, C: Ciphersuite> fmt::Debug for Generators<T, C> {
  fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
    let g = self.g.to_bytes();
    let g: &[u8] = g.as_ref();

    let h = self.h.to_bytes();
    let h: &[u8] = h.as_ref();

    fmt.debug_struct("Generators").field("g", &g).field("h", &h).finish_non_exhaustive()
  }
}

/// The generators for a specific proof, potentially reduced from the original full set of
/// generators.
#[derive(Clone)]
pub struct ProofGenerators<'a, T: 'static + Transcript, C: Ciphersuite> {
  g: &'a C::G,
  h: &'a C::G,

  g_bold: &'a [C::G],
  h_bold: &'a [C::G],
  h_sum: C::G,

  transcript: T::Challenge,
}

impl<T: 'static + Transcript, C: Ciphersuite> fmt::Debug for ProofGenerators<'_, T, C> {
  fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
    let g = self.g.to_bytes();
    let g: &[u8] = g.as_ref();

    let h = self.h.to_bytes();
    let h: &[u8] = h.as_ref();

    fmt.debug_struct("ProofGenerators").field("g", &g).field("h", &h).finish_non_exhaustive()
  }
}

impl<T: 'static + Transcript, C: Ciphersuite> Generators<T, C> {
  /// Construct an instance of Generators for usage with Bulletproofs.
  pub fn new(
    g: C::G,
    h: C::G,
    g_bold: Vec<C::G>,
    h_bold: Vec<C::G>,
  ) -> Result<Self, GeneratorsError> {
    if g_bold.is_empty() {
      Err(GeneratorsError::GBoldEmpty)?;
    }
    if g_bold.len() != h_bold.len() {
      Err(GeneratorsError::DifferingGhBoldLengths)?;
    }
    if padded_pow_of_2(g_bold.len()) != g_bold.len() {
      Err(GeneratorsError::NotPowerOfTwo)?;
    }

    let mut transcript = T::new(b"Generalized Bulletproofs Generators");

    transcript.domain_separate(b"generators");
    let mut set = HashSet::new();
    let mut add_generator = |label, generator: &C::G| {
      assert!(!bool::from(generator.is_identity()));
      let bytes = generator.to_bytes();
      transcript.append_message(label, bytes);
      !set.insert(bytes.as_ref().to_vec())
    };

    assert!(!add_generator(b"g", &g), "g was prior present in empty set");
    if add_generator(b"h", &h) {
      Err(GeneratorsError::DuplicatedGenerator)?;
    }
    for g in &g_bold {
      if add_generator(b"g_bold", g) {
        Err(GeneratorsError::DuplicatedGenerator)?;
      }
    }
    for h in &h_bold {
      if add_generator(b"h_bold", h) {
        Err(GeneratorsError::DuplicatedGenerator)?;
      }
    }

    let mut running_h_sum = C::G::identity();
    let mut h_sum = vec![];
    let mut next_pow_of_2 = 1;
    for (i, h) in h_bold.iter().enumerate() {
      running_h_sum += h;
      if (i + 1) == next_pow_of_2 {
        h_sum.push(running_h_sum);
        next_pow_of_2 *= 2;
      }
    }

    Ok(Generators { g, h, g_bold, h_bold, h_sum, transcript })
  }

  pub fn g(&self) -> C::G {
    self.g
  }

  pub fn h(&self) -> C::G {
    self.h
  }

  pub fn g_bold_slice(&self) -> &[C::G] {
    &self.g_bold
  }

  pub fn h_bold_slice(&self) -> &[C::G] {
    &self.h_bold
  }

  /// Reduce a set of generators to the quantity necessary to support a certain amount of
  /// in-circuit multiplications/terms in a Pedersen vector commitment.
  ///
  /// Returns None if the generators reduced are insufficient to provide this many generators.
  pub fn reduce(&self, generators: usize) -> Option<ProofGenerators<'_, T, C>> {
    // Round to the nearest power of 2
    let generators = padded_pow_of_2(generators);
    if generators > self.g_bold.len() {
      None?;
    }

    let mut transcript = self.transcript.clone();
    transcript.append_message(b"used_generators", u32::try_from(generators).unwrap().to_le_bytes());

    let mut pow_of_2 = 0;
    while (1 << pow_of_2) != generators {
      pow_of_2 += 1;
    }

    Some(ProofGenerators {
      g: &self.g,
      h: &self.h,

      g_bold: &self.g_bold[.. generators],
      h_bold: &self.h_bold[.. generators],
      h_sum: self.h_sum[pow_of_2],

      transcript: transcript.challenge(b"summary"),
    })
  }
}

impl<'a, T: 'static + Transcript, C: Ciphersuite> ProofGenerators<'a, T, C> {
  pub(crate) fn len(&self) -> usize {
    self.g_bold.len()
  }

  pub(crate) fn g(&self) -> C::G {
    *self.g
  }

  pub(crate) fn h(&self) -> C::G {
    *self.h
  }

  pub(crate) fn g_bold(&self, i: usize) -> C::G {
    self.g_bold[i]
  }

  pub(crate) fn h_bold(&self, i: usize) -> C::G {
    self.h_bold[i]
  }

  pub(crate) fn h_sum(&self) -> C::G {
    self.h_sum
  }

  pub(crate) fn g_bold_slice(&self) -> &[C::G] {
    self.g_bold
  }

  pub(crate) fn h_bold_slice(&self) -> &[C::G] {
    self.h_bold
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Zeroize)]
pub struct PedersenCommitment<C: Ciphersuite> {
  pub value: C::F,
  pub mask: C::F,
}

impl<C: Ciphersuite> PedersenCommitment<C> {
  pub fn commit(&self, g: C::G, h: C::G) -> C::G {
    multiexp(&[(self.value, g), (self.mask, h)])
  }
}

#[derive(Clone, PartialEq, Eq, Debug, Zeroize)]
pub struct PedersenVectorCommitment<C: Ciphersuite> {
  pub values: ScalarVector<C::F>,
  pub mask: C::F,
}

impl<C: Ciphersuite> PedersenVectorCommitment<C> {
  pub fn commit(&self, g_bold: &[C::G], h: C::G) -> C::G {
    let mut terms = vec![(self.mask, h)];
    for pair in self.values.0.iter().cloned().zip(g_bold.iter().cloned()) {
      terms.push(pair);
    }
    let res = multiexp(&terms);
    terms.zeroize();
    res
  }
}
