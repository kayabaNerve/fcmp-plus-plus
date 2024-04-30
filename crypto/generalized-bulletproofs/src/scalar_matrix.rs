use zeroize::Zeroize;

use transcript::Transcript;

use ciphersuite::{group::ff::PrimeField, Ciphersuite};

use crate::ScalarVector;

/// A sparse matrix of scalars.
#[derive(Clone, PartialEq, Eq, Debug, Zeroize)]
pub struct ScalarMatrix<C: Ciphersuite> {
  // The highest index present in a row in this matrix.
  pub(crate) highest_index: usize,
  data: Vec<Vec<(usize, C::F)>>,
}

impl<C: Ciphersuite> ScalarMatrix<C> {
  #[allow(clippy::new_without_default)]
  pub fn new() -> Self {
    ScalarMatrix { highest_index: 0, data: vec![] }
  }

  // The first number from the paper's matrix size definitions, the amount of rows
  pub(crate) fn len(&self) -> usize {
    self.data.len()
  }

  /// Push a sparse row of scalars onto the matrix.
  pub fn push(&mut self, row: Vec<(usize, C::F)>) {
    let mut high_index = 0;
    for (i, _) in &row {
      if *i > high_index {
        high_index = *i;
      }
    }
    if self.highest_index < high_index {
      self.highest_index = high_index;
    }

    self.data.push(row);
  }

  pub(crate) fn mul_vec(&self, n: usize, vector: &ScalarVector<C::F>) -> ScalarVector<C::F> {
    assert_eq!(self.len(), vector.len());
    let mut res = ScalarVector::new(n);
    for (row, weight) in self.data.iter().zip(vector.0.iter()) {
      for (i, item) in row {
        res[*i] += *item * weight;
      }
    }
    res
  }

  pub(crate) fn transcript<T: 'static + Transcript>(
    &self,
    transcript: &mut T,
    label: &'static [u8],
  ) {
    transcript.append_message(b"length", u32::try_from(self.len()).unwrap().to_le_bytes());
    for vector in &self.data {
      transcript.append_message(b"row_count", u32::try_from(vector.len()).unwrap().to_le_bytes());
      for (i, scalar) in vector {
        transcript.append_message(b"i", u32::try_from(*i).unwrap().to_le_bytes());
        transcript.append_message(label, scalar.to_repr());
      }
    }
  }
}
