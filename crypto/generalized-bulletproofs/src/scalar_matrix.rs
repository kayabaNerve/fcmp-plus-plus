use zeroize::Zeroize;

use ciphersuite::Ciphersuite;

use crate::ScalarVector;

/// A sparse matrix of scalars.
#[derive(Clone, PartialEq, Eq, Debug, Zeroize)]
pub struct ScalarMatrix<C: Ciphersuite> {
  // The highest index present in a row in this matrix.
  pub(crate) highest_index: usize,
  pub(crate) data: Vec<Vec<(usize, C::F)>>,
}

impl<C: Ciphersuite> ScalarMatrix<C> {
  /// Create a new ScalarMatrix.
  #[allow(clippy::new_without_default)]
  pub fn new() -> Self {
    ScalarMatrix { highest_index: 0, data: vec![] }
  }

  // The first number from the paper's matrix size definitions, the amount of rows
  pub(crate) fn len(&self) -> usize {
    self.data.len()
  }

  /// Push a sparse row of scalars onto the matrix.
  ///
  /// If this row has multiple scalars for the same index, they'll be summed.
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
}
