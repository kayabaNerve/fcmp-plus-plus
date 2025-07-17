use ff::Field;
use std_shims::vec::Vec;

pub struct BatchInverse;

impl BatchInverse {
  /// Compute products required for the batch inversion.
  /// Provide optional Vec to avoid allocating a new one.
  pub fn products<'a, F, I>(mut elems: I, space: Option<Vec<F>>) -> Vec<F>
  where
    F: Field,
    I: Iterator<Item = &'a F>,
  {
    let mut products = space.unwrap_or_else(|| Vec::with_capacity(256));
    products.truncate(0);
    let mut acc = F::ONE;
    while let Some(elem) = elems.next() {
      acc *= *elem;
      products.push(acc);
    }
    assert_ne!(acc, F::ZERO, "tried to batch invert a 0");
    products
  }

  /// Invert elements using the products computed, the iterator
  /// must be in the reverse order of that one provided to `Self::products`
  pub fn invert<'a, F, I>(mut elems: I, products: &[F])
  where
    F: Field,
    I: Iterator<Item = &'a mut F>,
  {
    let mut all_inverses = products.last().unwrap().invert().unwrap();
    let mut products = products.iter().rev().skip(1);

    loop {
      let elem = elems.next();
      let product = products.next();

      match (elem, product) {
        (Some(elem), Some(product)) => {
          let new_elem: F = all_inverses * product;
          all_inverses.mul_assign(&*elem);
          *elem = new_elem;
        }
        (Some(elem), None) => {
          *elem = all_inverses;
          break;
        }
        _ => unreachable!(),
      }
    }
  }

  pub fn invert_slice<F: Field>(slice: &mut [F]) {
    let space: Vec<F> = Vec::with_capacity(slice.len());
    let elems = slice.iter();
    let products = Self::products(elems, Some(space));
    let elems = slice.iter_mut().rev();
    Self::invert(elems, &products);
  }
}

#[test]
fn inversion() {
  use pasta_curves::Fp;
  let vals = [2, 5, 25, 235, 23, 324, 432, 4_u64];
  let vals = vals.map(Fp::from);
  let mut inverses = vals.clone();
  BatchInverse::invert_slice(&mut inverses);
  for i in 0 .. vals.len() {
    assert_eq!(vals[i] * inverses[i], Fp::ONE);
  }
}
