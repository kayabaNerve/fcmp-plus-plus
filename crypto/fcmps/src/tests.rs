use rand_core::OsRng;

use transcript::RecommendedTranscript;

use ciphersuite::{group::Group, Ciphersuite, Ed25519, Selene, Helios};

use crate::*;

#[allow(non_snake_case)]
#[test]
fn test() {
  let G = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  let T = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  let U = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  let V = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);

  let curve_1_generators = generalized_bulletproofs::tests::generators::<Selene>(512);
  let curve_2_generators = generalized_bulletproofs::tests::generators::<Helios>(512);
  let params =
    FcmpParams::<_, Ed25519, _, _> { curve_1_generators, curve_2_generators, G, T, U, V };

  let mut O = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  while Option::<<Selene as Ciphersuite>::F>::from(
    (<Selene as Ciphersuite>::F::ONE + <Ed25519 as Ciphersuite>::G::to_xy(O).1).sqrt(),
  )
  .is_none()
  {
    O += <Ed25519 as Ciphersuite>::G::generator();
  }
  let I = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  let mut C = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  while Option::<<Selene as Ciphersuite>::F>::from(
    (<Selene as Ciphersuite>::F::ONE + <Ed25519 as Ciphersuite>::G::to_xy(O).1).sqrt(),
  )
  .is_none()
  {
    C += <Ed25519 as Ciphersuite>::G::generator();
  }
  let output = Output { O, I, C };

  let blinds = OutputBlinds::new(&mut OsRng);
  let blinds = blinds.prepare(G, T, U, V, output);

  let branches = Branches { leaves: vec![output], curve_2_layers: vec![], curve_1_layers: vec![] };

  Fcmp::prove(
    &mut OsRng,
    &mut RecommendedTranscript::new(b""),
    &params,
    TreeRoot::<Selene, Helios>::C1(<Selene as Ciphersuite>::G::random(&mut OsRng)),
    output,
    blinds,
    branches,
  );
}
