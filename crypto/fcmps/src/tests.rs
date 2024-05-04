use rand_core::OsRng;

use transcript::RecommendedTranscript;

use multiexp::multiexp_vartime;
use ciphersuite::{group::Group, Ciphersuite, Ed25519, Selene, Helios};

use crate::*;

fn make_permissible<C: DivisorCurve>(generator: C, mut point: C) -> C {
  while Option::<C::FieldElement>::from((C::FieldElement::ONE + C::to_xy(point).1).sqrt()).is_none()
  {
    point += generator;
  }
  point
}

#[allow(non_snake_case)]
fn random_permissible_point<C: Ciphersuite>() -> C::G
where
  C::G: DivisorCurve,
{
  make_permissible(C::G::generator(), C::G::random(&mut OsRng))
}

#[allow(non_snake_case)]
fn random_output() -> Output<Ed25519> {
  let O = random_permissible_point::<Ed25519>();
  let I = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  let C = random_permissible_point::<Ed25519>();
  Output { O, I, C }
}

#[allow(non_snake_case)]
#[test]
fn test() {
  let G = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  let T = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  let U = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  let V = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);

  let curve_1_generators = generalized_bulletproofs::tests::generators::<Selene>(512);
  let curve_2_generators = generalized_bulletproofs::tests::generators::<Helios>(512);
  let params = FcmpParams::<_, Ed25519, _, _> {
    curve_1_generators: curve_1_generators.clone(),
    curve_2_generators: curve_2_generators.clone(),
    G,
    T,
    U,
    V,
  };

  let output = random_output();
  let blinds = OutputBlinds::new(&mut OsRng);
  let blinds = blinds.prepare(G, T, U, V, output);

  let mut leaves = vec![];
  for _ in 0 .. usize::try_from(OsRng.next_u64() % 4).unwrap() + 1 {
    leaves.push(random_output());
  }
  let leaves_len = leaves.len();
  leaves[usize::try_from(OsRng.next_u64()).unwrap() % leaves_len] = output;

  let mut selene_hash = Some({
    let mut multiexp = vec![];
    for (scalar, point) in leaves
      .iter()
      .flat_map(|output| {
        [
          <Ed25519 as Ciphersuite>::G::to_xy(output.O).0,
          <Ed25519 as Ciphersuite>::G::to_xy(output.I).0,
          <Ed25519 as Ciphersuite>::G::to_xy(output.I).1,
          <Ed25519 as Ciphersuite>::G::to_xy(output.C).0,
        ]
      })
      .zip(curve_1_generators.g_bold_slice())
    {
      multiexp.push((scalar, *point));
    }
    make_permissible(curve_1_generators.h(), multiexp_vartime(&multiexp))
  });
  let mut helios_hash;

  let mut curve_2_layers = vec![];
  let mut curve_1_layers = vec![];
  for _ in 0 .. 2 {
    let mut curve_2_layer = vec![];
    for _ in 0 .. usize::try_from(OsRng.next_u64() % 4).unwrap() + 1 {
      curve_2_layer.push(random_permissible_point::<Selene>());
    }
    let layer_len = curve_2_layer.len();
    curve_2_layer[usize::try_from(OsRng.next_u64()).unwrap() % layer_len] =
      selene_hash.take().unwrap();
    let curve_2_layer = curve_2_layer
      .into_iter()
      .map(|point| <Selene as Ciphersuite>::G::to_xy(point).0)
      .collect::<Vec<_>>();

    helios_hash = Some({
      let mut multiexp = vec![];
      for (scalar, point) in curve_2_layer.iter().zip(curve_2_generators.g_bold_slice()) {
        multiexp.push((*scalar, *point));
      }
      make_permissible(curve_2_generators.h(), multiexp_vartime(&multiexp))
    });

    curve_2_layers.push(curve_2_layer);

    let mut curve_1_layer = vec![];
    for _ in 0 .. usize::try_from(OsRng.next_u64() % 4).unwrap() + 1 {
      curve_1_layer.push(random_permissible_point::<Helios>());
    }
    let layer_len = curve_1_layer.len();
    curve_1_layer[usize::try_from(OsRng.next_u64()).unwrap() % layer_len] =
      helios_hash.take().unwrap();
    let curve_1_layer = curve_1_layer
      .into_iter()
      .map(|point| <Helios as Ciphersuite>::G::to_xy(point).0)
      .collect::<Vec<_>>();

    selene_hash = Some({
      let mut multiexp = vec![];
      for (scalar, point) in curve_1_layer.iter().zip(curve_1_generators.g_bold_slice()) {
        multiexp.push((*scalar, *point));
      }
      make_permissible(curve_1_generators.h(), multiexp_vartime(&multiexp))
    });

    curve_1_layers.push(curve_1_layer);
  }

  let branches = Branches { leaves, curve_2_layers, curve_1_layers };

  Fcmp::prove(
    &mut OsRng,
    &mut RecommendedTranscript::new(b"FCMP Test"),
    &params,
    TreeRoot::<Selene, Helios>::C1(<Selene as Ciphersuite>::G::random(&mut OsRng)),
    output,
    blinds,
    branches,
  );
}
