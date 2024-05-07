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

fn random_permissible_point<C: Ciphersuite>() -> C::G
where
  C::G: DivisorCurve,
{
  make_permissible(C::G::generator(), C::G::random(&mut OsRng))
}

fn random_output() -> Output<Ed25519> {
  let O = random_permissible_point::<Ed25519>();
  let I = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  let C = random_permissible_point::<Ed25519>();
  Output { O, I, C }
}

#[test]
fn test() {
  let G = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  let T = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  let U = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  let V = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);

  let curve_1_generators = generalized_bulletproofs::tests::generators::<Selene>(256);
  let curve_2_generators = generalized_bulletproofs::tests::generators::<Helios>(256);
  let params = FcmpParams::<_, _, _>::new::<Ed25519>(
    curve_1_generators.clone(),
    curve_2_generators.clone(),
    G,
    T,
    U,
    V,
  );

  let output = random_output();
  let blinds = OutputBlinds::new(&mut OsRng);
  let blinds = blinds.prepare(G, T, U, V, output);
  let input = blinds.input;

  const LAYER_ONE_LEN: usize = 37;
  const LAYER_TWO_LEN: usize = 17;

  let mut leaves = vec![];
  for _ in 0 .. LAYER_ONE_LEN {
    leaves.push(random_output());
  }
  leaves[usize::try_from(OsRng.next_u64()).unwrap() % LAYER_ONE_LEN] = output;

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
  for layer_pair in 0 .. 4 {
    let mut curve_2_layer = vec![];
    for _ in 0 .. LAYER_TWO_LEN {
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

    if layer_pair == 3 {
      break;
    }

    let mut curve_1_layer = vec![];
    for _ in 0 .. LAYER_ONE_LEN {
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
  assert_eq!(curve_1_layers.len(), 3);
  assert_eq!(curve_2_layers.len(), 4);

  let mut layer_lens = vec![4 * LAYER_ONE_LEN];
  for (a, b) in curve_2_layers.iter().zip(&curve_1_layers) {
    layer_lens.push(LAYER_TWO_LEN);
    layer_lens.push(LAYER_ONE_LEN);
  }
  layer_lens.push(LAYER_TWO_LEN);

  let branches = Branches { leaves, curve_2_layers, curve_1_layers };

  let root = TreeRoot::<Selene, Helios>::C1(<Selene as Ciphersuite>::G::random(&mut OsRng));

  let proof = Fcmp::prove(
    &mut OsRng,
    &mut RecommendedTranscript::new(b"FCMP Test"),
    &params,
    root,
    output,
    blinds,
    branches,
  );

  let mut verifier_1 = params.curve_1_generators.batch_verifier();
  let mut verifier_2 = params.curve_2_generators.batch_verifier();

  let instant = std::time::Instant::now();
  for _ in 0 .. 10 {
    proof.clone().verify::<_, _, Ed25519>(
      &mut OsRng,
      &mut RecommendedTranscript::new(b"FCMP Test"),
      &mut verifier_1,
      &mut verifier_2,
      &params,
      root,
      layer_lens.clone(),
      input,
    );
  }
  assert!(params.curve_1_generators.verify(verifier_1));
  assert!(params.curve_2_generators.verify(verifier_2));
  dbg!((std::time::Instant::now() - instant).as_millis());
}
