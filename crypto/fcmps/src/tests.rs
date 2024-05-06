use rand_core::OsRng;

use transcript::RecommendedTranscript;

use multiexp::multiexp_vartime;
use ciphersuite::{group::Group, Ciphersuite, Ed25519, Selene, Helios};

use crate::*;

fn random_output() -> Output<Ed25519> {
  let O = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  let I = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  let C = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  Output { O, I, C }
}

#[inline(never)]
fn verify_fn(
  proof: Fcmp<Selene, Helios>,
  params: &FcmpParams<RecommendedTranscript, Selene, Helios>,
  root: TreeRoot<Selene, Helios>,
  layer_lens: Vec<usize>,
  input: Input<<Selene as Ciphersuite>::F>,
) {
  let instant = std::time::Instant::now();

  let mut verifier_1 = params.curve_1_generators.batch_verifier();
  let mut verifier_2 = params.curve_2_generators.batch_verifier();

  for _ in 0 .. 100 {
    proof.clone().verify::<_, _, Ed25519>(
      &mut OsRng,
      &mut RecommendedTranscript::new(b"FCMP Test"),
      &mut verifier_1,
      &mut verifier_2,
      params,
      root,
      layer_lens.clone(),
      input,
    );
  }

  assert!(params.curve_1_generators.verify(verifier_1));
  assert!(params.curve_2_generators.verify(verifier_2));

  dbg!((std::time::Instant::now() - instant).as_millis());
}

#[test]
fn test() {
  let G = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  let T = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  let U = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  let V = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);

  let curve_1_generators = generalized_bulletproofs::tests::generators::<Selene>(512);
  let curve_2_generators = generalized_bulletproofs::tests::generators::<Helios>(512);
  let params = FcmpParams::<_, _, _>::new::<Ed25519>(
    curve_1_generators.clone(),
    curve_2_generators.clone(),
    <Selene as Ciphersuite>::G::random(&mut OsRng),
    <Helios as Ciphersuite>::G::random(&mut OsRng),
    G,
    T,
    U,
    V,
  );

  let output = random_output();
  let blinds = OutputBlinds::new(&mut OsRng);
  let blinds = blinds.prepare(G, T, U, V, output);
  let input = blinds.input;

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
          <Ed25519 as Ciphersuite>::G::to_xy(output.C).0,
        ]
      })
      .zip(curve_1_generators.g_bold_slice())
    {
      multiexp.push((scalar, *point));
    }
    params.curve_1_hash_init + multiexp_vartime(&multiexp)
  });
  let mut helios_hash;

  let mut curve_2_layers = vec![];
  let mut curve_1_layers = vec![];
  for _ in 0 .. 2 {
    let mut curve_2_layer = vec![];
    for _ in 0 .. usize::try_from(OsRng.next_u64() % 4).unwrap() + 1 {
      curve_2_layer.push(<Selene as Ciphersuite>::G::random(&mut OsRng));
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
      params.curve_2_hash_init + multiexp_vartime(&multiexp)
    });

    curve_2_layers.push(curve_2_layer);

    let mut curve_1_layer = vec![];
    for _ in 0 .. usize::try_from(OsRng.next_u64() % 4).unwrap() + 1 {
      curve_1_layer.push(<Helios as Ciphersuite>::G::random(&mut OsRng));
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
      params.curve_1_hash_init + multiexp_vartime(&multiexp)
    });

    curve_1_layers.push(curve_1_layer);
  }

  let mut layer_lens = vec![3 * leaves.len()];
  for (a, b) in curve_2_layers.iter().zip(&curve_1_layers) {
    layer_lens.push(a.len());
    layer_lens.push(b.len());
  }

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

  verify_fn(proof, &params, root, layer_lens, input);
}
