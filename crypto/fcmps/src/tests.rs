use rand_core::OsRng;

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
  iters: usize,
  batch: usize,
  proof: Fcmp<Selene, Helios>,
  params: &FcmpParams<Selene, Helios>,
  root: TreeRoot<Selene, Helios>,
  layer_lens: &[usize],
  input: Input<<Selene as Ciphersuite>::F>,
) {
  let mut times = vec![];
  for _ in 0 .. iters {
    let instant = std::time::Instant::now();

    let mut verifier_1 = params.curve_1_generators.batch_verifier();
    let mut verifier_2 = params.curve_2_generators.batch_verifier();

    for _ in 0 .. batch {
      proof.verify::<_, Ed25519>(
        &mut OsRng,
        &mut verifier_1,
        &mut verifier_2,
        params,
        root,
        layer_lens,
        input,
      );
    }

    assert!(params.curve_1_generators.verify(verifier_1));
    assert!(params.curve_2_generators.verify(verifier_2));

    times.push((std::time::Instant::now() - instant).as_millis());
  }
  times.sort();
  dbg!((batch, times[times.len() / 2]));
}

#[test]
fn test() {
  let G = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  let T = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  let U = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  let V = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);

  let curve_1_generators = generalized_bulletproofs::tests::generators::<Selene>(256);
  let curve_2_generators = generalized_bulletproofs::tests::generators::<Helios>(256);
  let params = FcmpParams::<_, _>::new::<Ed25519>(
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

  const LAYER_ONE_LEN: usize = 38;
  const LAYER_TWO_LEN: usize = 18;
  const TARGET_LAYERS: usize = 8;

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
  loop {
    let mut curve_2_layer = vec![];
    for _ in 0 .. LAYER_TWO_LEN {
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

    if (1 + curve_1_layers.len() + curve_2_layers.len()) == TARGET_LAYERS {
      break;
    }

    let mut curve_1_layer = vec![];
    for _ in 0 .. LAYER_ONE_LEN {
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

    if (1 + curve_1_layers.len() + curve_2_layers.len()) == TARGET_LAYERS {
      break;
    }
  }
  assert_eq!(curve_1_layers.len(), 3);
  assert_eq!(curve_2_layers.len(), 4);

  let mut layer_lens = vec![3 * LAYER_ONE_LEN];
  for _ in curve_2_layers.iter().zip(&curve_1_layers) {
    layer_lens.push(LAYER_TWO_LEN);
    layer_lens.push(LAYER_ONE_LEN);
  }
  if curve_2_layers.len() > curve_1_layers.len() {
    layer_lens.push(LAYER_TWO_LEN);
  }
  assert_eq!(layer_lens.len(), TARGET_LAYERS);

  let root = if let Some(selene_hash) = selene_hash {
    TreeRoot::<Selene, Helios>::C1(selene_hash)
  } else {
    TreeRoot::<Selene, Helios>::C2(helios_hash.unwrap())
  };

  let branches = Branches { leaves, curve_2_layers, curve_1_layers };

  let prove_start = std::time::Instant::now();
  for _ in 0 .. 100 {
    let blinds = OutputBlinds::new(&mut OsRng);
    let blinds = blinds.prepare(G, T, U, V, output);

    let proof = Fcmp::prove(&mut OsRng, &params, root, output, blinds, branches.clone());

    core::hint::black_box(proof);
  }
  dbg!((std::time::Instant::now() - prove_start).as_millis());

  let blinds = OutputBlinds::new(&mut OsRng);
  let blinds = blinds.prepare(G, T, U, V, output);
  let input = blinds.input;

  let proof = Fcmp::prove(&mut OsRng, &params, root, output, blinds, branches);

  verify_fn(100, 1, proof.clone(), &params, root, &layer_lens, input);
  verify_fn(100, 10, proof.clone(), &params, root, &layer_lens, input);
  verify_fn(100, 100, proof.clone(), &params, root, &layer_lens, input);
}
