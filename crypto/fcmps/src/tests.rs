use rand_core::OsRng;

use generic_array::typenum::{Sum, Diff, Quot, U, U1, U2};

use multiexp::multiexp_vartime;
use ciphersuite::{group::Group, Ciphersuite, Ed25519, Selene, Helios};
use ec_divisors::ScalarDecomposition;

use crate::{*, tree::hash_grow};

const LAYER_ONE_LEN: usize = 38;
const LAYER_TWO_LEN: usize = 18;
const TARGET_LAYERS: usize = 8;

struct Ed25519Params;
impl DiscreteLogParameters for Ed25519Params {
  type ScalarBits = U<{ <<Ed25519 as Ciphersuite>::F as PrimeField>::NUM_BITS as usize }>;
  type XCoefficients = Quot<Sum<Self::ScalarBits, U1>, U2>;
  type XCoefficientsMinusOne = Diff<Self::XCoefficients, U1>;
  type YxCoefficients = Diff<Quot<Sum<Self::ScalarBits, U1>, U2>, U2>;
}

struct SeleneParams;
impl DiscreteLogParameters for SeleneParams {
  type ScalarBits = U<{ <<Selene as Ciphersuite>::F as PrimeField>::NUM_BITS as usize }>;
  type XCoefficients = Quot<Sum<Self::ScalarBits, U1>, U2>;
  type XCoefficientsMinusOne = Diff<Self::XCoefficients, U1>;
  type YxCoefficients = Diff<Quot<Sum<Self::ScalarBits, U1>, U2>, U2>;
}

struct HeliosParams;
impl DiscreteLogParameters for HeliosParams {
  type ScalarBits = U<{ <<Helios as Ciphersuite>::F as PrimeField>::NUM_BITS as usize }>;
  type XCoefficients = Quot<Sum<Self::ScalarBits, U1>, U2>;
  type XCoefficientsMinusOne = Diff<Self::XCoefficients, U1>;
  type YxCoefficients = Diff<Quot<Sum<Self::ScalarBits, U1>, U2>, U2>;
}

#[derive(Clone)]
struct MoneroCurves;
impl FcmpCurves for MoneroCurves {
  type OC = Ed25519;
  type OcParameters = Ed25519Params;
  type C1 = Selene;
  type C1Parameters = SeleneParams;
  type C2 = Helios;
  type C2Parameters = HeliosParams;
}

#[allow(clippy::type_complexity)]
fn random_params(
  input_limit: usize,
) -> (
  <Ed25519 as Ciphersuite>::G,
  <Ed25519 as Ciphersuite>::G,
  <Ed25519 as Ciphersuite>::G,
  <Ed25519 as Ciphersuite>::G,
  FcmpParams<MoneroCurves>,
) {
  let G = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  let T = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  let U = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  let V = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);

  let params = FcmpParams::<MoneroCurves>::new(
    generalized_bulletproofs::tests::generators::<Selene>(input_limit * 256),
    generalized_bulletproofs::tests::generators::<Helios>(input_limit * 128),
    // Hash init generators
    <Selene as Ciphersuite>::G::random(&mut OsRng),
    <Helios as Ciphersuite>::G::random(&mut OsRng),
    // G, T, U, V
    G,
    T,
    U,
    V,
  );

  (G, T, U, V, params)
}

fn random_output() -> Output<<Ed25519 as Ciphersuite>::G> {
  let O = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  let I = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  let C = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  Output::new(O, I, C).unwrap()
}

fn random_path(
  params: &FcmpParams<MoneroCurves>,
  layers: usize,
) -> (Path<MoneroCurves>, Vec<usize>, TreeRoot<Selene, Helios>) {
  assert!(layers >= 1);

  let mut layer_lens = vec![3 * LAYER_ONE_LEN];
  let mut leaves = vec![];
  while leaves.len() < LAYER_ONE_LEN {
    leaves.push(random_output());
  }

  let output =
    leaves[usize::try_from(OsRng.next_u64() % u64::try_from(leaves.len()).unwrap()).unwrap()];

  let mut selene_hash = Some({
    let mut multiexp = vec![];
    for (scalar, point) in leaves
      .iter()
      .flat_map(|output| {
        [
          <Ed25519 as Ciphersuite>::G::to_xy(output.O).unwrap().0,
          <Ed25519 as Ciphersuite>::G::to_xy(output.I).unwrap().0,
          <Ed25519 as Ciphersuite>::G::to_xy(output.C).unwrap().0,
        ]
      })
      .zip(params.curve_1_generators.g_bold_slice())
    {
      multiexp.push((scalar, *point));
    }
    params.curve_1_hash_init + multiexp_vartime(&multiexp)
  });
  let mut helios_hash = None;

  let mut curve_2_layers = vec![];
  let mut curve_1_layers = vec![];
  loop {
    if layers == 1 {
      break;
    }

    let mut curve_2_layer = vec![];
    while curve_2_layer.len() < LAYER_TWO_LEN {
      curve_2_layer.push(<Selene as Ciphersuite>::G::random(&mut OsRng));
    }
    let layer_len = curve_2_layer.len();
    curve_2_layer[usize::try_from(OsRng.next_u64()).unwrap() % layer_len] =
      selene_hash.take().unwrap();
    let curve_2_layer = curve_2_layer
      .into_iter()
      .map(|point| <Selene as Ciphersuite>::G::to_xy(point).unwrap().0)
      .collect::<Vec<_>>();

    helios_hash = Some({
      let mut multiexp = vec![];
      for (scalar, point) in curve_2_layer.iter().zip(params.curve_2_generators.g_bold_slice()) {
        multiexp.push((*scalar, *point));
      }
      params.curve_2_hash_init + multiexp_vartime(&multiexp)
    });

    curve_2_layers.push(curve_2_layer);
    layer_lens.push(LAYER_TWO_LEN);

    if (1 + curve_1_layers.len() + curve_2_layers.len()) == layers {
      break;
    }

    let mut curve_1_layer = vec![];
    while curve_1_layer.len() < LAYER_ONE_LEN {
      curve_1_layer.push(<Helios as Ciphersuite>::G::random(&mut OsRng));
    }
    let layer_len = curve_1_layer.len();
    curve_1_layer[usize::try_from(OsRng.next_u64()).unwrap() % layer_len] =
      helios_hash.take().unwrap();
    let curve_1_layer = curve_1_layer
      .into_iter()
      .map(|point| <Helios as Ciphersuite>::G::to_xy(point).unwrap().0)
      .collect::<Vec<_>>();

    selene_hash = Some({
      let mut multiexp = vec![];
      for (scalar, point) in curve_1_layer.iter().zip(params.curve_1_generators.g_bold_slice()) {
        multiexp.push((*scalar, *point));
      }
      params.curve_1_hash_init + multiexp_vartime(&multiexp)
    });

    curve_1_layers.push(curve_1_layer);
    layer_lens.push(LAYER_ONE_LEN);

    if (1 + curve_1_layers.len() + curve_2_layers.len()) == layers {
      break;
    }
  }

  let root = if let Some(selene_hash) = selene_hash {
    TreeRoot::<Selene, Helios>::C1(selene_hash)
  } else {
    TreeRoot::<Selene, Helios>::C2(helios_hash.unwrap())
  };

  (Path { output, leaves, curve_2_layers, curve_1_layers }, layer_lens, root)
}

fn random_paths(
  params: &FcmpParams<MoneroCurves>,
  layers: usize,
  paths: usize,
) -> (Vec<Path<MoneroCurves>>, Vec<usize>, TreeRoot<Selene, Helios>) {
  assert!(paths >= 1);
  assert!(paths <= LAYER_ONE_LEN.min(LAYER_TWO_LEN));

  let mut res = vec![];
  let mut layer_lens = None;
  for _ in 0 .. paths {
    let (path, these_layer_lens, _root) = random_path(params, layers);
    res.push(path);
    if let Some(layer_lens) = &layer_lens {
      assert_eq!(&these_layer_lens, layer_lens);
    } else {
      layer_lens = Some(these_layer_lens);
    }
  }
  let layer_lens = layer_lens.unwrap();

  // Pop each path's top layer
  // Then push a new top layer which is unified for all paths
  // 1st layer has a C1 root (so the top layer is the leaves)
  // 2nd layer has a C2 root (so the top layer is C1)
  // 3rd layer has a C1 root (so the top layer is C2)
  let root = if layers == 1 {
    assert_eq!(*layer_lens.last().unwrap(), res[0].leaves.len());

    let mut outputs = vec![];
    for path in &res {
      outputs.push(path.output);
    }
    while outputs.len() < LAYER_ONE_LEN {
      outputs.push(random_output());
    }
    let mut shuffled_outputs = vec![];
    while !outputs.is_empty() {
      let i = usize::try_from(OsRng.next_u64() % u64::try_from(outputs.len()).unwrap()).unwrap();
      shuffled_outputs.push(outputs.swap_remove(i));
    }

    for path in &mut res {
      path.leaves = shuffled_outputs.clone();
    }

    let mut new_leaves_layer = vec![];
    for output in shuffled_outputs {
      new_leaves_layer.push(<Ed25519 as Ciphersuite>::G::to_xy(output.O).unwrap().0);
      new_leaves_layer.push(<Ed25519 as Ciphersuite>::G::to_xy(output.I).unwrap().0);
      new_leaves_layer.push(<Ed25519 as Ciphersuite>::G::to_xy(output.C).unwrap().0);
    }

    TreeRoot::C1(
      hash_grow(
        &params.curve_1_generators,
        params.curve_1_hash_init,
        0,
        <Selene as Ciphersuite>::F::ZERO,
        &new_leaves_layer,
      )
      .unwrap(),
    )
  } else if (layers % 2) == 0 {
    assert_eq!(*layer_lens.last().unwrap(), res[0].curve_2_layers.last().unwrap().len());

    let mut branch = vec![];
    for path in &res {
      branch.push(
        <Selene as Ciphersuite>::G::to_xy(if let Some(branch) = path.curve_1_layers.last() {
          hash_grow(
            &params.curve_1_generators,
            params.curve_1_hash_init,
            0,
            <Selene as Ciphersuite>::F::ZERO,
            branch,
          )
          .unwrap()
        } else {
          let mut leaves_layer = vec![];
          for output in &path.leaves {
            leaves_layer.push(<Ed25519 as Ciphersuite>::G::to_xy(output.O).unwrap().0);
            leaves_layer.push(<Ed25519 as Ciphersuite>::G::to_xy(output.I).unwrap().0);
            leaves_layer.push(<Ed25519 as Ciphersuite>::G::to_xy(output.C).unwrap().0);
          }

          hash_grow(
            &params.curve_1_generators,
            params.curve_1_hash_init,
            0,
            <Selene as Ciphersuite>::F::ZERO,
            &leaves_layer,
          )
          .unwrap()
        })
        .unwrap()
        .0,
      );
    }
    while branch.len() < LAYER_TWO_LEN {
      branch.push(<Helios as Ciphersuite>::F::random(&mut OsRng));
    }
    let mut shuffled_branch = vec![];
    while !branch.is_empty() {
      let i = usize::try_from(OsRng.next_u64() % u64::try_from(branch.len()).unwrap()).unwrap();
      shuffled_branch.push(branch.swap_remove(i));
    }

    for path in &mut res {
      *path.curve_2_layers.last_mut().unwrap() = shuffled_branch.clone();
    }

    TreeRoot::C2(
      hash_grow(
        &params.curve_2_generators,
        params.curve_2_hash_init,
        0,
        <Helios as Ciphersuite>::F::ZERO,
        &shuffled_branch,
      )
      .unwrap(),
    )
  } else {
    assert_eq!(*layer_lens.last().unwrap(), res[0].curve_1_layers.last().unwrap().len());

    let mut branch = vec![];
    for path in &res {
      branch.push(
        <Helios as Ciphersuite>::G::to_xy({
          let branch = path.curve_2_layers.last().unwrap();
          hash_grow(
            &params.curve_2_generators,
            params.curve_2_hash_init,
            0,
            <Helios as Ciphersuite>::F::ZERO,
            branch,
          )
          .unwrap()
        })
        .unwrap()
        .0,
      );
    }
    while branch.len() < LAYER_ONE_LEN {
      branch.push(<Selene as Ciphersuite>::F::random(&mut OsRng));
    }
    let mut shuffled_branch = vec![];
    while !branch.is_empty() {
      let i = usize::try_from(OsRng.next_u64() % u64::try_from(branch.len()).unwrap()).unwrap();
      shuffled_branch.push(branch.swap_remove(i));
    }

    for path in &mut res {
      *path.curve_1_layers.last_mut().unwrap() = shuffled_branch.clone();
    }

    TreeRoot::C1(
      hash_grow(
        &params.curve_1_generators,
        params.curve_1_hash_init,
        0,
        <Selene as Ciphersuite>::F::ZERO,
        &shuffled_branch,
      )
      .unwrap(),
    )
  };

  (res, layer_lens, root)
}

fn random_output_blinds(
  G: <Ed25519 as Ciphersuite>::G,
  T: <Ed25519 as Ciphersuite>::G,
  U: <Ed25519 as Ciphersuite>::G,
  V: <Ed25519 as Ciphersuite>::G,
) -> OutputBlinds<<Ed25519 as Ciphersuite>::G> {
  let output_blinds_start = std::time::Instant::now();
  let res = OutputBlinds::new(
    OBlind::new(
      T,
      ScalarDecomposition::new(<Ed25519 as Ciphersuite>::F::random(&mut OsRng)).unwrap(),
    ),
    IBlind::new(
      U,
      V,
      ScalarDecomposition::new(<Ed25519 as Ciphersuite>::F::random(&mut OsRng)).unwrap(),
    ),
    IBlindBlind::new(
      T,
      ScalarDecomposition::new(<Ed25519 as Ciphersuite>::F::random(&mut OsRng)).unwrap(),
    ),
    CBlind::new(
      G,
      ScalarDecomposition::new(<Ed25519 as Ciphersuite>::F::random(&mut OsRng)).unwrap(),
    ),
  );
  println!(
    "Output blinds took {}ms to calculate",
    (std::time::Instant::now() - output_blinds_start).as_millis()
  );
  res
}

fn blind_branches(
  params: &FcmpParams<MoneroCurves>,
  branches: Branches<MoneroCurves>,
  output_blinds: Vec<OutputBlinds<<Ed25519 as Ciphersuite>::G>>,
) -> BranchesWithBlinds<MoneroCurves> {
  let branch_blinds_start = std::time::Instant::now();
  let mut branches_1_blinds = vec![];
  for _ in 0 .. branches.necessary_c1_blinds() {
    branches_1_blinds.push(BranchBlind::<<Selene as Ciphersuite>::G>::new(
      params.curve_1_generators.h(),
      ScalarDecomposition::new(<Selene as Ciphersuite>::F::random(&mut OsRng)).unwrap(),
    ));
  }

  let mut branches_2_blinds = vec![];
  for _ in 0 .. branches.necessary_c2_blinds() {
    branches_2_blinds.push(BranchBlind::<<Helios as Ciphersuite>::G>::new(
      params.curve_2_generators.h(),
      ScalarDecomposition::new(<Helios as Ciphersuite>::F::random(&mut OsRng)).unwrap(),
    ));
  }
  println!(
    "{} C1 branch blinds and {} C2 branch blinds took {}ms to calculate",
    branches.necessary_c1_blinds(),
    branches.necessary_c2_blinds(),
    (std::time::Instant::now() - branch_blinds_start).as_millis()
  );

  branches.blind(output_blinds, branches_1_blinds, branches_2_blinds).unwrap()
}

#[inline(never)]
fn verify_fn(
  iters: usize,
  batch: usize,
  proof: Fcmp<MoneroCurves>,
  params: &FcmpParams<MoneroCurves>,
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
      proof.verify(&mut OsRng, &mut verifier_1, &mut verifier_2, params, root, layer_lens, input);
    }

    assert!(params.curve_1_generators.verify(verifier_1));
    assert!(params.curve_2_generators.verify(verifier_2));

    times.push((std::time::Instant::now() - instant).as_millis());
  }
  times.sort();
  println!("Median time to verify {batch} proof(s) was {}ms (n={iters})", times[times.len() / 2]);
}

#[test]
fn test_single_input() {
  let (G, T, U, V, params) = random_params(1);

  let output_blinds = random_output_blinds(G, T, U, V);

  for layers in 1 ..= TARGET_LAYERS {
    println!("Testing a proof with 1 input and {layers} layers");

    let (path, layer_lens, root) = random_path(&params, layers);
    let output = path.output;

    let branches = Branches::new(vec![path]).unwrap();

    let input = output_blinds.blind(&output).unwrap();

    let proof = Fcmp::prove(
      &mut OsRng,
      &params,
      root,
      blind_branches(&params, branches, vec![output_blinds.clone()]),
    );

    verify_fn(1, 1, proof.clone(), &params, root, &layer_lens, input);
  }
}

#[test]
fn test_multiple_inputs() {
  let (G, T, U, V, params) = random_params(8);

  for layers in 1 ..= TARGET_LAYERS {
    for paths in 2 ..= 8 {
      println!("Testing a proof with {paths} inputs and {layers} layers");

      let (paths, layer_lens, root) = random_paths(&params, TARGET_LAYERS, paths);

      let mut output_blinds = vec![];
      for _ in 0 .. paths.len() {
        output_blinds.push(random_output_blinds(G, T, U, V));
      }
      //let input = output_blinds.blind(&output).unwrap();

      let branches = Branches::new(paths).unwrap();

      let proof =
        Fcmp::prove(&mut OsRng, &params, root, blind_branches(&params, branches, output_blinds));

      // verify_fn(1, 1, proof.clone(), &params, root, &layer_lens, input);
    }
  }

  // TODO: Batch verify all of these proofs
}

#[test]
fn prove_benchmark() {
  const RUNS: usize = 10;
  let inputs = 1; // TODO: Test with a variety of inputs

  let (G, T, U, V, params) = random_params(inputs);
  let (path, _layer_lens, root) = random_path(&params, TARGET_LAYERS);

  let mut set_size = 1u64;
  for i in 0 .. TARGET_LAYERS {
    if i % 2 == 0 {
      set_size *= u64::try_from(LAYER_ONE_LEN).unwrap();
    } else {
      set_size *= u64::try_from(LAYER_TWO_LEN).unwrap();
    }
  }

  let branches = Branches::new(vec![path]).unwrap();

  let prove_start = std::time::Instant::now();
  for _ in 0 .. 10 {
    let output_blinds = random_output_blinds(G, T, U, V);

    let proof = Fcmp::prove(
      &mut OsRng,
      &params,
      root,
      blind_branches(&params, branches.clone(), vec![output_blinds]),
    );

    core::hint::black_box(proof);
  }
  println!(
    "Proving for {RUNS} {inputs}-input FCMPs with a set size of {} took an average of {}ms each",
    set_size,
    (std::time::Instant::now() - prove_start).as_millis() / u128::try_from(RUNS).unwrap()
  );
}

#[test]
fn verify_benchmark() {
  let (G, T, U, V, params) = random_params(1);

  let (path, layer_lens, root) = random_path(&params, TARGET_LAYERS);
  let output = path.output;

  let branches = Branches::new(vec![path]).unwrap();

  let output_blinds = random_output_blinds(G, T, U, V);
  let input = output_blinds.blind(&output).unwrap();

  let proof = Fcmp::prove(
    &mut OsRng,
    &params,
    root,
    blind_branches(&params, branches.clone(), vec![output_blinds]),
  );

  verify_fn(100, 1, proof.clone(), &params, root, &layer_lens, input);
  verify_fn(100, 10, proof.clone(), &params, root, &layer_lens, input);
  verify_fn(100, 100, proof.clone(), &params, root, &layer_lens, input);
}
