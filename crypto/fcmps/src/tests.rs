use rand_core::OsRng;

use generic_array::typenum::{Sum, Diff, Quot, U, U1, U2};

use multiexp::multiexp_vartime;
use ciphersuite::{group::Group, Ciphersuite, Ed25519, Selene, Helios};

use crate::*;

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

fn random_output() -> Output<<Ed25519 as Ciphersuite>::G> {
  let O = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  let I = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  let C = <Ed25519 as Ciphersuite>::G::random(&mut OsRng);
  Output::new(O, I, C).unwrap()
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
  let params = FcmpParams::<MoneroCurves>::new(
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
          <Ed25519 as Ciphersuite>::G::to_xy(output.O).unwrap().0,
          <Ed25519 as Ciphersuite>::G::to_xy(output.I).unwrap().0,
          <Ed25519 as Ciphersuite>::G::to_xy(output.C).unwrap().0,
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
      .map(|point| <Selene as Ciphersuite>::G::to_xy(point).unwrap().0)
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
      .map(|point| <Helios as Ciphersuite>::G::to_xy(point).unwrap().0)
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

  let blinded_output_start = std::time::Instant::now();
  let blinds = BlindedOutput::new(
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
    output,
  )
  .unwrap();
  dbg!((std::time::Instant::now() - blinded_output_start).as_millis());
  let input = blinds.input;

  let proof = Fcmp::prove(&mut OsRng, &params, root, output, blinds, branches.clone());

  verify_fn(100, 1, proof.clone(), &params, root, &layer_lens, input);
  verify_fn(100, 10, proof.clone(), &params, root, &layer_lens, input);
  verify_fn(100, 100, proof.clone(), &params, root, &layer_lens, input);

  let prove_start = std::time::Instant::now();
  for _ in 0 .. 10 {
    let blinds = BlindedOutput::new(
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
      output,
    )
    .unwrap();

    let proof = Fcmp::prove(&mut OsRng, &params, root, output, blinds, branches.clone());

    core::hint::black_box(proof);
  }
  dbg!((std::time::Instant::now() - prove_start).as_millis());
}
