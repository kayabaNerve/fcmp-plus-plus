#![allow(non_snake_case)]

use rand_core::{RngCore, CryptoRng};
use zeroize::{Zeroize, ZeroizeOnDrop, Zeroizing};

use generic_array::typenum::{Sum, Diff, Quot, U, U1, U2};

use transcript::{Transcript, RecommendedTranscript};

use dalek_ff_group::EdwardsPoint;
use ciphersuite::{
  group::{
    ff::{Field, PrimeField},
    Group, GroupEncoding,
  },
  Ciphersuite, Ed25519, Helios, Selene,
};

use generalized_schnorr::GeneralizedSchnorr;
use generalized_bulletproofs_ec_gadgets::*;
use fcmps::*;

use monero_generators::{H, T, FCMP_U, FCMP_V, hash_to_point};

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Ed25519Params;
impl DiscreteLogParameters for Ed25519Params {
  type ScalarBits = U<{ <<Ed25519 as Ciphersuite>::F as PrimeField>::NUM_BITS as usize }>;
  type XCoefficients = Quot<Sum<Self::ScalarBits, U1>, U2>;
  type XCoefficientsMinusOne = Diff<Self::XCoefficients, U1>;
  type YxCoefficients = Diff<Quot<Sum<Self::ScalarBits, U1>, U2>, U2>;
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SeleneParams;
impl DiscreteLogParameters for SeleneParams {
  type ScalarBits = U<{ <<Selene as Ciphersuite>::F as PrimeField>::NUM_BITS as usize }>;
  type XCoefficients = Quot<Sum<Self::ScalarBits, U1>, U2>;
  type XCoefficientsMinusOne = Diff<Self::XCoefficients, U1>;
  type YxCoefficients = Diff<Quot<Sum<Self::ScalarBits, U1>, U2>, U2>;
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct HeliosParams;
impl DiscreteLogParameters for HeliosParams {
  type ScalarBits = U<{ <<Helios as Ciphersuite>::F as PrimeField>::NUM_BITS as usize }>;
  type XCoefficients = Quot<Sum<Self::ScalarBits, U1>, U2>;
  type XCoefficientsMinusOne = Diff<Self::XCoefficients, U1>;
  type YxCoefficients = Diff<Quot<Sum<Self::ScalarBits, U1>, U2>, U2>;
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Curves;
impl FcmpCurves for Curves {
  type OC = Ed25519;
  type OcParameters = Ed25519Params;
  type C1 = Selene;
  type C1Parameters = SeleneParams;
  type C2 = Helios;
  type C2Parameters = HeliosParams;
}

#[derive(Clone, PartialEq, Eq, Zeroize)]
pub struct Output {
  O: <Ed25519 as Ciphersuite>::G,
  I: <Ed25519 as Ciphersuite>::G,
  C: <Ed25519 as Ciphersuite>::G,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Zeroize)]
pub struct Input {
  O_tilde: <Ed25519 as Ciphersuite>::G,
  I_tilde: <Ed25519 as Ciphersuite>::G,
  C_tilde: <Ed25519 as Ciphersuite>::G,
  R: <Ed25519 as Ciphersuite>::G,
}

impl Input {
  pub fn transcript(&self, transcript: &mut impl Transcript, L: <Ed25519 as Ciphersuite>::G) {
    transcript.append_message(b"L", L.to_bytes());
    transcript.append_message(b"O_tilde", self.O_tilde.to_bytes());
    transcript.append_message(b"I_tilde", self.I_tilde.to_bytes());
    transcript.append_message(b"C_tilde", self.C_tilde.to_bytes());
    transcript.append_message(b"R", self.R.to_bytes());
  }
}

impl Output {
  pub fn from_ring(O: <Ed25519 as Ciphersuite>::G, amount: u64) -> Output {
    let C = EdwardsPoint(H()) * <Ed25519 as Ciphersuite>::F::from(amount);
    Self::from_ringct(O, C)
  }
  pub fn from_ringct(O: <Ed25519 as Ciphersuite>::G, C: <Ed25519 as Ciphersuite>::G) -> Output {
    Output { O, I: EdwardsPoint(hash_to_point(O.compress().0)), C }
  }
}

#[derive(Clone, PartialEq, Eq, Zeroize, ZeroizeOnDrop)]
pub struct RerandomizedOutput {
  input: Input,
  r_o: <Ed25519 as Ciphersuite>::F,
  r_i: <Ed25519 as Ciphersuite>::F,
  r_j: <Ed25519 as Ciphersuite>::F,
  r_c: <Ed25519 as Ciphersuite>::F,
}

impl RerandomizedOutput {
  pub fn new(rng: &mut (impl RngCore + CryptoRng), output: Output) -> RerandomizedOutput {
    let r_o = <Ed25519 as Ciphersuite>::F::random(&mut *rng);
    let r_i = <Ed25519 as Ciphersuite>::F::random(&mut *rng);
    let r_j = <Ed25519 as Ciphersuite>::F::random(&mut *rng);
    let r_c = <Ed25519 as Ciphersuite>::F::random(&mut *rng);

    let O_tilde = output.O + (EdwardsPoint(T()) * r_o);
    let I_tilde = output.I + (EdwardsPoint(FCMP_U()) * r_i);
    let R = (EdwardsPoint(FCMP_V()) * r_i) + (EdwardsPoint(T()) * r_j);
    let C_tilde = output.C + (<Ed25519 as Ciphersuite>::generator() * r_c);

    RerandomizedOutput { input: Input { O_tilde, I_tilde, R, C_tilde }, r_o, r_i, r_j, r_c }
  }

  pub fn input(&self) -> Input {
    self.input
  }
}

/// The opening for the O, I, R of an Input tuple.
///
/// This does not open C as it's unnecessary for the purposes of this proof.
#[derive(Clone, PartialEq, Eq, Zeroize, ZeroizeOnDrop)]
pub struct OpenedInputTuple {
  input: Input,
  // O~ = xG + yT
  x: <Ed25519 as Ciphersuite>::F,
  y: <Ed25519 as Ciphersuite>::F,
  // R = r_i V + r_j T
  r_i: <Ed25519 as Ciphersuite>::F,
  r_j: <Ed25519 as Ciphersuite>::F,
}

impl OpenedInputTuple {
  /// x and y are for the x and y variables in O = xG + yT.
  pub fn open(
    rerandomized_output: RerandomizedOutput,
    x: &<Ed25519 as Ciphersuite>::F,
    y: &<Ed25519 as Ciphersuite>::F,
  ) -> Option<OpenedInputTuple> {
    // Verify the opening is consistent.
    let mut y_tilde = rerandomized_output.r_o + y;
    if (<Ed25519 as Ciphersuite>::generator() * x) + (EdwardsPoint(T()) * y_tilde) !=
      rerandomized_output.input.O_tilde
    {
      y_tilde.zeroize();
      None?;
    }
    Some(OpenedInputTuple {
      input: rerandomized_output.input,
      x: *x,
      y: y_tilde,
      r_i: rerandomized_output.r_i,
      r_j: rerandomized_output.r_j,
    })
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Zeroize)]
pub struct BpPlus {
  A: <Ed25519 as Ciphersuite>::G,
  B: <Ed25519 as Ciphersuite>::G,
  s_alpha: <Ed25519 as Ciphersuite>::F,
  s_beta: <Ed25519 as Ciphersuite>::F,
  s_delta: <Ed25519 as Ciphersuite>::F,
}

#[derive(Clone, PartialEq, Eq, Debug, Zeroize)]
pub struct SpendAuthAndLinkability {
  P: <Ed25519 as Ciphersuite>::G,
  bp_plus: BpPlus,
  gsp: GeneralizedSchnorr<Ed25519, 3, 4, 6>,
}

impl SpendAuthAndLinkability {
  pub fn prove(
    rng: &mut (impl RngCore + CryptoRng),
    signable_tx_hash: [u8; 32],
    opening: OpenedInputTuple,
  ) -> (<Ed25519 as Ciphersuite>::G, SpendAuthAndLinkability) {
    let G = <Ed25519 as Ciphersuite>::G::generator();
    let T = EdwardsPoint(T());
    let U = EdwardsPoint(FCMP_U());
    let V = EdwardsPoint(FCMP_V());

    let L = (opening.input.I_tilde * opening.x) - (U * opening.r_i);

    let mut transcript = RecommendedTranscript::new(b"FCMP++ SA+L");
    transcript.domain_separate(b"monero");
    transcript.append_message(b"tx_hash", signable_tx_hash);
    opening.input.transcript(&mut transcript, L);

    let r_p = Zeroizing::new(<Ed25519 as Ciphersuite>::F::random(&mut *rng));
    let alpha = Zeroizing::new(<Ed25519 as Ciphersuite>::F::random(&mut *rng));
    let beta = Zeroizing::new(<Ed25519 as Ciphersuite>::F::random(&mut *rng));
    let mu = Zeroizing::new(<Ed25519 as Ciphersuite>::F::random(&mut *rng));
    let delta = Zeroizing::new(<Ed25519 as Ciphersuite>::F::random(&mut *rng));

    let x_r_i = Zeroizing::new(opening.x * opening.r_i);
    let P = (G * opening.x) + (V * opening.r_i) + (U * *x_r_i) + (T * *r_p);

    let A = (G * *alpha) +
      (V * *beta) +
      (U * ((*alpha * opening.r_i) + (*beta * opening.x))) +
      (T * *delta);
    let B = (U * (*alpha * *beta)) + (T * *mu);

    transcript.domain_separate(b"bp+");
    transcript.append_message(b"P", P.to_bytes());
    transcript.append_message(b"A", A.to_bytes());
    transcript.append_message(b"B", B.to_bytes());

    let e = <Ed25519 as Ciphersuite>::hash_to_F(b"FCMP++ SA+L BP+", &transcript.challenge(b"e"));

    let s_alpha = *alpha + (e * opening.x);
    let s_beta = *beta + (e * opening.r_i);
    let s_delta = *mu + (e * *delta) + (*r_p * e.square());

    let P_ = P - opening.input.O_tilde - opening.input.R;

    let identity = <Ed25519 as Ciphersuite>::G::identity();
    #[rustfmt::skip]
    // x,                     y,         x * r_i,  r_p - y' - r_j
    let matrix = [
      [G,                     T,         identity, identity], // = O~ = xG + yT
      [identity,              identity,  U,        T],        // = P_ = x r_i U + (r_p - y' - r_j) T
      [opening.input.I_tilde, identity, -U,        identity], // = L = x I~ - x r_i U
    ];
    let x = Zeroizing::new(opening.x);
    let y = Zeroizing::new(opening.y);
    let P__randomness = Zeroizing::new(*r_p - opening.y - opening.r_j);
    // This transcript the generator matrix, the outputs, and its nonces
    // The matrix/output transcripting is partially redundant
    let ([O_tilde_calc, P__calc, L_calc], gsp) =
      GeneralizedSchnorr::prove(rng, &mut transcript, matrix, [&x, &y, &x_r_i, &P__randomness]);
    debug_assert_eq!(opening.input.O_tilde, O_tilde_calc);
    debug_assert_eq!(P_, P__calc);
    debug_assert_eq!(L, L_calc);

    (L, SpendAuthAndLinkability { P, bp_plus: BpPlus { A, B, s_alpha, s_beta, s_delta }, gsp })
  }

  #[allow(unused)]
  pub fn verify(
    self,
    rng: &mut (impl RngCore + CryptoRng),
    verifier: &mut multiexp::BatchVerifier<(), <Ed25519 as Ciphersuite>::G>,
    signable_tx_hash: [u8; 32],
    input: &Input,
    key_image: <Ed25519 as Ciphersuite>::G,
  ) {
    todo!("TODO")
  }
}

#[derive(Clone, Debug, Zeroize)]
pub struct FcmpPlusPlus {
  input: Input,
  fcmp: Fcmp<Curves>,
  spend_auth_and_linkability: SpendAuthAndLinkability,
}

impl FcmpPlusPlus {
  pub fn new(
    input: Input,
    fcmp: Fcmp<Curves>,
    spend_auth_and_linkability: SpendAuthAndLinkability,
  ) -> FcmpPlusPlus {
    FcmpPlusPlus { input, fcmp, spend_auth_and_linkability }
  }

  #[allow(clippy::too_many_arguments)]
  pub fn verify(
    self,
    rng: &mut (impl RngCore + CryptoRng),
    verifier_ed: &mut multiexp::BatchVerifier<(), <Ed25519 as Ciphersuite>::G>,
    verifier_1: &mut generalized_bulletproofs::BatchVerifier<Selene>,
    verifier_2: &mut generalized_bulletproofs::BatchVerifier<Helios>,
    params: &FcmpParams<Curves>,
    tree: TreeRoot<<Curves as FcmpCurves>::C1, <Curves as FcmpCurves>::C2>,
    layer_lens: &[usize],
    signable_tx_hash: [u8; 32],
    key_image: <Ed25519 as Ciphersuite>::G,
  ) {
    self.spend_auth_and_linkability.verify(
      rng,
      verifier_ed,
      signable_tx_hash,
      &self.input,
      key_image,
    );

    // TODO: Return false, don't panic
    let fcmp_input =
      fcmps::Input::new(self.input.O_tilde, self.input.I_tilde, self.input.R, self.input.C_tilde)
        .unwrap();
    self.fcmp.verify(rng, verifier_1, verifier_2, params, tree, layer_lens, fcmp_input);
  }
}
