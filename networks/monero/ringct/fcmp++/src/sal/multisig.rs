use core::{ops::Deref, fmt::Debug};
use std_shims::io;

use rand_core::{RngCore, CryptoRng, SeedableRng};
use rand_chacha::ChaCha20Rng;

use zeroize::{Zeroize, Zeroizing};

use transcript::Transcript;

use dalek_ff_group::{Scalar, EdwardsPoint};
use ciphersuite::{
  group::{
    ff::{Field, PrimeField},
    Group, GroupEncoding,
  },
  Ciphersuite, Ed25519,
};

use modular_frost::{
  curve::Curve, FrostError, Participant, ThresholdKeys, ThresholdView, algorithm::Algorithm,
};

use monero_generators::{T, FCMP_U, FCMP_V};

use crate::sal::*;

/// The Ed25519 curve/ciphersuite, yet with T as the generator.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Zeroize)]
pub struct Ed25519T;
impl Ciphersuite for Ed25519T {
  type F = Scalar;
  type G = EdwardsPoint;
  type H = blake2::Blake2b512;

  const ID: &'static [u8] = b"Ed25519 Monero T";

  fn generator() -> Self::G {
    EdwardsPoint(*T)
  }

  fn hash_to_F(dst: &[u8], data: &[u8]) -> Self::F {
    <Ed25519 as Ciphersuite>::hash_to_F(dst, data)
  }
}
impl Curve for Ed25519T {
  const CONTEXT: &'static [u8] = b"FROST-ED25519-FCMP++-v1";
}

#[derive(Clone, PartialEq, Eq, Zeroize)]
struct PartialSpendAuthAndLinkability {
  P: <Ed25519 as Ciphersuite>::G,
  A: <Ed25519 as Ciphersuite>::G,
  B: <Ed25519 as Ciphersuite>::G,
  R_O: <Ed25519 as Ciphersuite>::G,
  R_P: <Ed25519 as Ciphersuite>::G,
  R_L: <Ed25519 as Ciphersuite>::G,
  s_alpha: <Ed25519 as Ciphersuite>::F,
  s_beta: <Ed25519 as Ciphersuite>::F,
  s_delta: <Ed25519 as Ciphersuite>::F,
  s_z: <Ed25519 as Ciphersuite>::F,
  s_r_p_pre: <Ed25519 as Ciphersuite>::F,
}

impl core::fmt::Debug for PartialSpendAuthAndLinkability {
  fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
    fmt.debug_struct("PartialSpendAuthAndLinkability").finish_non_exhaustive()
  }
}

/// An algorithm to produce a SpendAuthAndLinkability with modular-frost.
///
/// This panics if the message signed for isn't empty. The entire message is expected to be
/// specified at initialization.
///
/// This may panic if functions are not called in the expected order.
///
/// The keys signed with are expected to already be offset by `r_o`/`o_blind` (the re-randomization
/// for the output key). This has undefined behavior if they're not.
#[derive(Clone)]
pub struct SalAlgorithm<
  R: Send + Sync + Clone + RngCore + CryptoRng,
  T: Sync + Clone + Debug + Transcript,
> {
  rng: R,
  transcript: T,
  signable_tx_hash: [u8; 32],
  rerandomized_output: RerandomizedOutput,
  x: Scalar,
  L: EdwardsPoint,
  partial: Option<PartialSpendAuthAndLinkability>,
  e: Option<Scalar>,
}

impl<R: Send + Sync + Clone + RngCore + CryptoRng, T: Sync + Clone + Debug + Transcript>
  core::fmt::Debug for SalAlgorithm<R, T>
{
  fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
    fmt.debug_struct("SalAlgorithm").finish_non_exhaustive()
  }
}

impl<R: Send + Sync + Clone + RngCore + CryptoRng, T: Sync + Clone + Debug + Transcript>
  Algorithm<Ed25519T> for SalAlgorithm<R, T>
{
  type Transcript = T;
  type Addendum = ();
  type Signature = SpendAuthAndLinkability;

  fn transcript(&mut self) -> &mut Self::Transcript {
    &mut self.transcript
  }

  fn nonces(&self) -> Vec<Vec<EdwardsPoint>> {
    vec![vec![EdwardsPoint(*T)]]
  }

  fn preprocess_addendum<R2: RngCore + CryptoRng>(
    &mut self,
    _: &mut R2,
    _keys: &ThresholdKeys<Ed25519T>,
  ) -> Self::Addendum {
  }

  fn read_addendum<R2: io::Read>(&self, _reader: &mut R2) -> io::Result<Self::Addendum> {
    Ok(())
  }

  fn process_addendum(
    &mut self,
    _view: &ThresholdView<Ed25519T>,
    _i: Participant,
    _addendum: Self::Addendum,
  ) -> Result<(), FrostError> {
    Ok(())
  }

  fn sign_share(
    &mut self,
    params: &ThresholdView<Ed25519T>,
    nonce_sums: &[Vec<EdwardsPoint>],
    nonces: Vec<Zeroizing<Scalar>>,
    msg: &[u8],
  ) -> Scalar {
    assert!(msg.is_empty(), "SalAlgorithm message wasn't empty");

    let G = <Ed25519 as Ciphersuite>::G::generator();
    let T_ = EdwardsPoint(*T);
    let U = EdwardsPoint(*FCMP_U);
    let V = EdwardsPoint(*FCMP_V);

    // We deterministically derive all the nonces which aren't for the `y` parameter as that's the
    // only variable considered private by this protocol
    let mut deterministic_nonces =
      ChaCha20Rng::from_seed(self.transcript.rng_seed(b"deterministic_nonces"));

    let alpha = Zeroizing::new(<Ed25519 as Ciphersuite>::F::random(&mut deterministic_nonces));
    let beta = Zeroizing::new(<Ed25519 as Ciphersuite>::F::random(&mut deterministic_nonces));
    let delta = Zeroizing::new(<Ed25519 as Ciphersuite>::F::random(&mut deterministic_nonces));
    let mu = Zeroizing::new(<Ed25519 as Ciphersuite>::F::random(&mut deterministic_nonces));
    let r_z = Zeroizing::new(<Ed25519 as Ciphersuite>::F::random(&mut deterministic_nonces));
    let r_p = Zeroizing::new(<Ed25519 as Ciphersuite>::F::random(&mut deterministic_nonces));
    let r_r_p = Zeroizing::new(<Ed25519 as Ciphersuite>::F::random(&mut deterministic_nonces));

    let x_r_i = Zeroizing::new(self.x * self.rerandomized_output.r_i);

    let P = (G * self.x) + (V * self.rerandomized_output.r_i) + (U * *x_r_i) + (T_ * *r_p);

    let alpha_G = G * *alpha;

    let A = alpha_G +
      (V * *beta) +
      (U * ((*alpha * self.rerandomized_output.r_i) + (*beta * self.x))) +
      (T_ * *delta);
    let B = (U * (*alpha * *beta)) + (T_ * *mu);

    let R_L = (self.rerandomized_output.input().I_tilde * *alpha) - (U * *r_z);

    /*
      We have to sign:

        - `s_y = r_y + (e * y)`
        - `s_r_p = r_r_p + (e * (r_p - y - r_r_i))

      We use the nonce we generated as `r_y`, with `y` as our secret represented by our
      ThresholdKeys. We then observe the following:

        - `-s_y == -r_y + (e * -y)`
        - `-s_y + (e * r_p) + (e * -r_r_i) == -r_y + (e * -y) + (e * r_p) + (e * -r_r_i)`
        - `-s_y + (e * (r_p - r_r_i)) == -r_y + (e * (r_p - y - r_r_i))`

      We can set `r_r_p` to `-r_y`, then `s_r_p = s_y + (e * r_p)`. Since `s_y` is ZK to `y`, any
      permutations off of it (which don't re-introduce `y`) must also be ZK to `y`. While
      `r_r_p = -r_y` would be nonce reuse (albeit with a different secret), we don't actually reuse
      `r_y`. We solely specify our commitment to `r_r_p` to be the additive inverse of our
      commitment to `r_y`, which is satisfactory for our purposes here. Reusing commitments isn't
      an issue as the commitments are to uniformly sampled scalars in a group where the
      discrete-log problem is assumed hard.

      It would be publicly observable that `r_r_p = -r_y`, so we further tweak the supposed
      commitment to `r_r_p` (the additive inverse of the commitment of `r_y`) by a
      deterministically derived offset we label `r_r_p` here. This resolves as:

        - `R_y = r_y T`
        - `R_r_p = -(r_y T) + (r_r_p T)`
        - `s_y = r_y + (e * y)`
        - `s_r_p = -s_y + r_r_p + (e * (r_p - r_r_i))`

      Please note `R_y`/`R_r_p` do not actually exist and are terms in `R_O`/`R_P` (respectively).
    */

    let R_y = nonce_sums[0][0];
    let R_r_p = -R_y + (T_ * *r_r_p);

    let R_O = alpha_G + R_y;
    let R_P = (U * *r_z) + R_r_p;

    let e = SpendAuthAndLinkability::challenge(
      self.signable_tx_hash,
      &self.rerandomized_output.input,
      self.L,
      P,
      A,
      B,
      R_O,
      R_P,
      R_L,
    );

    let s_alpha = *alpha + (e * self.x);
    let s_beta = *beta + (e * self.rerandomized_output.r_i);
    let s_delta = *mu + (e * *delta) + (*r_p * e.square());
    // z is x_r_i
    let s_z = *r_z + (e * *x_r_i);

    self.partial = Some(PartialSpendAuthAndLinkability {
      P,
      A,
      B,
      R_O,
      R_P,
      R_L,
      s_alpha,
      s_beta,
      s_delta,
      s_z,
      s_r_p_pre: *r_r_p + (e * (*r_p - self.rerandomized_output.r_r_i)),
    });
    self.e = Some(e);

    // Yield the share of s_y
    (e * params.secret_share().deref()) + nonces[0].deref()
  }

  fn verify(
    &self,
    _group_key: EdwardsPoint,
    _nonces: &[Vec<EdwardsPoint>],
    sum: Scalar,
  ) -> Option<Self::Signature> {
    let PartialSpendAuthAndLinkability {
      P,
      A,
      B,
      R_O,
      R_P,
      R_L,
      s_alpha,
      s_beta,
      s_delta,
      s_z,
      s_r_p_pre,
    } = self.partial.clone().unwrap();
    let s_y = sum;
    let s_r_p = s_r_p_pre - s_y;
    let sig =
      SpendAuthAndLinkability { P, A, B, R_O, R_P, R_L, s_alpha, s_beta, s_delta, s_z, s_y, s_r_p };

    let mut verifier = multiexp::BatchVerifier::new(4);
    // Use the internal RNG for this
    sig.verify(
      &mut self.rng.clone(),
      &mut verifier,
      self.signable_tx_hash,
      &self.rerandomized_output.input,
      self.L,
    );
    if verifier.verify_vartime() {
      return Some(sig);
    }
    None
  }

  fn verify_share(
    &self,
    verification_share: EdwardsPoint,
    nonces: &[Vec<EdwardsPoint>],
    share: Scalar,
  ) -> Result<Vec<(Scalar, EdwardsPoint)>, ()> {
    Ok(vec![
      (Scalar::ONE, nonces[0][0]),
      (self.e.unwrap(), verification_share),
      (-share, EdwardsPoint(*T)),
    ])
  }
}

impl<R: Send + Sync + Clone + RngCore + CryptoRng, T: Sync + Clone + Debug + Transcript>
  SalAlgorithm<R, T>
{
  /// Sign a SpendAuthAndLinkability proof using modular-frost.
  pub fn new(
    rng: R,
    mut transcript: T,
    signable_tx_hash: [u8; 32],
    rerandomized_output: RerandomizedOutput,
    x: Scalar,
  ) -> Self {
    transcript.domain_separate(b"SpendAuthAndLinkability Multisig");

    transcript.append_message(b"signable_tx_hash", signable_tx_hash);

    transcript.append_message(b"O_tilde", rerandomized_output.input.O_tilde.to_bytes());
    transcript.append_message(b"I_tilde", rerandomized_output.input.I_tilde.to_bytes());
    transcript.append_message(b"R", rerandomized_output.input.R.to_bytes());
    transcript.append_message(b"C_tilde", rerandomized_output.input.C_tilde.to_bytes());

    transcript.append_message(b"r_o", rerandomized_output.r_o.to_repr());
    transcript.append_message(b"r_i", rerandomized_output.r_i.to_repr());
    transcript.append_message(b"r_r_i", rerandomized_output.r_r_i.to_repr());
    transcript.append_message(b"r_c", rerandomized_output.r_c.to_repr());

    transcript.append_message(b"x", x.to_repr());

    let L =
      (rerandomized_output.input.I_tilde - (EdwardsPoint(*FCMP_U) * rerandomized_output.r_i)) * x;

    Self { rng, transcript, signable_tx_hash, rerandomized_output, x, L, partial: None, e: None }
  }
}
