use core::{ops::Deref, fmt::Debug};
use std::{io, collections::HashMap};

use rand_core::{RngCore, CryptoRng};

use zeroize::{Zeroize, Zeroizing};

use transcript::Transcript;

use ciphersuite::{
  group::{
    ff::{Field, PrimeField},
    Group, GroupEncoding,
  },
  Ciphersuite,
};

use frost::{
  dkg::lagrange,
  curve::Curve,
  FrostError, Participant, ThresholdKeys, ThresholdView,
  algorithm::{WriteAddendum, Algorithm},
};

use crate::GeneralizedSchnorr;

// The column of generators for the multi-party shared scalar scaled by the local share.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct OutputShare<C: Ciphersuite, const OUTPUTS: usize>([C::G; OUTPUTS]);
impl<C: Ciphersuite, const OUTPUTS: usize> WriteAddendum for OutputShare<C, OUTPUTS> {
  fn write<W: io::Write>(&self, writer: &mut W) -> io::Result<()> {
    for point in &self.0 {
      writer.write_all(point.to_bytes().as_ref())?;
    }
    Ok(())
  }
}

/// An algorithm to produce a GeneralizedSchnorr with modular-frost.
#[derive(Clone, PartialEq, Debug)]
pub struct GeneralizedSchnorrAlgorithm<
  C: Curve,
  T: Sync + Clone + PartialEq + Debug + Transcript,
  const OUTPUTS: usize,
  const SCALARS: usize,
  const SCALARS_PLUS_TWO: usize,
> {
  mpc_transcript: T,
  proof_transcript: T,
  matrix: [[C::G; SCALARS]; OUTPUTS],
  scalars: [Option<Zeroizing<C::F>>; SCALARS],
  output_shares: HashMap<Vec<u8>, [C::G; OUTPUTS]>,
  outputs: Option<[C::G; OUTPUTS]>,
  R: Option<[C::G; OUTPUTS]>,
  c: Option<C::F>,
  s: Option<[C::F; SCALARS]>,
}
impl<
    C: Curve,
    T: Sync + Clone + PartialEq + Debug + Transcript,
    const OUTPUTS: usize,
    const SCALARS: usize,
    const SCALARS_PLUS_TWO: usize,
  > Algorithm<C> for GeneralizedSchnorrAlgorithm<C, T, OUTPUTS, SCALARS, SCALARS_PLUS_TWO>
{
  type Transcript = T;
  type Addendum = OutputShare<C, OUTPUTS>;
  type Signature = ([C::G; OUTPUTS], T, GeneralizedSchnorr<C, OUTPUTS, SCALARS, SCALARS_PLUS_TWO>);

  fn transcript(&mut self) -> &mut Self::Transcript {
    &mut self.mpc_transcript
  }

  fn nonces(&self) -> Vec<Vec<C::G>> {
    let i = self
      .scalars
      .iter()
      .position(Option::is_none)
      .expect("constructed algorithm doesn't have a multi-party scalar");
    // One nonce, with representations for each generator in this column
    vec![self.matrix.iter().map(|row| row[i]).collect()]
  }

  fn preprocess_addendum<R: RngCore + CryptoRng>(
    &mut self,
    _: &mut R,
    keys: &ThresholdKeys<C>,
  ) -> Self::Addendum {
    let j = self
      .scalars
      .iter()
      .position(Option::is_none)
      .expect("constructed algorithm doesn't have a multi-party scalar");
    OutputShare(core::array::from_fn(|i| self.matrix[i][j] * keys.secret_share().deref()))
  }

  fn read_addendum<R: io::Read>(&self, reader: &mut R) -> io::Result<Self::Addendum> {
    let mut outputs = [C::G::identity(); OUTPUTS];
    for output in &mut outputs {
      *output = <C as Curve>::read_G(reader)?;
    }
    Ok(OutputShare(outputs))
  }

  fn process_addendum(
    &mut self,
    view: &ThresholdView<C>,
    i: Participant,
    addendum: Self::Addendum,
  ) -> Result<(), FrostError> {
    if self.outputs.is_none() {
      self.mpc_transcript.domain_separate(b"generalized_schnorr-mpc-addendum");
      self.outputs = Some(core::array::from_fn(|i| {
        let mut sum = C::G::identity();
        for j in 0 .. SCALARS {
          sum += self.matrix[i][j] *
            self.scalars[j].as_ref().unwrap_or(&Zeroizing::new(C::F::ZERO)).deref();
        }
        sum
      }));
    }

    self.mpc_transcript.append_message(b"participant", i.to_bytes());
    let outputs = self.outputs.as_mut().unwrap();
    for (output, share) in outputs.iter_mut().zip(addendum.0.iter()) {
      self.mpc_transcript.append_message(b"output_share", share.to_bytes());
      *output += *share * lagrange::<C::F>(i, view.included());
    }
    self.output_shares.insert(view.verification_share(i).to_bytes().as_ref().to_vec(), addendum.0);
    Ok(())
  }

  fn sign_share(
    &mut self,
    params: &ThresholdView<C>,
    nonce_sums: &[Vec<C::G>],
    nonces: Vec<Zeroizing<C::F>>,
    msg: &[u8],
  ) -> C::F {
    assert!(msg.is_empty(), "msg wasn't empty when the 'msg' is passed on construction");

    let mut R: [C::G; OUTPUTS] = nonce_sums[0]
      .clone()
      .try_into()
      .expect("didn't generate as many representations of the nonce as outputs");

    // Deterministically derive nonces for the rest of the scalars
    let mut deterministic_nonces: [C::F; SCALARS] = core::array::from_fn(|_| {
      <C as Ciphersuite>::hash_to_F(
        b"generalized_schnorr-mpc-nonce",
        self.mpc_transcript.challenge(b"nonce").as_ref(),
      )
    });

    let mpc_scalar_index = self
      .scalars
      .iter()
      .position(Option::is_none)
      .expect("constructed algorithm doesn't have a multi-party scalar");
    // Don't add any nonce for what we actually generated a nonce for
    deterministic_nonces[mpc_scalar_index] = C::F::ZERO;

    for (i, R) in R.iter_mut().enumerate() {
      for (j, nonce) in deterministic_nonces.iter().enumerate() {
        *R += self.matrix[i][j] * nonce;
      }
    }
    self.R = Some(R);

    let c = GeneralizedSchnorr::<C, OUTPUTS, SCALARS, SCALARS_PLUS_TWO>::challenge(
      &mut self.proof_transcript.clone(),
      self.matrix,
      self.outputs.expect("didn't process any addendums"),
      R,
    );
    self.c = Some(c);
    self.mpc_transcript.append_message(b"c", c.to_repr());

    let mut s = [C::F::ZERO; SCALARS];
    for ((s, nonce), scalar) in
      s.iter_mut().zip(deterministic_nonces.iter()).zip(self.scalars.iter())
    {
      if let Some(scalar) = scalar {
        *s = (c * scalar.deref()) + nonce;
      } else {
        assert_eq!(*nonce, C::F::ZERO);
      }
    }
    deterministic_nonces.zeroize();
    self.s = Some(s);

    (c * params.secret_share().deref()) + nonces[0].deref()
  }

  #[must_use]
  fn verify(&self, _group_key: C::G, _nonces: &[Vec<C::G>], sum: C::F) -> Option<Self::Signature> {
    // We drop the nonces argument as we've already incorporated them into R
    let R = self.R.unwrap();
    let mpc_scalar_index = self
      .scalars
      .iter()
      .position(Option::is_none)
      .expect("constructed algorithm doesn't have a multi-party scalar");
    let mut s = self.s.unwrap();
    s[mpc_scalar_index] = sum;

    let outputs = self.outputs.unwrap();
    let sig = GeneralizedSchnorr { R, s };
    let mut transcript = self.proof_transcript.clone();
    if sig.verify(&mut transcript, self.matrix, outputs) {
      return Some((outputs, transcript, sig));
    }
    None
  }

  fn verify_share(
    &self,
    verification_share: C::G,
    nonces: &[Vec<C::G>],
    share: C::F,
  ) -> Result<Vec<(C::F, C::G)>, ()> {
    let mpc_scalar_index = self
      .scalars
      .iter()
      .position(Option::is_none)
      .expect("constructed algorithm doesn't have a multi-party scalar");

    let c = self.c.unwrap();
    let outputs = self.output_shares[&verification_share.to_bytes().as_ref().to_vec()];

    // Since we need to append multiple statements, we need a random weight
    // Use the MPC transcript, which should be binding to all context and valid as a deterministic
    // weight
    // The one item it hasn't bound is the scalar share, so bind that
    let mut transcript = self.mpc_transcript.clone();
    transcript.append_message(b"share", share.to_repr());

    let mut statements = vec![];
    for ((row, nonce), output) in self.matrix.iter().zip(nonces[0].iter()).zip(outputs.iter()) {
      let weight = <C as Ciphersuite>::hash_to_F(
        b"generalized_schnorr-mpc-verify_share",
        transcript.challenge(b"verify_share").as_ref(),
      );
      statements.extend(&[
        (weight, *nonce),
        (weight * c, *output),
        (weight * -share, row[mpc_scalar_index]),
      ]);
    }
    Ok(statements)
  }
}

impl<C: Curve, const OUTPUTS: usize, const SCALARS: usize, const SCALARS_PLUS_TWO: usize>
  GeneralizedSchnorr<C, OUTPUTS, SCALARS, SCALARS_PLUS_TWO>
{
  /// Prove a Generalized Schnorr statement via MPC.
  ///
  /// Creates a machine which returns the outputs, the proof, and the mutated proof transcript.
  ///
  /// Only one scalar in the witness is allowed to be shared among the RPC participants. The rest
  /// must be known to all parties. The nonces blinding these known-by-all scalars will be
  /// deterministically derived from the transcript. While this enables recovery of those values by
  /// anyone with the transcript, that's presumed to solely be the participants (who already have
  /// knowledge of the scalars). Please encrypt the transcript at the communication layer if you
  /// need it to be private.
  ///
  /// Returns None if there isn't exactly one scalar in the witness is missing.
  pub fn multiparty_prove<T: Sync + Clone + PartialEq + Debug + Transcript>(
    mpc_transcript: T,
    proof_transcript: T,
    matrix: [[C::G; SCALARS]; OUTPUTS],
    scalars: [Option<Zeroizing<C::F>>; SCALARS],
  ) -> Option<GeneralizedSchnorrAlgorithm<C, T, OUTPUTS, SCALARS, SCALARS_PLUS_TWO>> {
    if scalars.iter().filter(|scalar| scalar.is_none()).count() != 1 {
      None?;
    }

    Some(GeneralizedSchnorrAlgorithm {
      mpc_transcript,
      proof_transcript,
      matrix,
      scalars,
      output_shares: HashMap::new(),
      outputs: None,
      R: None,
      c: None,
      s: None,
    })
  }
}
