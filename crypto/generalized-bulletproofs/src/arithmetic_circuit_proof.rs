use rand_core::{RngCore, CryptoRng};

use zeroize::{Zeroize, ZeroizeOnDrop};

use multiexp::{multiexp, multiexp_vartime};
use ciphersuite::{group::ff::Field, Ciphersuite};

use crate::{
  ScalarVector, ScalarMatrix, PointVector, ProofGenerators, PedersenCommitment,
  PedersenVectorCommitment, BatchVerifier,
  transcript::*,
  inner_product::{IpError, IpStatement, IpWitness, P},
};

/// Bulletproofs' Arithmetic Circuit Statement from 5.1, modified per Generalized Bulletproofs.
///
/// Bulletproofs' `aL * aR = aO, WL * aL + WR * aR + WO * aO = WV * V + c`
/// is modified to
/// Generalized Bulletproofs'
/// `aL * aR = aO, WL * aL + WR * aR + WO * aO + WCL * C_L + WCR * C_R = WV * V + c`.
#[derive(Clone, Debug)]
pub struct ArithmeticCircuitStatement<'a, C: Ciphersuite> {
  generators: ProofGenerators<'a, C>,

  /// The WL matrix from the above statement.
  WL: ScalarMatrix<C>,
  /// The WR matrix from the above statement.
  WR: ScalarMatrix<C>,
  /// The WO matrix from the above statement.
  WO: ScalarMatrix<C>,
  /// The WV matrix from the above statement.
  WV: ScalarMatrix<C>,
  /// The WCL matrix from the above statement.
  WCL: Vec<ScalarMatrix<C>>,
  /// The WCR matrix from the above statement.
  WCR: Vec<ScalarMatrix<C>>,
  /// The c vector from the above statement.
  c: ScalarVector<C::F>,

  /// The vector commitments.
  C: PointVector<C>,
  /// The non-vector commitments.
  V: PointVector<C>,
}

impl<'a, C: Ciphersuite> Zeroize for ArithmeticCircuitStatement<'a, C> {
  fn zeroize(&mut self) {
    self.WL.zeroize();
    self.WR.zeroize();
    self.WO.zeroize();
    self.WCL.zeroize();
    self.WCR.zeroize();
    self.WV.zeroize();
    self.c.zeroize();

    self.C.zeroize();
    self.V.zeroize();
  }
}

/// The witness for an arithmetic circuit statement.
#[derive(Clone, Debug, Zeroize, ZeroizeOnDrop)]
pub struct ArithmeticCircuitWitness<C: Ciphersuite> {
  aL: ScalarVector<C::F>,
  aR: ScalarVector<C::F>,
  aO: ScalarVector<C::F>,

  c: Vec<PedersenVectorCommitment<C>>,
  v: Vec<PedersenCommitment<C>>,
}

/// An error incurred during arithmetic circuit proof operations.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AcError {
  /// The vectors of scalars which are multiplied against each other were of different lengths.
  DifferingLrLengths,
  /// The matrices of constraints are of different lengths.
  InconsistentAmountOfConstraints,
  /// A constraint referred to a non-existent term.
  ConstrainedNonExistentTerm,
  /// A constraint referred to a non-existent commitment.
  ConstrainedNonExistentCommitment,
  /// There weren't enough generators to prove for this statement.
  NotEnoughGenerators,
  /// The witness was inconsistent to the statement.
  ///
  /// Sanity checks on the witness are always performed. If the library is compiled with debug
  /// assertions on, the satisfaction of all constraints and validity of the commitmentsd is
  /// additionally checked.
  InconsistentWitness,
  /// There was an error from the inner-product proof.
  Ip(IpError),
  /// The proof wasn't complete and the necessary values could not be read from the transcript.
  IncompleteProof,
}

impl<C: Ciphersuite> ArithmeticCircuitWitness<C> {
  /// Constructs a new witness instance.
  pub fn new(
    aL: ScalarVector<C::F>,
    aR: ScalarVector<C::F>,
    c: Vec<PedersenVectorCommitment<C>>,
    v: Vec<PedersenCommitment<C>>,
  ) -> Result<Self, AcError> {
    if aL.len() != aR.len() {
      Err(AcError::DifferingLrLengths)?;
    }

    // The Pedersen Vector Commitments don't have their variables' lengths checked as they aren't
    // paired off with each other as aL, aR are

    // The PVC commit function ensures there's enough generators for their amount of terms
    // If there aren't enough/the same generators when this is proven for, it'll trigger
    // InconsistentWitness

    let aO = aL.clone() * &aR;
    Ok(ArithmeticCircuitWitness { aL, aR, aO, c, v })
  }
}

struct YzChallenges<C: Ciphersuite> {
  y_inv: ScalarVector<C::F>,
  z: ScalarVector<C::F>,
}

impl<'a, C: Ciphersuite> ArithmeticCircuitStatement<'a, C> {
  // The amount of multiplications performed.
  fn n(&self) -> usize {
    self.generators.len()
  }

  // The amount of constraints.
  fn q(&self) -> usize {
    self.WL.len()
  }

  // The amount of Pedersen Vector Commitments.
  fn c(&self) -> usize {
    self.C.len()
  }

  // The amount of Pedersen Commitments.
  fn m(&self) -> usize {
    self.V.len()
  }

  /// Create a new ArithmeticCircuitStatement for the specified relationship.
  ///
  /// The weights and c vector are not transcripted. They're expected to be deterministic from the
  /// context and higher-level statement. If your constraints are variable, you MUST transcript
  /// them before calling prove/verify.
  ///
  /// The commitments are expected to have been transcripted extenally to this statement's
  /// invocation. That's practically ensured by taking a `Commitments` struct here, which is only
  /// obtainable via a transcript.
  #[allow(clippy::too_many_arguments)]
  pub fn new(
    generators: ProofGenerators<'a, C>,
    WL: ScalarMatrix<C>,
    WR: ScalarMatrix<C>,
    WO: ScalarMatrix<C>,
    WCL: Vec<ScalarMatrix<C>>,
    WCR: Vec<ScalarMatrix<C>>,
    WV: ScalarMatrix<C>,
    c: ScalarVector<C::F>,
    commitments: Commitments<C>,
  ) -> Result<Self, AcError> {
    let Commitments { C, V } = commitments;

    // n is the amount of multiplications
    let n = generators.len();

    // m is the amount of Pedersen Commitments
    let m = V.len();

    // q is the amount of constraints
    let q = WL.len();
    if (WR.len() != q) || (WO.len() != q) || (WV.len() != q) || (c.len() != q) {
      Err(AcError::InconsistentAmountOfConstraints)?;
    }
    for WCL in &WCL {
      if WCL.len() != q {
        Err(AcError::InconsistentAmountOfConstraints)?;
      }
    }
    for WCR in &WCR {
      if WCR.len() != q {
        Err(AcError::InconsistentAmountOfConstraints)?;
      }
    }

    // Check if the highest index exceeds n, meaning this matrix has a faulty constraint
    if WL.highest_index.max(WR.highest_index).max(WO.highest_index) >= n {
      Err(AcError::ConstrainedNonExistentTerm)?;
    }

    if WCL.len() != C.len() {
      Err(AcError::ConstrainedNonExistentCommitment)?;
    }
    if WCR.len() != C.len() {
      Err(AcError::ConstrainedNonExistentCommitment)?;
    }
    for WCL in &WCL {
      // The Pedersen Vector Commitments internally have as many terms as we have multiplications
      if WCL.highest_index > n {
        Err(AcError::ConstrainedNonExistentTerm)?;
      }
    }
    for WCR in &WCR {
      // The Pedersen Vector Commitments internally have as many terms as we have multiplications
      if WCR.highest_index > n {
        Err(AcError::ConstrainedNonExistentTerm)?;
      }
    }

    if WV.highest_index > m {
      Err(AcError::ConstrainedNonExistentCommitment)?;
    }

    Ok(Self { generators, WL, WR, WO, WCL, WCR, WV, c, C, V })
  }

  fn yz_challenges(&self, y: C::F, z_1: C::F) -> YzChallenges<C> {
    let y_inv = y.invert().unwrap();
    let y_inv = ScalarVector::powers(y_inv, self.n());

    // Powers of z *starting with z**1*
    // We could reuse powers and remove the first element, yet this is cheaper than the shift that
    // would require
    let q = self.q();
    let mut z = ScalarVector(Vec::with_capacity(q));
    z.0.push(z_1);
    for _ in 1 .. q {
      z.0.push(*z.0.last().unwrap() * z_1);
    }
    z.0.truncate(q);

    YzChallenges { y_inv, z }
  }

  /// Prove for this statement/witness.
  pub fn prove<R: RngCore + CryptoRng>(
    self,
    rng: &mut R,
    transcript: &mut Transcript,
    mut witness: ArithmeticCircuitWitness<C>,
  ) -> Result<(), AcError> {
    let n = self.n();
    let c = self.c();
    let m = self.m();

    // Check the witness length and pad it to the necessary power of two
    if witness.aL.len() > n {
      Err(AcError::NotEnoughGenerators)?;
    }
    while witness.aL.len() < n {
      witness.aL.0.push(C::F::ZERO);
      witness.aR.0.push(C::F::ZERO);
      witness.aO.0.push(C::F::ZERO);
    }
    for c in &mut witness.c {
      if c.g_values.len() > n {
        Err(AcError::NotEnoughGenerators)?;
      }
      if c.h_values.len() > n {
        Err(AcError::NotEnoughGenerators)?;
      }
      // The Pedersen vector commitments internally have n terms
      while c.g_values.len() < n {
        c.g_values.0.push(C::F::ZERO);
      }
      while c.h_values.len() < n {
        c.h_values.0.push(C::F::ZERO);
      }
    }

    // Check the witness's consistency with the statement
    if (c != witness.c.len()) || (m != witness.v.len()) {
      Err(AcError::InconsistentWitness)?;
    }

    #[cfg(debug_assertions)]
    {
      for (commitment, opening) in self.V.0.iter().zip(witness.v.iter()) {
        if *commitment != opening.commit(self.generators.g(), self.generators.h()) {
          Err(AcError::InconsistentWitness)?;
        }
      }
      for (commitment, opening) in self.C.0.iter().zip(witness.c.iter()) {
        if Some(*commitment) !=
          opening.commit(
            self.generators.g_bold_slice(),
            self.generators.h_bold_slice(),
            self.generators.h(),
          )
        {
          Err(AcError::InconsistentWitness)?;
        }
      }
      for i in 0 .. self.q() {
        if (self.WL.data[i].iter().map(|(j, weight)| *weight * witness.aL[*j]).sum::<C::F>() +
          self.WR.data[i].iter().map(|(j, weight)| *weight * witness.aR[*j]).sum::<C::F>() +
          self.WO.data[i].iter().map(|(j, weight)| *weight * witness.aO[*j]).sum::<C::F>() +
          self
            .WCL
            .iter()
            .enumerate()
            .map(|(c, WCL)| {
              WCL.data[i]
                .iter()
                .map(|(j, weight)| *weight * witness.c[c].g_values[*j])
                .sum::<C::F>()
            })
            .sum::<C::F>() +
          self
            .WCR
            .iter()
            .enumerate()
            .map(|(c, WCR)| {
              WCR.data[i]
                .iter()
                .map(|(j, weight)| *weight * witness.c[c].h_values[*j])
                .sum::<C::F>()
            })
            .sum::<C::F>()) !=
          (self.WV.data[i].iter().map(|(j, weight)| *weight * witness.v[*j].value).sum::<C::F>() +
            self.c[i])
        {
          Err(AcError::InconsistentWitness)?;
        }
      }
    }

    let alpha = C::F::random(&mut *rng);
    let beta = C::F::random(&mut *rng);
    let rho = C::F::random(&mut *rng);

    let AI = {
      let alg = witness.aL.0.iter().enumerate().map(|(i, aL)| (*aL, self.generators.g_bold(i)));
      let arh = witness.aR.0.iter().enumerate().map(|(i, aR)| (*aR, self.generators.h_bold(i)));
      let ah = core::iter::once((alpha, self.generators.h()));
      let mut AI_terms = alg.chain(arh).chain(ah).collect::<Vec<_>>();
      let AI = multiexp(&AI_terms);
      AI_terms.zeroize();
      AI
    };
    let AO = {
      let aog = witness.aO.0.iter().enumerate().map(|(i, aO)| (*aO, self.generators.g_bold(i)));
      let bh = core::iter::once((beta, self.generators.h()));
      let mut AO_terms = aog.chain(bh).collect::<Vec<_>>();
      let AO = multiexp(&AO_terms);
      AO_terms.zeroize();
      AO
    };

    let mut sL = ScalarVector(Vec::with_capacity(n));
    let mut sR = ScalarVector(Vec::with_capacity(n));
    for _ in 0 .. n {
      sL.0.push(C::F::random(&mut *rng));
      sR.0.push(C::F::random(&mut *rng));
    }
    let S = {
      let slg = sL.0.iter().enumerate().map(|(i, sL)| (*sL, self.generators.g_bold(i)));
      let srh = sR.0.iter().enumerate().map(|(i, sR)| (*sR, self.generators.h_bold(i)));
      let rh = core::iter::once((rho, self.generators.h()));
      let mut S_terms = slg.chain(srh).chain(rh).collect::<Vec<_>>();
      let S = multiexp(&S_terms);
      S_terms.zeroize();
      S
    };

    transcript.push_point(AI);
    transcript.push_point(AO);
    transcript.push_point(S);
    let y = transcript.challenge();
    let z = transcript.challenge();
    let YzChallenges { y_inv, z } = self.yz_challenges(y, z);
    let y = ScalarVector::powers(y, n);

    // t is a n'-term polynomial
    // While Bulletproofs discuss it as a 6-term polynomial, Generalized Bulletproofs re-defines it
    // as `2(n' + 1)`-term, where `n'` is `2 (c + 1)`.
    // When `c = 0`, `n' = 2`, and t is `6` (which lines up with Bulletproofs having a 6-term
    // polynomial).

    // ni = n'
    let ni = 2 * (c + 1);
    // These indexes are from the Generalized Bulletproofs paper
    #[rustfmt::skip]
    let ilr = ni / 2; // 1 if c = 0
    #[rustfmt::skip]
    let io = ni; // 2 if c = 0
    #[rustfmt::skip]
    let is = ni + 1; // 3 if c = 0
    #[rustfmt::skip]
    let jlr = ni / 2; // 1 if c = 0
    #[rustfmt::skip]
    let jo = 0; // 0 if c = 0
    #[rustfmt::skip]
    let js = ni + 1; // 3 if c = 0

    // If c = 0, these indexes perfectly align with the stated powers of X from the Bulletproofs
    // paper for the following coefficients

    // Declare the l and r polynomials, assigning the traditional coefficients to their positions
    let mut l = vec![];
    let mut r = vec![];
    for _ in 0 .. (is + 1) {
      l.push(ScalarVector::new(0));
      r.push(ScalarVector::new(0));
    }
    l[ilr] = (self.WR.mul_vec(n, &z) * &y_inv) + &witness.aL;
    l[io] = witness.aO.clone();
    l[is] = sL;
    r[jlr] = self.WL.mul_vec(n, &z) + &(witness.aR.clone() * &y);
    r[jo] = self.WO.mul_vec(n, &z) - &y;
    r[js] = sR * &y;

    // Pad as expected
    for l in &mut l {
      debug_assert!((l.len() == 0) || (l.len() == n));
      if l.len() == 0 {
        *l = ScalarVector::new(n);
      }
    }
    for r in &mut r {
      debug_assert!((r.len() == 0) || (r.len() == n));
      if r.len() == 0 {
        *r = ScalarVector::new(n);
      }
    }

    // We now fill in the vector commitments
    // We use unused coefficients of l increasing from 0 (skipping ilr), and unused coefficients of
    // r decreasing from n' (skipping jlr)
    for (i, ((c, WCL), WCR)) in witness.c.iter().zip(self.WCL).zip(self.WCR).enumerate() {
      let i = i + 1;
      let j = ni - i;

      l[i] = c.g_values.clone();
      l[j] = WCR.mul_vec(n, &z) * &y_inv;
      r[j] = WCL.mul_vec(n, &z);
      r[i] = (c.h_values.clone() * &y) + &r[i];
    }

    // Multiply them to obtain t
    let mut t = ScalarVector::new(1 + (2 * (l.len() - 1)));
    for (i, l) in l.iter().enumerate() {
      for (j, r) in r.iter().enumerate() {
        let new_coeff = i + j;
        t[new_coeff] += l.inner_product(r);
      }
    }

    // Per Bulletproofs, calculate masks tau for each t where (i > 0) && (i != 2)
    // Per Generalized Bulletproofs, calculate masks tau for each t where i != n'
    // With Bulletproofs, t[0] is zero, hence its omission, yet Generalized Bulletproofs uses it
    let mut tau_before_ni = vec![];
    for _ in 0 .. ni {
      tau_before_ni.push(C::F::random(&mut *rng));
    }
    let mut tau_after_ni = vec![];
    for _ in 0 .. t.0[(ni + 1) ..].len() {
      tau_after_ni.push(C::F::random(&mut *rng));
    }
    // Calculate commitments to the coefficients of t, blinded by tau
    assert_eq!(t.0[0 .. ni].len(), tau_before_ni.len());
    for (t, tau) in t.0[0 .. ni].iter().zip(tau_before_ni.iter()) {
      transcript.push_point(multiexp(&[(*t, self.generators.g()), (*tau, self.generators.h())]));
    }
    assert_eq!(t.0[(ni + 1) ..].len(), tau_after_ni.len());
    for (t, tau) in t.0[(ni + 1) ..].iter().zip(tau_after_ni.iter()) {
      transcript.push_point(multiexp(&[(*t, self.generators.g()), (*tau, self.generators.h())]));
    }

    let x: ScalarVector<C::F> = ScalarVector::powers(transcript.challenge(), t.len());

    let poly_eval = |poly: &[ScalarVector<C::F>], x: &ScalarVector<_>| -> ScalarVector<_> {
      let mut res = ScalarVector::<C::F>::new(poly[0].0.len());
      for (i, coeff) in poly.iter().enumerate() {
        res = res + &(coeff.clone() * x[i]);
      }
      res
    };
    let l = poly_eval(&l, &x);
    let r = poly_eval(&r, &x);

    let t_caret = l.inner_product(&r);

    let tau_x = {
      let mut tau_x_poly = vec![];
      tau_x_poly.extend(tau_before_ni);
      tau_x_poly.push(
        self
          .WV
          .mul_vec(m, &z)
          .inner_product(&ScalarVector(witness.v.iter().map(|v| v.mask).collect())),
      );
      tau_x_poly.extend(tau_after_ni);

      let mut tau_x = C::F::ZERO;
      for (i, coeff) in tau_x_poly.into_iter().enumerate() {
        tau_x += coeff * x[i];
      }
      tau_x
    };

    // Calculate u for the powers of x variable to ilr/io/is
    let u = {
      // Calculate the first part of u
      let mut u = (alpha * x[ilr]) + (beta * x[io]) + (rho * x[is]);

      // Incorporate the commitment masks multiplied by the associated power of x
      for (i, commitment) in witness.c.iter().enumerate() {
        let i = i + 1;
        u += x[i] * commitment.mask;
      }
      u
    };

    // Use the Inner-Product argument to prove for this
    // P = t_caret * g + l * g_bold + r * (y_inv * h_bold)

    let mut P_terms = Vec::with_capacity(1 + (2 * self.generators.len()));
    assert_eq!(l.len(), r.len());
    for (i, (l, r)) in l.0.iter().zip(r.0.iter()).enumerate() {
      P_terms.push((*l, self.generators.g_bold(i)));
      P_terms.push((y_inv[i] * r, self.generators.h_bold(i)));
    }

    // Protocol 1, inlined, since our IpStatement is for Protocol 2
    transcript.push_scalar(tau_x);
    transcript.push_scalar(u);
    transcript.push_scalar(t_caret);
    let ip_x = transcript.challenge();
    P_terms.push((ip_x * t_caret, self.generators.g()));
    IpStatement::new(
      self.generators,
      y_inv,
      ip_x,
      // Safe since IpStatement isn't a ZK proof
      P::Prover(multiexp_vartime(&P_terms)),
    )
    .unwrap()
    .prove(transcript, IpWitness::new(l, r).unwrap())
    .map_err(AcError::Ip)
  }

  /// Verify a proof for this statement.
  pub fn verify<R: RngCore + CryptoRng>(
    self,
    rng: &mut R,
    verifier: &mut BatchVerifier<C>,
    transcript: &mut VerifierTranscript,
  ) -> Result<(), AcError> {
    let n = self.n();
    let c = self.c();
    let m = self.m();

    let ni = 2 * (c + 1);

    let ilr = ni / 2;
    let io = ni;
    let is = ni + 1;
    let jlr = ni / 2;

    let l_r_poly_len = 1 + ni + 1;
    let t_poly_len = (2 * l_r_poly_len) - 1;

    let AI = transcript.read_point::<C>().map_err(|_| AcError::IncompleteProof)?;
    let AO = transcript.read_point::<C>().map_err(|_| AcError::IncompleteProof)?;
    let S = transcript.read_point::<C>().map_err(|_| AcError::IncompleteProof)?;
    let y = transcript.challenge();
    let z = transcript.challenge();
    let YzChallenges { y_inv, z } = self.yz_challenges(y, z);

    let delta = (self.WR.mul_vec(n, &z) * &y_inv).inner_product(&self.WL.mul_vec(n, &z));

    let mut T_before_ni = Vec::with_capacity(ni);
    let mut T_after_ni = Vec::with_capacity(t_poly_len - ni - 1);
    for _ in 0 .. ni {
      T_before_ni.push(transcript.read_point::<C>().map_err(|_| AcError::IncompleteProof)?);
    }
    for _ in 0 .. (t_poly_len - ni - 1) {
      T_after_ni.push(transcript.read_point::<C>().map_err(|_| AcError::IncompleteProof)?);
    }
    let x: ScalarVector<C::F> = ScalarVector::powers(transcript.challenge(), t_poly_len);

    let tau_x = transcript.read_scalar::<C>().map_err(|_| AcError::IncompleteProof)?;
    let u = transcript.read_scalar::<C>().map_err(|_| AcError::IncompleteProof)?;
    let t_caret = transcript.read_scalar::<C>().map_err(|_| AcError::IncompleteProof)?;

    // Lines 88-90, modified per Generalized Bulletproofs as needed w.r.t. t
    {
      let verifier_weight = C::F::random(&mut *rng);
      // lhs of the equation, weighted to enable batch verification
      verifier.g += t_caret * verifier_weight;
      verifier.h += tau_x * verifier_weight;

      // rhs of the equation, negated to cause a sum to zero
      verifier.g -= verifier_weight * x[ni] * (delta + z.inner_product(&self.c));
      let V_weights = self.WV.mul_vec(m, &z) * x[ni];
      assert_eq!(V_weights.len(), self.V.len());
      for pair in V_weights.0.into_iter().zip(self.V.0) {
        verifier.additional.push((-verifier_weight * pair.0, pair.1));
      }
      for (i, T) in T_before_ni.into_iter().enumerate() {
        verifier.additional.push((-verifier_weight * x[i], T));
      }
      for (i, T) in T_after_ni.into_iter().enumerate() {
        verifier.additional.push((-verifier_weight * x[ni + 1 + i], T));
      }
    }

    let verifier_weight = C::F::random(&mut *rng);

    // This following block effectively calculates P, within the multiexp
    {
      verifier.additional.push((verifier_weight * x[ilr], AI));
      verifier.additional.push((verifier_weight * x[io], AO));
      // h' ** y is equivalent to h as h' is h ** y_inv
      let mut log2_n = 0;
      while (1 << log2_n) != n {
        log2_n += 1;
      }
      verifier.h_sum[log2_n] -= verifier_weight;
      verifier.additional.push((verifier_weight * x[is], S));

      let mut h_bold_scalars = ScalarVector::new(n);
      // Lines 85-87 calculate WL, WR, WO
      // We preserve them in terms of g_bold and h_bold for a more efficient multiexp
      h_bold_scalars = h_bold_scalars + &(self.WL.mul_vec(n, &z) * x[jlr]);
      // WO is weighted by x**jo where jo == 0, hence why we can ignore the x term
      h_bold_scalars = h_bold_scalars + &self.WO.mul_vec(n, &z);

      for (i, wr) in (self.WR.mul_vec(n, &z) * &y_inv * x[jlr]).0.into_iter().enumerate() {
        verifier.g_bold[i] += verifier_weight * wr;
      }

      // Push the terms for C, which increment from 0, and the terms for WC, which decrement from
      // n'
      assert_eq!(self.C.len(), self.WCL.len());
      assert_eq!(self.C.len(), self.WCR.len());
      for (i, ((C, WCL), WCR)) in
        self.C.0.into_iter().zip(self.WCL.into_iter()).zip(self.WCR.into_iter()).enumerate()
      {
        let i = i + 1;
        let j = ni - i;
        verifier.additional.push((verifier_weight * x[i], C));
        h_bold_scalars = h_bold_scalars + &(WCL.mul_vec(n, &z) * x[j]);
        for (i, scalar) in (WCR.mul_vec(n, &z) * &y_inv * x[j]).0.into_iter().enumerate() {
          verifier.g_bold[i] += verifier_weight * scalar;
        }
      }

      // All terms for h_bold here have actually been for h_bold', h_bold * y_inv
      h_bold_scalars = h_bold_scalars * &y_inv;
      for (i, scalar) in h_bold_scalars.0.into_iter().enumerate() {
        verifier.h_bold[i] += verifier_weight * scalar;
      }

      // Remove u * h from P
      verifier.h -= verifier_weight * u;
    }

    // Prove for lines 88, 92 with an Inner-Product statement
    // This inlines Protocol 1, as our IpStatement implements Protocol 2
    let ip_x = transcript.challenge();
    // P is amended with this additional term
    verifier.g += verifier_weight * ip_x * t_caret;
    IpStatement::new(self.generators, y_inv, ip_x, P::Verifier { verifier_weight })
      .unwrap()
      .verify(verifier, transcript)
      .map_err(AcError::Ip)?;

    Ok(())
  }
}
