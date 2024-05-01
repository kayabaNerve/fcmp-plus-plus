use rand_core::{RngCore, CryptoRng};

use zeroize::{Zeroize, ZeroizeOnDrop};

use transcript::Transcript;

use multiexp::{multiexp, BatchVerifier};
use ciphersuite::{
  group::{
    ff::{Field, PrimeField},
    GroupEncoding,
  },
  Ciphersuite,
};

use crate::{
  ScalarVector, ScalarMatrix, PointVector, ProofGenerators, PedersenCommitment,
  PedersenVectorCommitment,
  inner_product::{IpError, IpStatement, IpWitness, IpProof},
};

/// Bulletproofs' Arithmetic Circuit Statement from 5.1, modified per Generalized Bulletproofs.
///
/// aL * aR = aO, WL * aL + WR * aR + WO * aO = WV * V + c
/// is modified to
/// aL * aR = aO, WL * aL + WR * aR + WO * aO + WC * C = WV * V + c
#[derive(Clone, Debug)]
pub struct ArithmeticCircuitStatement<'a, T: 'static + Transcript, C: Ciphersuite> {
  generators: ProofGenerators<'a, T, C>,

  // Circuit constraints
  WL: ScalarMatrix<C>,
  WR: ScalarMatrix<C>,
  WO: ScalarMatrix<C>,
  WV: ScalarMatrix<C>,
  WC: Vec<ScalarMatrix<C>>,
  c: ScalarVector<C::F>,

  // The commitments, vector and non-vector
  C: PointVector<C>,
  V: PointVector<C>,
}

impl<'a, T: 'static + Transcript, C: Ciphersuite> Zeroize for ArithmeticCircuitStatement<'a, T, C> {
  fn zeroize(&mut self) {
    self.WL.zeroize();
    self.WR.zeroize();
    self.WO.zeroize();
    self.WC.zeroize();
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
  DifferingLrLengths,
  InconsistentAmountOfConstraints,
  ConstrainedNonExistentTerm,
  ConstrainedNonExistentCommitment,
  IncorrectAmountOfGenerators,
  InconsistentWitness,
  IncorrectTBeforeNiLength,
  IncorrectTAfterNiLength,
  Ip(IpError),
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

    let aO = aL.clone() * &aR;
    Ok(ArithmeticCircuitWitness { aL, aR, aO, c, v })
  }
}

/// A proof for an arithmetic circuit statement.
#[derive(Clone, Debug, Zeroize)]
pub struct ArithmeticCircuitProof<C: Ciphersuite> {
  AI: C::G,
  AO: C::G,
  S: C::G,

  // TODO: Merge these two vectors
  T_before_ni: Vec<C::G>,
  T_after_ni: Vec<C::G>,
  tau_x: C::F,
  u: C::F,
  t_caret: C::F,

  ip: IpProof<C>,
}

struct YzChallenges<C: Ciphersuite> {
  y: C::F,
  y_inv: ScalarVector<C::F>,
  z: ScalarVector<C::F>,
}

impl<'a, T: 'static + Transcript, C: Ciphersuite> ArithmeticCircuitStatement<'a, T, C> {
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
  /// static program and higher-level statement. If your constraints are variable with regards to
  /// variables which aren't the commitments, you must transcript them as needed before calling
  /// prove/verify.
  #[allow(clippy::too_many_arguments)]
  pub fn new(
    generators: ProofGenerators<'a, T, C>,
    WL: ScalarMatrix<C>,
    WR: ScalarMatrix<C>,
    WO: ScalarMatrix<C>,
    WC: Vec<ScalarMatrix<C>>,
    WV: ScalarMatrix<C>,
    c: ScalarVector<C::F>,
    C: PointVector<C>,
    V: PointVector<C>,
  ) -> Result<Self, AcError> {
    // n is the amount of multiplications
    let n = generators.len();

    // m is the amount of Pedersen Commitments
    let m = V.len();

    // q is the amount of constraints
    let q = WL.len();
    if (WR.len() != q) || (WO.len() != q) || (WV.len() != q) || (c.len() != q) {
      Err(AcError::InconsistentAmountOfConstraints)?;
    }
    for WC in &WC {
      if WC.len() != q {
        Err(AcError::InconsistentAmountOfConstraints)?;
      }
    }

    // Check if the highest index exceeds n, meaning this matrix has a faulty constraint
    if WL.highest_index.max(WR.highest_index).max(WO.highest_index) >= n {
      Err(AcError::ConstrainedNonExistentTerm)?;
    }

    if WC.len() > C.len() {
      Err(AcError::ConstrainedNonExistentCommitment)?;
    }
    for WC in &WC {
      // The Pedersen Vector Commitments have as many terms as we have multiplications
      if WC.highest_index > n {
        Err(AcError::ConstrainedNonExistentTerm)?;
      }
    }

    if WV.highest_index > m {
      Err(AcError::ConstrainedNonExistentCommitment)?;
    }

    Ok(Self { generators, WL, WR, WO, WC, WV, c, C, V })
  }

  fn initial_transcript(&self, transcript: &mut T, AI: C::G, AO: C::G, S: C::G) -> YzChallenges<C> {
    transcript.domain_separate(b"arithmetic_circuit_proof");

    transcript.append_message(b"generators", self.generators.transcript.as_ref());

    let n = self.n();
    transcript.append_message(
      b"n",
      u32::try_from(n).expect("more than 2**32 multiplications").to_le_bytes(),
    );
    let q = self.q();
    transcript
      .append_message(b"q", u32::try_from(q).expect("more than 2**32 constraints").to_le_bytes());

    self.C.transcript(transcript, b"vector_commitment");
    self.V.transcript(transcript, b"commitment");

    transcript.append_message(b"AI", AI.to_bytes());
    transcript.append_message(b"AO", AO.to_bytes());
    transcript.append_message(b"S", S.to_bytes());

    let y = C::hash_to_F(b"arithmetic_circuit_proof", transcript.challenge(b"y").as_ref());
    if bool::from(y.is_zero()) {
      panic!("zero challenge in arithmetic circuit proof");
    }
    let y_inv = y.invert().unwrap();

    let y_inv = ScalarVector::powers(y_inv, n);

    let z_1 = C::hash_to_F(b"arithmetic_circuit_proof", transcript.challenge(b"z").as_ref());
    if bool::from(z_1.is_zero()) {
      panic!("zero challenge in arithmetic circuit proof");
    }

    // Powers of z *starting with z**1*
    // We could reuse powers and remove the first element, yet this is cheaper than the shift that
    // would require
    let mut z = ScalarVector(Vec::with_capacity(q));
    z.0.push(z_1);
    for _ in 1 .. q {
      z.0.push(*z.0.last().unwrap() * z_1);
    }

    YzChallenges { y, y_inv, z }
  }

  fn transcript_Ts(
    transcript: &mut T,
    T_before_ni: &[C::G],
    T_after_ni: &[C::G],
  ) -> ScalarVector<C::F> {
    for Ti in T_before_ni {
      transcript.append_message(b"Ti", Ti.to_bytes());
    }
    for Ti in T_after_ni {
      transcript.append_message(b"Tni+1+i", Ti.to_bytes());
    }

    let x = C::hash_to_F(b"arithmetic_circuit_proof", transcript.challenge(b"x").as_ref());
    if bool::from(x.is_zero()) {
      panic!("zero challenge in arithmetic circuit proof");
    }
    ScalarVector::powers(x, T_before_ni.len() + 1 + T_after_ni.len())
  }

  fn transcript_tau_x_u_t_caret(transcript: &mut T, tau_x: C::F, u: C::F, t_caret: C::F) -> C::F {
    transcript.append_message(b"tau_x", tau_x.to_repr());
    transcript.append_message(b"u", u.to_repr());
    transcript.append_message(b"t_caret", t_caret.to_repr());
    let ip_x = C::hash_to_F(b"arithmetic_circuit_proof", transcript.challenge(b"ip_x").as_ref());
    if bool::from(ip_x.is_zero()) {
      panic!("zero challenge in arithmetic circuit proof");
    }
    ip_x
  }

  pub fn prove<R: RngCore + CryptoRng>(
    self,
    rng: &mut R,
    transcript: &mut T,
    mut witness: ArithmeticCircuitWitness<C>,
  ) -> Result<ArithmeticCircuitProof<C>, AcError> {
    let n = self.n();
    let c = self.c();
    let m = self.m();

    // Check the witness length and pad it to the necessary power of two
    if witness.aL.len() > n {
      Err(AcError::IncorrectAmountOfGenerators)?;
    }
    while witness.aL.len() < n {
      witness.aL.0.push(C::F::ZERO);
      witness.aR.0.push(C::F::ZERO);
      witness.aO.0.push(C::F::ZERO);
    }
    for c in &mut witness.c {
      if c.values.len() > n {
        Err(AcError::IncorrectAmountOfGenerators)?;
      }
      // The Pedersen vector commitments internally have n terms
      while c.values.len() < n {
        c.values.0.push(C::F::ZERO);
      }
    }

    // Check the witness's consistency with the statement
    if (c != witness.c.len()) || (m != witness.v.len()) {
      Err(AcError::InconsistentWitness)?;
    }
    for (commitment, opening) in self.V.0.iter().zip(witness.v.iter()) {
      if *commitment != opening.commit(self.generators.g(), self.generators.h()) {
        Err(AcError::InconsistentWitness)?;
      }
    }
    // TODO: Check WL WR WO WV WC C for inconsistencies

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

    let YzChallenges { y, y_inv, z } = self.initial_transcript(transcript, AI, AO, S);
    let y = ScalarVector::powers(y, n);
    /*
    let delta = {
      let lhs = self.WR.mul_vec(n, &z) * &y_inv;
      let rhs = self.WL.mul_vec(n, &z);
      lhs.inner_product(&rhs)
    };
    */

    // t is a n'-term polynomial
    // While Bulletproofs discuss it as a 6-term polynomial, Generalized Bulletproofs re-defines it
    // as `2(n' + 1)`, where `n'` is `2 + 2 (c // 2)`.
    // When `c = 0`, `n' = 2`, and t is `6` (which lines up with Bulletproofs having a 6-term
    // polynomial).

    // ni = n'
    let ni = 2 + (2 * (c / 2));
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
      assert!((l.len() == 0) || (l.len() == n));
      if l.len() == 0 {
        *l = ScalarVector::new(n);
      }
    }
    for r in &mut r {
      assert!((r.len() == 0) || (r.len() == n));
      if r.len() == 0 {
        *r = ScalarVector::new(n);
      }
    }

    // We now fill in the vector commitments
    // We use unused coefficients of l increasing from 0 (skipping ilr), and unused coefficients of
    // r decreasing from n' (skipping jlr)
    for (mut i, (c, WC)) in witness.c.iter().zip(self.WC).enumerate() {
      if i >= ilr {
        i += 1;
      }
      // Because i has skipped ilr, j will skip jlr
      let j = ni - i;

      l[i] = c.values.clone();
      r[j] = WC.mul_vec(n, &z);
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
    let mut T_before_ni = vec![];
    for (t, tau) in t.0[0 .. ni].iter().zip(tau_before_ni.iter()) {
      T_before_ni.push(multiexp(&[(*t, self.generators.g()), (*tau, self.generators.h())]));
    }
    let mut T_after_ni = vec![];
    for (t, tau) in t.0[(ni + 1) ..].iter().zip(tau_after_ni.iter()) {
      T_after_ni.push(multiexp(&[(*t, self.generators.g()), (*tau, self.generators.h())]));
    }

    let x = Self::transcript_Ts(transcript, &T_before_ni, &T_after_ni);

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
      for (mut i, commitment) in witness.c.iter().enumerate() {
        // If this index is ni / 2, skip it
        if i == (ni / 2) {
          i += 1;
        }
        u += x[i] * commitment.mask;
      }
      u
    };

    // Use the Inner-Product argument to prove for this
    let ip = {
      // P = t_caret * g + l * g_bold + r * (y_inv * h_bold)

      let mut P_terms = Vec::with_capacity(1 + (2 * self.generators.len()));
      for (i, (l, r)) in l.0.iter().zip(r.0.iter()).enumerate() {
        P_terms.push((*l, self.generators.g_bold(i)));
        P_terms.push((y_inv[i] * r, self.generators.h_bold(i)));
      }

      // Protocol 1, inlined, since our IpStatement is for Protocol 2
      let ip_x = Self::transcript_tau_x_u_t_caret(transcript, tau_x, u, t_caret);
      P_terms.push((ip_x * t_caret, self.generators.g()));
      IpStatement::new_without_P_transcript(
        self.generators.g_bold_slice(),
        self.generators.h_bold_slice(),
        y_inv,
        self.generators.g() * ip_x,
        P_terms,
      )
      .unwrap()
      .prove(transcript, IpWitness::new(l, r).unwrap())
      .unwrap()
    };

    Ok(ArithmeticCircuitProof { AI, AO, S, T_before_ni, T_after_ni, tau_x, u, t_caret, ip })
  }

  pub fn verify<R: RngCore + CryptoRng>(
    self,
    rng: &mut R,
    verifier: &mut BatchVerifier<(), C::G>,
    transcript: &mut T,
    proof: ArithmeticCircuitProof<C>,
  ) -> Result<(), AcError> {
    let n = self.n();
    let c = self.c();
    let m = self.m();

    let ni = 2 + (2 * (c / 2));

    let ilr = ni / 2;
    let io = ni;
    let is = ni + 1;
    let jlr = ni / 2;

    let l_r_poly_len = 1 + ni + 1;
    let t_poly_len = (2 * l_r_poly_len) - 1;

    if proof.T_before_ni.len() != ni {
      Err(AcError::IncorrectTBeforeNiLength)?;
    }
    if proof.T_after_ni.len() != (t_poly_len - ni - 1) {
      Err(AcError::IncorrectTAfterNiLength)?;
    }

    let YzChallenges { y: _, y_inv, z } =
      self.initial_transcript(transcript, proof.AI, proof.AO, proof.S);

    let delta = (self.WR.mul_vec(n, &z) * &y_inv).inner_product(&self.WL.mul_vec(n, &z));

    let x = Self::transcript_Ts(transcript, &proof.T_before_ni, &proof.T_after_ni);

    // Lines 88-90, modified per Generalized Bulletproofs as needed w.r.t. t
    {
      let mut lhs = vec![(proof.t_caret, self.generators.g()), (proof.tau_x, self.generators.h())];

      let mut rhs = Vec::with_capacity(self.V.len() + t_poly_len);
      rhs.push((x[ni] * (delta + z.inner_product(&self.c)), self.generators.g()));
      for pair in (self.WV.mul_vec(m, &z) * x[ni]).0.into_iter().zip(self.V.0) {
        rhs.push(pair);
      }
      for (i, T) in proof.T_before_ni.into_iter().enumerate() {
        rhs.push((x[i], T));
      }
      for (i, T) in proof.T_after_ni.into_iter().enumerate() {
        rhs.push((x[ni + 1 + i], T));
      }

      lhs.reserve(rhs.len());
      for rhs in rhs {
        lhs.push((-rhs.0, rhs.1));
      }
      let check = lhs;

      verifier.queue(rng, (), check);
    }

    let mut P_terms = {
      let mut P_terms = vec![
        (x[ilr], proof.AI),
        (x[io], proof.AO),
        // h' ** y is equivalent to h as h' is h ** y_inv
        (-C::F::ONE, self.generators.h_sum()),
        (x[is], proof.S),
      ];
      P_terms.reserve((2 * n) + self.C.len() + 2);

      let mut h_bold_scalars = ScalarVector::new(n);
      // Lines 85-87 calculate WL, WR, WO
      // We preserve them in terms of g_bold and h_bold for a more efficient multiexp
      h_bold_scalars = h_bold_scalars + &(self.WL.mul_vec(n, &z) * x[jlr]);
      // WO is weighted by x**jo where jo == 0, hence why we can ignore the x term
      h_bold_scalars = h_bold_scalars + &self.WO.mul_vec(n, &z);

      for (i, wr) in (self.WR.mul_vec(n, &z) * &y_inv * x[jlr]).0.into_iter().enumerate() {
        P_terms.push((wr, self.generators.g_bold(i)));
      }

      // Push the terms for C, which increment from 0, and the terms for WC, which decrement from
      // n'
      for (mut i, (C, WC)) in self.C.0.into_iter().zip(self.WC.into_iter()).enumerate() {
        if i == (ni / 2) {
          i += 1;
        }
        let j = ni - i;
        P_terms.push((x[i], C));
        h_bold_scalars = h_bold_scalars + &(WC.mul_vec(n, &z) * x[j]);
      }

      // All terms for h_bold here have actually been for h_bold', h_bold * y_inv
      h_bold_scalars = h_bold_scalars * &y_inv;
      for (i, scalar) in h_bold_scalars.0.into_iter().enumerate() {
        P_terms.push((scalar, self.generators.h_bold(i)));
      }

      // Remove u * h
      P_terms.push((-proof.u, self.generators.h()));

      P_terms
    };

    // Prove for lines 88, 92 with an Inner-Product statement
    // This inlines Protocol 1, as our IpStatement implements Protocol 2
    let ip_x = Self::transcript_tau_x_u_t_caret(transcript, proof.tau_x, proof.u, proof.t_caret);
    P_terms.push((ip_x * proof.t_caret, self.generators.g()));
    IpStatement::new_without_P_transcript(
      self.generators.g_bold_slice(),
      self.generators.h_bold_slice(),
      y_inv,
      self.generators.g() * ip_x,
      P_terms,
    )
    .unwrap()
    .verify(rng, verifier, transcript, proof.ip)
    .map_err(AcError::Ip)?;

    Ok(())
  }
}
