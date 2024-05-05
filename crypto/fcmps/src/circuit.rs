use transcript::Transcript;

use ciphersuite::{group::ff::Field, Ciphersuite};

use generalized_bulletproofs::{
  ScalarVector, ScalarMatrix, PointVector, PedersenVectorCommitment, ProofGenerators,
  arithmetic_circuit_proof::{AcError, ArithmeticCircuitStatement, ArithmeticCircuitWitness},
};

use crate::lincomb::*;
use crate::gadgets::*;

/// The witness for the satisfaction of this circuit.
#[derive(Clone, PartialEq, Eq, Debug)]
struct ProverData<F: Field> {
  aL: Vec<F>,
  aR: Vec<F>,
  C: Vec<Vec<F>>,
}

/// A struct representing a circuit.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) struct Circuit<C: Ciphersuite> {
  muls: usize,
  // A series of linear combinations which must evaluate to 0.
  constraints: Vec<LinComb<C::F>>,
  prover: Option<ProverData<C::F>>,
}

impl<C: Ciphersuite> Circuit<C> {
  // Returns the amount of multiplications used by this circuit.
  pub(crate) fn muls(&self) -> usize {
    self.muls
  }

  // Create an instance to prove with.
  pub(crate) fn prove(commitments: Vec<Vec<C::F>>) -> Self {
    Self {
      muls: 0,
      constraints: vec![],
      prover: Some(ProverData { aL: vec![], aR: vec![], C: commitments }),
    }
  }

  // Create an instance to verify with.
  pub(crate) fn verify() -> Self {
    Self { muls: 0, constraints: vec![], prover: None }
  }

  /// Evaluate a constraint.
  ///
  /// Yields WL aL + WR aR + WO aO + WC C.
  ///
  /// Panics if the constraint references non-existent terms.
  ///
  /// Returns None if not a prover.
  pub(crate) fn eval(&self, constraint: &LinComb<C::F>) -> Option<C::F> {
    self.prover.as_ref().map(|prover| {
      let mut res = constraint.c;
      for (index, weight) in &constraint.WL {
        res += prover.aL[*index] * weight;
      }
      for (index, weight) in &constraint.WR {
        res += prover.aR[*index] * weight;
      }
      for (index, weight) in &constraint.WO {
        res += prover.aL[*index] * prover.aR[*index] * weight;
      }
      for (WC, C) in constraint.WC.iter().zip(&prover.C) {
        for (j, weight) in WC {
          res += C[*j] * weight;
        }
      }
      res
    })
  }

  /// Multiply two values, optionally constrained, returning the constrainable left/right/out
  /// terms.
  ///
  /// This will panic if passed a witness when this circuit isn't constructed for proving.
  pub(crate) fn mul(
    &mut self,
    a: Option<LinComb<C::F>>,
    b: Option<LinComb<C::F>>,
    witness: Option<(C::F, C::F)>,
  ) -> (Variable, Variable, Variable) {
    let l = Variable::aL(self.muls);
    let r = Variable::aR(self.muls);
    let o = Variable::aO(self.muls);
    self.muls += 1;

    assert_eq!(self.prover.is_some(), witness.is_some());
    if let Some(witness) = witness {
      let prover = self.prover.as_mut().unwrap();
      prover.aL.push(witness.0);
      prover.aR.push(witness.1);
    }

    if let Some(a) = a {
      self.constrain_equal_to_zero(a.term(-C::F::ONE, l));
    }
    if let Some(b) = b {
      self.constrain_equal_to_zero(b.term(-C::F::ONE, r));
    }

    (l, r, o)
  }

  pub(crate) fn constrain_equal_to_zero(&mut self, constraint: LinComb<C::F>) {
    if let Some(eval) = self.eval(&constraint) {
      assert_eq!(eval, C::F::ZERO);
    }
    self.constraints.push(constraint);
  }

  #[allow(clippy::too_many_arguments)]
  pub(crate) fn first_layer<T: Transcript>(
    &mut self,
    transcript: &mut T,
    curve: &CurveSpec<C::F>,

    O_tilde: (C::F, C::F),
    o_blind: ClaimedPointWithDlog<C::F>,
    O: (Variable, Variable),

    I_tilde: (C::F, C::F),
    i_blind_u: ClaimedPointWithDlog<C::F>,
    I: (Variable, Variable),

    R: (C::F, C::F),
    i_blind_v: ClaimedPointWithDlog<C::F>,
    i_blind_blind: ClaimedPointWithDlog<C::F>,

    C_tilde: (C::F, C::F),
    c_blind: ClaimedPointWithDlog<C::F>,
    C: (Variable, Variable),

    branch: Vec<Vec<Variable>>,
  ) {
    let mut challenges = self
      .discrete_log_challenges(
        transcript,
        curve,
        &[
          o_blind.generator,
          i_blind_u.generator,
          i_blind_v.generator,
          i_blind_blind.generator,
          c_blind.generator,
        ],
      )
      .into_iter();

    let O = self.on_curve(curve, O);
    let o_blind = self.discrete_log(curve, o_blind, challenges.next().unwrap());
    self.incomplete_add_pub(O_tilde, o_blind, O);

    // This cannot simply be removed in order to cheat this proof
    // The discrete logarithms we assert equal are actually asserting the variables we use to refer
    // to the discrete logarithms are equal
    // If a dishonest prover removes this assertion and passes two different sets of variables,
    // they'll generate a different circuit
    // An honest verifier will generate the intended circuit (using a consistent set of variables)
    // and still reject such proofs
    // This check only exists for sanity/safety to ensure an honest verifier doesn't mis-call this
    assert_eq!(
      i_blind_u.dlog, i_blind_v.dlog,
      "first layer passed differing variables for the dlog"
    );

    let I = self.on_curve(curve, I);
    let i_blind_u = self.discrete_log(curve, i_blind_u, challenges.next().unwrap());
    self.incomplete_add_pub(I_tilde, i_blind_u, I);

    let i_blind_v = self.discrete_log(curve, i_blind_v, challenges.next().unwrap());
    let i_blind_blind = self.discrete_log(curve, i_blind_blind, challenges.next().unwrap());
    self.incomplete_add_pub(R, i_blind_v, i_blind_blind);

    let C = self.on_curve(curve, C);
    let c_blind = self.discrete_log(curve, c_blind, challenges.next().unwrap());
    self.incomplete_add_pub(C_tilde, c_blind, C);

    self.permissible(C::F::ONE, C::F::ONE, O.y);
    self.permissible(C::F::ONE, C::F::ONE, C.y);
    self.tuple_member_of_list(transcript, vec![O.x, I.x, I.y, C.x], branch);
  }

  pub(crate) fn additional_layer<T: Transcript>(
    &mut self,
    transcript: &mut T,
    curve: &CurveSpec<C::F>,
    blinded_hash: (C::F, C::F),
    blind: ClaimedPointWithDlog<C::F>,
    hash: (Variable, Variable),
    branch: Vec<Variable>,
  ) {
    let challenge = self.discrete_log_challenges(transcript, curve, &[blind.generator]).remove(0);
    let blind = self.discrete_log(curve, blind, challenge);
    let hash = self.on_curve(curve, hash);
    self.incomplete_add_pub(blinded_hash, blind, hash);
    self.permissible(C::F::ONE, C::F::ONE, hash.y);
    self.member_of_list(hash.x.into(), branch.into_iter().map(Into::into).collect::<Vec<_>>());
  }

  #[allow(clippy::type_complexity)]
  pub(crate) fn statement<T: Transcript>(
    self,
    generators: ProofGenerators<'_, T, C>,
    C: Vec<C::G>,
    commitment_blinds: Vec<C::F>,
  ) -> Result<(ArithmeticCircuitStatement<'_, T, C>, Option<ArithmeticCircuitWitness<C>>), AcError>
  {
    let mut WL = ScalarMatrix::new();
    let mut WR = ScalarMatrix::new();
    let mut WO = ScalarMatrix::new();
    let mut WC = Vec::with_capacity(C.len());
    for _ in 0 .. C.len() {
      WC.push(ScalarMatrix::new());
    }
    let mut WV = ScalarMatrix::new();
    let mut c = ScalarVector(Vec::with_capacity(self.constraints.len()));

    for constraint in self.constraints {
      WL.push(constraint.WL);
      WR.push(constraint.WR);
      WO.push(constraint.WO);
      let cWC_len = constraint.WC.len();
      for (WC, cWC) in WC.iter_mut().zip(constraint.WC.into_iter()) {
        WC.push(cWC);
      }
      for WC in &mut WC[cWC_len ..] {
        WC.push(vec![]);
      }
      WV.push(vec![]);
      // We represent `c` as `+ c = 0`, yet BP uses `= c`
      // If we subtract `c` from both sides, we get `= -c`
      // Negate this to achieve the intended `c`
      c.0.push(-constraint.c);
    }

    let statement = ArithmeticCircuitStatement::new(
      generators,
      WL,
      WR,
      WO,
      WC,
      WV,
      c,
      PointVector(C),
      PointVector(vec![]),
    )?;

    let witness = self
      .prover
      .map(|prover| {
        assert_eq!(prover.C.len(), commitment_blinds.len());
        ArithmeticCircuitWitness::new(
          ScalarVector(prover.aL),
          ScalarVector(prover.aR),
          prover
            .C
            .into_iter()
            .zip(commitment_blinds)
            .map(|(values, blind)| PedersenVectorCommitment {
              values: ScalarVector(values),
              mask: blind,
            })
            .collect(),
          vec![],
        )
      })
      .transpose()?;

    Ok((statement, witness))
  }
}
