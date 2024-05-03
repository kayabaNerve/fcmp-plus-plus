use rand_core::{RngCore, CryptoRng};

use transcript::Transcript;

use ciphersuite::{
  group::ff::{Field, PrimeField, PrimeFieldBits},
  Ciphersuite,
};

use crate::lincomb::*;
use crate::gadgets::*;

/// The witness for the satisfaction of this circuit.
#[derive(Clone, PartialEq, Eq, Debug)]
#[allow(non_snake_case)]
struct ProverData<F: Field> {
  aL: Vec<F>,
  aR: Vec<F>,
  C: Vec<Vec<F>>,
}

/// A struct representing a circuit.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) struct Circuit<C: Ciphersuite> {
  muls: usize,
  commitments: usize,
  // A series of linear combinations which must evaluate to 0.
  pub(crate) constraints: Vec<LinComb<C::F>>,
  prover: Option<ProverData<C::F>>,
}

impl<C: Ciphersuite> Circuit<C> {
  // Create an instance to prove with.
  pub(crate) fn prove(commitments: Vec<Vec<C::F>>) -> Self {
    Self {
      muls: 0,
      commitments: commitments.len(),
      constraints: vec![],
      prover: Some(ProverData { aL: vec![], aR: vec![], C: commitments }),
    }
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
      for (i, j, weight) in &constraint.WC {
        res += prover.C[*i][*j] * weight;
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

    if let Some(a) = a {
      self.constraints.push(a.term(-C::F::ONE, l));
    }
    if let Some(b) = b {
      self.constraints.push(b.term(-C::F::ONE, r));
    }

    assert_eq!(self.prover.is_some(), witness.is_some());
    if let Some(witness) = witness {
      let prover = self.prover.as_mut().unwrap();
      prover.aL.push(witness.0);
      prover.aR.push(witness.1);
    }

    (l, r, o)
  }

  #[allow(non_snake_case, clippy::too_many_arguments)]
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
    let O = self.on_curve(curve, O);
    let o_blind = self.discrete_log_pok(transcript, curve, o_blind);
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
    let i_blind_u = self.discrete_log(transcript, curve, i_blind_u);
    self.incomplete_add_pub(I_tilde, i_blind_u, I);

    let i_blind_v = self.discrete_log(transcript, curve, i_blind_v);
    let i_blind_blind = self.discrete_log_pok(transcript, curve, i_blind_blind);
    self.incomplete_add_pub(R, i_blind_v, i_blind_blind);

    let C = self.on_curve(curve, C);
    let c_blind = self.discrete_log_pok(transcript, curve, c_blind);
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
    let blind = self.discrete_log_pok(transcript, curve, blind);
    let hash = self.on_curve(curve, hash);
    self.incomplete_add_pub(blinded_hash, blind, hash);
    self.permissible(C::F::ONE, C::F::ONE, hash.y);
    self.member_of_list(hash.x.into(), branch.into_iter().map(Into::into).collect::<Vec<_>>());
  }
}
