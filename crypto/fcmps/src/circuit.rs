use ciphersuite::Ciphersuite;

use generalized_bulletproofs::{
  PedersenVectorCommitment, ProofGenerators,
  transcript::Commitments,
  arithmetic_circuit_proof::{AcError, ArithmeticCircuitStatement, ArithmeticCircuitWitness},
};
pub(crate) use generalized_bulletproofs::arithmetic_circuit_proof::{Variable, LinComb};

use generalized_bulletproofs_circuit_abstraction::{Circuit as UnderlyingCircuit};
pub(crate) use generalized_bulletproofs_circuit_abstraction::Transcript;

use crate::gadgets::*;

/// A struct representing a circuit.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) struct Circuit<C: Ciphersuite>(pub(crate) UnderlyingCircuit<C>);

impl<C: Ciphersuite> Circuit<C> {
  pub(crate) fn muls(&self) -> usize {
    self.0.muls()
  }

  #[allow(clippy::type_complexity)]
  pub(crate) fn prove(commitments: Vec<PedersenVectorCommitment<C>>) -> Self {
    Self(UnderlyingCircuit::prove(commitments, vec![]))
  }

  pub(crate) fn verify() -> Self {
    Self(UnderlyingCircuit::verify())
  }

  pub(crate) fn eval(&self, lincomb: &LinComb<C::F>) -> Option<C::F> {
    self.0.eval(lincomb)
  }

  pub(crate) fn mul(
    &mut self,
    a: Option<LinComb<C::F>>,
    b: Option<LinComb<C::F>>,
    witness: Option<(C::F, C::F)>,
  ) -> (Variable, Variable, Variable) {
    self.0.mul(a, b, witness)
  }

  pub(crate) fn constrain_equal_to_zero(&mut self, lincomb: LinComb<C::F>) {
    self.0.constrain_equal_to_zero(lincomb)
  }

  #[allow(clippy::too_many_arguments)]
  pub(crate) fn first_layer<T: Transcript>(
    &mut self,
    transcript: &mut T,
    curve: &CurveSpec<C::F>,

    T_table: &[(C::F, C::F)],
    U_table: &[(C::F, C::F)],
    V_table: &[(C::F, C::F)],
    G_table: &[(C::F, C::F)],

    O_tilde: (C::F, C::F),
    o_blind: ClaimedPointWithDlog,
    O: (Variable, Variable),

    I_tilde: (C::F, C::F),
    i_blind_u: ClaimedPointWithDlog,
    I: (Variable, Variable),

    R: (C::F, C::F),
    i_blind_v: ClaimedPointWithDlog,
    i_blind_blind: ClaimedPointWithDlog,

    C_tilde: (C::F, C::F),
    c_blind: ClaimedPointWithDlog,
    C: (Variable, Variable),

    branch: Vec<Vec<Variable>>,
  ) {
    let (challenge, challenged_generators) = self.discrete_log_challenges(
      transcript,
      curve,
      // Assumes all blinds have the same size divisor, which is true
      1 + o_blind.divisor.x_from_power_of_2.len(),
      o_blind.divisor.yx.len(),
      &[T_table, U_table, V_table, G_table],
    );
    let mut challenged_generators = challenged_generators.into_iter();
    let challenged_T = challenged_generators.next().unwrap();
    let challenged_U = challenged_generators.next().unwrap();
    let challenged_V = challenged_generators.next().unwrap();
    let challenged_G = challenged_generators.next().unwrap();

    let O = self.on_curve(curve, O);
    let o_blind = self.discrete_log(curve, o_blind, &challenge, &challenged_T);
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
    let i_blind_u = self.discrete_log(curve, i_blind_u, &challenge, &challenged_U);
    self.incomplete_add_pub(I_tilde, i_blind_u, I);

    let i_blind_v = self.discrete_log(curve, i_blind_v, &challenge, &challenged_V);
    let i_blind_blind = self.discrete_log(curve, i_blind_blind, &challenge, &challenged_T);
    self.incomplete_add_pub(R, i_blind_v, i_blind_blind);

    let C = self.on_curve(curve, C);
    let c_blind = self.discrete_log(curve, c_blind, &challenge, &challenged_G);
    self.incomplete_add_pub(C_tilde, c_blind, C);

    self.tuple_member_of_list(transcript, vec![O.x, I.x, C.x], branch);
  }

  pub(crate) fn additional_layer_discrete_log_challenge<T: Transcript>(
    &self,
    transcript: &mut T,
    curve: &CurveSpec<C::F>,
    divisor_x_len: usize,
    divisor_yx_len: usize,
    H_table: &[(C::F, C::F)],
  ) -> (DiscreteLogChallenge<C::F>, Vec<C::F>) {
    let (challenge, mut challenged_generator) =
      self.discrete_log_challenges(transcript, curve, divisor_x_len, divisor_yx_len, &[H_table]);
    (challenge, challenged_generator.remove(0))
  }

  pub(crate) fn additional_layer(
    &mut self,
    curve: &CurveSpec<C::F>,
    discrete_log_challenge: &(DiscreteLogChallenge<C::F>, Vec<C::F>),
    blinded_hash: (C::F, C::F),
    blind: ClaimedPointWithDlog,
    hash: (Variable, Variable),
    branch: Vec<Variable>,
  ) {
    let (challenge, challenged_generator) = discrete_log_challenge;
    let blind = self.discrete_log(curve, blind, challenge, challenged_generator);
    let hash = self.on_curve(curve, hash);
    self.incomplete_add_pub(blinded_hash, blind, hash);
    self.member_of_list(hash.x.into(), branch.into_iter().map(Into::into).collect::<Vec<_>>());
  }

  #[allow(clippy::type_complexity)]
  pub(crate) fn statement(
    self,
    generators: ProofGenerators<'_, C>,
    commitments: Commitments<C>,
  ) -> Result<(ArithmeticCircuitStatement<'_, C>, Option<ArithmeticCircuitWitness<C>>), AcError> {
    self.0.statement(generators, commitments)
  }
}
