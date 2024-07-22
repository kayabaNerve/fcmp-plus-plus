use ciphersuite::Ciphersuite;

pub(crate) use generalized_bulletproofs_ec_gadgets::*;

use crate::*;

impl<C: Ciphersuite> Circuit<C> {
  pub(crate) fn tuple_member_of_list<T: Transcript>(
    &mut self,
    transcript: &mut T,
    member: Vec<Variable>,
    list: Vec<Vec<Variable>>,
  ) {
    // Ensure this is being safely called
    for variable in member.iter().chain(list.iter().flatten()) {
      assert!(
        matches!(variable, Variable::CG { .. }) || matches!(variable, Variable::CH { .. }),
        "tuple member of set requires all arguments belong to vector commitments"
      );
    }

    // Create challenges which we use to aggregate tuples into LinCombs
    let mut challenges: Vec<C::F> = vec![];
    for _ in 0 .. member.len() {
      challenges.push(transcript.challenge());
    }

    // Aggregate the claimed member
    let member = {
      let mut res = LinComb::empty();
      for (i, member) in member.into_iter().enumerate() {
        res = res + &(LinComb::from(member) * challenges[i]);
      }
      res
    };

    // Aggregate the list members
    let list = {
      let mut res = vec![];
      for list_tuple in list {
        let mut item = LinComb::empty();
        for (i, list_member) in list_tuple.into_iter().enumerate() {
          item = item + &(LinComb::from(list_member) * challenges[i]);
        }
        res.push(item);
      }
      res
    };

    // Run traditional set membership
    self.member_of_list(member, list)
  }

  #[allow(clippy::type_complexity)]
  pub(crate) fn discrete_log_challenge<T: Transcript, Parameters: DiscreteLogParameters>(
    &self,
    transcript: &mut T,
    curve: &CurveSpec<C::F>,
    generators: &[&GeneratorTable<C::F, Parameters>],
  ) -> (DiscreteLogChallenge<C::F, Parameters>, Vec<ChallengedGenerator<C::F, Parameters>>) {
    self.0.discrete_log_challenge(transcript, curve, generators)
  }

  pub(crate) fn discrete_log<Parameters: DiscreteLogParameters>(
    &mut self,
    curve: &CurveSpec<C::F>,
    point: PointWithDlog<Parameters>,
    challenge: &DiscreteLogChallenge<C::F, Parameters>,
    challenged_generator: &ChallengedGenerator<C::F, Parameters>,
  ) -> OnCurve {
    self.0.discrete_log(curve, point, challenge, challenged_generator)
  }
}
