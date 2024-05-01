# Full-Chain Membership Proofs

An implementation of the membership proof from
[FCMP++](https://github.com/kayabaNerve/fcmp-ringct/blob/develop/fcmp%2B%2B.pdf),
which inputs a re-randomized key, re-randomized linking tag generator, a
Pedersen commitment to the linking tag generator, and an amount commitment
before verifying there is a known de-re-randomization for a member of a Merkle
tree.
