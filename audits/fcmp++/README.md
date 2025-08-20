# FCMP++

The FCMP++ protocol upgrade for Monero has a long history, with a scattered
record of documents. The protocol originally evolved from
"Full-Chain Membership Proofs" (FCMPs) for
[Seraphis](https://github.com/UkoeHB/Seraphis). Seraphis was a new privacy
protocol Monero was working on upgrading to which would've replaced the ring
signatures present with one Membership proof and one
Spend-Authorization + Linkability proof.

In response to a spam attack occurring on the Monero network, which impacted
users' privacy, the idea was thrown out to implement FCMPs before Seraphis (in
what evolved to the FCMP++ protocol). This was first presented in a
[GitHub Gist](
  https://gist.github.com/kayabaNerve/0e1f7719e5797c826b87249f21ab6f86
).

The idea was discussed extensively throughout the Monero community, including
on the [GitHub issue to implement full-set membership proofs](
  https://github.com/monero-project/research-lab/issues/100
).

The [FCMP++ paper](https://github.com/kayabaNerve/fcmp-plus-plus-paper)
conclusively defined a reference document for the FCMP++ protocol upgrade for
Monero.

[This Python script](
  https://gist.github.com/kayabaNerve/e09ba62d4a6165ced006b037f1068d95  
) demonstrated that from an input tuple and
Spend-Authorization and Linkability proof, an adversary who can solve the
discrete-logarithm problem could find an opening for any output, therefore
proving the composition's forward-secrecy against a quantum computer.

[Cypher Stack reviewed the composition presented](
  https://github.com/cypherstack/fcmp-review
), providing security proofs for the Spend-Authorization + Linkability proof.
