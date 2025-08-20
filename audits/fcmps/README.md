# Full-chain Membership Proofs

The `crypto/fcmps` folder, comprehensively to
`crypto/fcmps/circuit-abstraction`
(`generalized-bulletproofs-circuit-abstraction`),
`crypto/fcmps/ec-gadgets` (`generalized-bulletproofs-ec-gadgets`), and
`crypto/fcmps` (`full-chain-membership-proofs`) itself, was
[audited by Veridise](
  https://veridise.com/audits-archive/company/monero-research-lab/magic-grants-monero-fcmp-2025-06-03
).

The non-interactive gadgets were formally verified via
[Picus](https://github.com/veridise/picus), after Veridise wrote a
[translation layer](
  https://github.com/Veridise/fcmp-plus-plus/tree/picus/crypto/fcmps/circuit-abstraction
) from our circuit abstraction to Picus.

The interactive gadgets had security proofs written (please refer to the audit
itself and also [here](../divisors)).
