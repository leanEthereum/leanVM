# SPHINCS security in Lean 4

[Scheme.lean](SphincsSecurity/Scheme.lean) defines the scheme with a 32-byte master seed: parameters, serialized hash inputs, key generation, signing, and verification. [Statement.lean](SphincsSecurity/Statement.lean) imports it and defines the SUF-CMA game, hash-query budget, and 127-bit security target. Public parameters, signing secrets, and signing randomizers are derived in separate hash domains. Every hash call in the experiment counts, including derivation, signing failures, repeated calls and final verification.

[Completeness.lean](SphincsSecurity/Completeness.lean) states the other side. Correctness, for every hash function: a signature the signer produces verifies. Completeness, against the same random oracle: the sum over all messages of the probability that sampling a seed, generating a key, signing and verifying fails is at most $2^{-256}$, where failing means the signer returned no signature or the verifier rejected it. This is the union-bound budget for one key signing every message. `sphincs_is_correct` and `sphincs_is_complete` prove the two statements; [PROOF.md](PROOF.md#completeness) outlines the route.

The public adversary may use private randomness adaptively and has no running-time or memory bound. The probability is over the master seed, the shared consistent random oracle and the adversary's private randomness. Private sampling does not count toward the hash-query budget. [Proof/Adversary](SphincsSecurity/Proof/Adversary) identifies this game with the internal probabilistic game, preserving success probabilities and query counts exactly.

The theorem `sphincs_has_127_bits_of_classical_security` proves this claim for at most `2^32` signing requests per key. The reduction in [Proof/Deterministic](SphincsSecurity/Proof/Deterministic) couples seed derivation to independent secrets and signing trials, handles repeated requests, bounds adaptive seed guesses, and transfers the query budget. The public-parameter derivation consumes a query, leaving enough slack to absorb the seed-guessing loss without weakening the 127-bit bound.

## Build and audit

Use the pinned Lean toolchain and VCVio revision:

```sh
cd formal/sphincs
lake exe cache get
lake build
```

The cache command is needed on initial setup. The root module pins the axiom footprint of every theorem to `propext`, `Classical.choice` and `Quot.sound` with `#guard_msgs`, so the build fails if it ever grows. [scripts/Reach.lean](scripts/Reach.lean) is a maintenance script: `lake env lean scripts/Reach.lean` writes `reach.txt`, listing every local declaration with the line range of its source block and whether the proof terms of the public theorems reach it, which is how dead code is found before pruning.

## Where to work

[PROOF.md](PROOF.md) explains the route, the constants, the component facades that seal each component's parameters, and which modules must change if a component changes. The proof is split by component:

| Entry | Purpose |
| --- | --- |
| [SphincsSecurity.lean](SphincsSecurity.lean) | The public theorems. |
| [Completeness](SphincsSecurity/Completeness) | Correctness and completeness: recovery, the reduction of failure to signing returning `none`, and the bounds on signing's six searches. |
| [Proof/Deterministic](SphincsSecurity/Proof/Deterministic) | Seed derivation, coupling to independent secrets, and the final security bound. |
| [Proof/Security127Completion.lean](SphincsSecurity/Proof/Security127Completion.lean) | Combines the large-budget and small-budget bounds into `security127`. |
| [Proof/Base](SphincsSecurity/Proof/Base) | Scheme-independent tooling: uniform tables and their exact adaptive posteriors, query caps, pauses and traces, oracle query charges, moment bounds. |
| [Proof/Scheme](SphincsSecurity/Proof/Scheme) | The concrete game over a query cache, honest computation and witness extraction from an accepting signature. |
| [Proof/Hypertree](SphincsSecurity/Proof/Hypertree) | The canonical graph of honest hash inputs, frontier oracles, structural matches, layer and hypertree witnesses. |
| [Proof/Chains](SphincsSecurity/Proof/Chains) | Abstract chain tables and their adaptive query bounds, independent of the scheme. |
| [Proof/Ots](SphincsSecurity/Proof/Ots) | The one-time signature: prefix simulation, contacts, encoding neighbors, markers and matches on the concrete chains, the OTS verifier witness. |
| [Proof/Fts](SphincsSecurity/Proof/Fts) | The few-time signature and message digest: target certificates, the banked monitor, proposal words, the terminal certificate price, cache exceptions. |
| [Proof/Reference](SphincsSecurity/Proof/Reference) | The reference experiment: sampled reference family, forgery source, verifier classification, primitive-event union, query allocation, certificate coverage. |
| [Proof/Residual](SphincsSecurity/Proof/Residual) | The retained residual monitor on the original game and the large-budget theorem. |
| [Proof/Forced](SphincsSecurity/Proof/Forced) | The secret-guess interpreter, the forced FTS games, their monitored runs and the small-budget arithmetic. |

Superseded proof routes and their planning notes are in the Git history.
