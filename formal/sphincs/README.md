# SPHINCS security in Lean 4

The public theorem proves **127 bits of classical strong unforgeability in the random-oracle model** for the concrete SPHINCS instance of `doc/sphincs`, with at most `2^24` signing requests per key pair: every adversary whose whole experiment makes at most $q\ge1$ hash queries forges with probability at most $q/2^{127}$.

[Statement.lean](SphincsSecurity/Statement.lean) defines the concrete parameters, serialized hash inputs, algorithms, the SUF game and the claim. The claim uses independently sampled secret leaves and a random oracle; instantiating that oracle with BLAKE2s or deriving all secrets from a seed is outside this theorem. The whole-experiment query budget bounds every execution of the consistent random oracle and includes key generation, signing failures, repeated calls and final verification.

## Build and audit

Use the pinned Lean toolchain and VCVio revision:

```sh
cd formal/sphincs
lake exe cache get
lake build
```

The cache command is needed on initial setup. The root module pins the axiom footprint of the theorem to `propext`, `Classical.choice` and `Quot.sound` with `#guard_msgs`, so the build fails if it ever grows. [scripts/Reach.lean](scripts/Reach.lean) is a maintenance script: `lake env lean scripts/Reach.lean` writes `reach.txt`, listing every local declaration with the line range of its source block and whether the proof terms of the public theorem reach it, which is how dead code is found before pruning.

## Where to work

[PROOF.md](PROOF.md) explains the route, the constants, the component dependencies of every directory and which modules must change if the one-time signature changes. The proof is split by component:

| Entry | Purpose |
| --- | --- |
| [SphincsSecurity.lean](SphincsSecurity.lean) | The public theorem. |
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
