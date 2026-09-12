# XMSS security formalization

[Statement.lean](XmssSecurity/Statement.lean) contains the complete scheme with a 32-byte master seed: parameters, serialized hash inputs, key generation, signing, verification, the consistent random-oracle game, and the 127-bit security target. Public parameters and WOTS secrets are derived in separate hash domains. Key generation computes the chain and tree tables; signing reads them and hashes only for message encoding.

The theorem `xmss_has_127_bits_of_classical_security` proves this claim. The reduction in [Proof/Seeded](XmssSecurity/Proof/Seeded) couples seed derivation to the independent-secret model, bounds adaptive seed guesses, and transfers the consistent-oracle query budget. The public-parameter derivation consumes a query, leaving enough slack to absorb the seed-guessing loss without weakening the 127-bit bound.

The adversary has access to the shared random oracle and a signing oracle. Signing responses are logged. Reusing a signing epoch invalidates the transcript, and the strong-forgery check rejects only an exact replay for the claimed message and epoch. The query bound applies to every execution of the consistent random oracle and covers the entire experiment, including key generation, adversarial queries, signing, repeated hash calls, and final verification.

The theorem covers full-tree key generation and at most `2^23` encoding attempts per signing request. Rust also supports restricted epoch ranges and currently retries encoding without a cap; those variants are outside this statement.

The theorem's axiom footprint is limited to Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. It contains no `sorryAx` or compiler-evaluation axiom. The root module pins this footprint with `#guard_msgs`, so the build fails if it ever grows.

The main proof spine is organized by mathematical stage: `CappedGlobalKeygen` constructs the presampled key-generation view, `CappedGlobalTreeCacheCorrespondence` fixes the WOTS endpoint tables once and couples all tree hashes under one cache invariant, `CappedGlobalCausalSetup` couples the result to signing and the causal experiment, `CappedGlobalChainOutputUniformity` samples the complete chain-output table, the five `CappedGlobalChainHigh*` modules establish setup, local coupling, replay, whole-game coverage, and reduction, and the four first-lane modules establish the experiment, source coupling, transport reduction, and final bound.

Build with:

```bash
lake build
```
