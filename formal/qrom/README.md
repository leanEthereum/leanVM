# QROM security of leanSPHINCS

This project proves leanSPHINCS strongly unforgeable in the quantum random-oracle model (QROM), with Keccak-256 modelled as a random function that the adversary queries in superposition. It is a proof step beside the classical one (`lean_sphincs/FORS`, `FORS.Lifetimes.h26_layered_adversary`), not an end statement: `formal/statement.tex` keeps quantum security out of what is proved, since the end statements are in the random-permutation model. It builds on VCVio's quantum layer (compressed oracle, instability, square-root hybrid).

## Done

- `Qrom.qrom_search_le`: a `t`-query program outputting `k` inputs finds one whose value is good with probability at most `λ (√6 t + 2k)²`, where every input has a fraction at most `λ` of good values. Database event bound (`EventBound`), the check on `H` read on the compressed database (`Bridge`), the one-cell bound (`Cell`), cell-wise operators (`PiKron`), the assembly (`Search`, `Leaf`, `QromSearch`).
- `Qrom.OvGame.ov_search_le`: the same bound for games whose hash answers some inputs from fixed data, depending on a classical side state, beside classical side ports such as a signing oracle, with `t` the number of calls in all (`Override`, `OvBridge`, `OvEvent`, `OvSearch`).
- `Qrom.OvGame.hiding_le`: replacing the hash by `G` on the inputs that carry data not yet revealed costs `√Pr₁ ≤ √Pr₂ + n √(4 ε tr ρ)`, when at most a fraction `ε` of the unrevealed values protect any input (`Blocks`, `OvBlocks`, `Hiding`, `HidingAvg`, `HidingMain`). Two games that agree on a set of side states closed under predecessors run every program to the same joint states and query weights there.
- `Qrom.Sphincs.winProb_le`: an adversary given the public key and making at most `n` calls in all (hash queries, quantum or classical, and signing requests) forges with probability at most `(√ε_hid + (n + 1 + verifyQueries) √(4 · 2^-128 tr ρ))²`. Pinned to Lean's three standard axioms in `Qrom.lean`.

## The leanSPHINCS proof

The adversary is a program whose calls go to the hash or to the classical ports (the public key, signing); the signer and key generation hash classically through the same random function, and the signing log is the game's side state.

1. **Presampling** (`Sphincs/Presampled`): the honest computation (key generation, every signature of every message, the randomizers and digests) reads the hash at distinct points, so the game equals the average over data `d` of one whose hash is a fresh `G` overridden by `d` (`winProb_eq`).
2. **Hiding** (`Sphincs/Hidden`, `Sphincs/HidingStep`): the inputs that read unrevealed data (`SK.seed`, `SK.prf`, unsigned chain values and FORS secrets, unsigned randomizers) are answered by `G`, at a cost of `n √(4 · 2^-128 tr ρ)` on the square root.
3. **Classification** (`Sphincs/Classify`): the classical Level A classification, applied to the hidden game's hash, splits a winning forgery into a protected read, a hit of `G` on an honest value, an encoding collision of the data, or a digest from `G` covered by the logged digests (`Sphincs/Bound/Split`).
4. **Bounds** (`Sphincs/Bound`): protected reads cost `verifyQueries · 2^-128` (`Terms`), hits `2^-128 (√6 (n + 1 + verifyQueries) + 2 verifyQueries)²` (`Terms`), encoding collisions `numLayers · 2^totalHeight · 2^32 · 2^-128` (`BadEnc`). Covered digests go through the deferral of the signed digests to presampled ones (`Defer`) and a search for a first digest call output that some second output completes to a covered digest (`Cover`), costing `λ_cov (√6 (n + 1 + verifyQueries) + 2 verifyQueries)²`.

## Follow-up

- `Qrom.Sphincs.lamCov`, the probability over `signatureLimit` uniform presampled digests and a uniform first digest call output that the output is coverable, is a defined quantity, not yet bounded numerically. The search reads one cell, so the leaves the second digest call carries are free; a two-cell search would recover them.
