# QROM security of leanSPHINCS

This project proves leanSPHINCS strongly unforgeable in the quantum random-oracle model (QROM), with Keccak-256 modelled as a random function that the adversary queries in superposition. It is a proof step beside the classical one (`lean_sphincs/FORS`, `FORS.Lifetimes.h26_layered_adversary`), not an end statement: `formal/statement.tex` keeps quantum security out of what is proved, since the end statements are in the random-permutation model. It builds on VCVio's quantum layer (compressed oracle, instability, square-root hybrid).

## Done

- `Qrom.qrom_search_le`: a `t`-query program outputting `k` inputs finds one whose value is good with probability at most `λ (√6 t + 2k)²`, where every input has a fraction at most `λ` of good values. Database event bound (`EventBound`), the check on `H` read on the compressed database (`Bridge`), the one-cell bound (`Cell`), cell-wise operators (`PiKron`), the assembly (`Search`, `Leaf`, `QromSearch`).
- `Qrom.OvGame.ov_search_le`: the same bound for games whose hash answers some inputs from fixed data, depending on a classical side state, beside classical side ports such as a signing oracle, with `t` the number of calls in all (`Override`, `OvBridge`, `OvEvent`, `OvSearch`).
- `Qrom.OvGame.hiding_le`: replacing the hash by `G` on the inputs that carry data not yet revealed costs `√Pr₁ ≤ √Pr₂ + n √(4 ε tr ρ)`, when at most a fraction `ε` of the unrevealed values protect any input (`Blocks`, `OvBlocks`, `Hiding`, `HidingAvg`, `HidingMain`). Two games that agree on a set of side states closed under predecessors run every program to the same joint states and query weights there.

## Plan

The adversary is a program with `q` calls to the hash and `q_s` classical signing requests; the signer and key generation hash classically through the same random function. Events are read on each block of the side register (the signing log), so the game's win condition, which reads the log, is an event of the leaves and the side state.

1. **Side-aware events.** Extend `hiding_le` to events of the leaf and the side state (the square-root hybrid takes any contraction on the leaves), bound the probability that the verifier reads a protected input at the final side state by `k ε`, and presample the signer's digests: on the side state `s` the run reads the digests of the signed messages only, so averaging over them is averaging over the first `|s|` presampled digests.
2. **Presampling.** The honest computation (key generation, every signature of every message, the randomizers and digests) reads the random function at distinct points chosen adaptively; its answers are uniform and independent of the function elsewhere. So the game equals one where the honest values are fixed data and the hash is the override of a fresh `G` by that data.
3. **The game.** `SK.seed`, `SK.prf`, the chain values below the signed digit, the FORS secrets at uncovered indices and the randomizers of unsigned messages are hidden; the inputs that carry them are protected, each with probability at most `2^-128` over the hidden value.
4. **Classification.** The classical proof's Level A classification (`FORS.Classification`, a statement about any total function and the verifier's trace), applied to the fully overridden hash, shows that an accepted fresh forgery whose verification reads no protected input makes the verifier read, at an input answered by `G`, a value equal to the honest value at that tweak or a digest covered by the presampled digests.
5. **Bound.** `ov_search_le` with `λ` the larger of `2^-128` and the cover probability, averaged over the data, plus the hiding and protected-read terms.
