# QROM security of leanSPHINCS

This project proves leanSPHINCS strongly unforgeable in the quantum random-oracle model (QROM), with Keccak-256 modelled as a random function that the adversary queries in superposition. It is a proof step beside the classical one (`lean_sphincs/FORS`, `FORS.Lifetimes.h26_layered_adversary`), not an end statement: `formal/statement.tex` keeps quantum security out of what is proved, since the end statements are in the random-permutation model. It builds on VCVio's quantum layer (compressed oracle, instability, square-root hybrid).

## Done

- `Qrom.qrom_search_le`: a `t`-query program outputting `k` inputs finds one whose value is good with probability at most `λ (√6 t + 2k)²`, where every input has a fraction at most `λ` of good values. Database event bound (`EventBound`), the check on `H` read on the compressed database (`Bridge`), the one-cell bound (`Cell`), cell-wise operators (`PiKron`), the assembly (`Search`, `Leaf`, `QromSearch`).

## Plan

The adversary is a program with `q` calls to the hash and `q_s` classical signing requests; the signer and key generation hash classically through the same random function.

1. **Oracle with overrides and side ports.** Generalize the search bound to runtimes whose hash port answers some inputs from fixed data (depending on a classical side state) and the rest from the random function `G`, beside classical side ports such as the signing oracle. The event bound counts every call, so the bound becomes `λ (√(6 (t + u) t) + 2k)²` with `u` side calls.
2. **Presampling.** The honest computation (key generation, every signature of every message, the randomizers and digests) reads the random function at distinct points chosen adaptively; its answers are uniform and independent of the function elsewhere. So the game equals one where the honest values are fixed data and the hash is the override of a fresh `G` by that data.
3. **Hiding.** A square-root hybrid replaces the hash by `G` at the points whose inputs carry values the adversary has not seen (`SK.seed`, `SK.prf`, chain values below the signed digit, FORS secrets at uncovered indices, and the digest points of messages not yet signed). Those values are independent of the adversary's view, so each call puts mass at most `2^-128` on them.
4. **Deferred digests.** After the hybrid, the digest of the `i`-th signed message is used only when it is signed, so it can be presampled as `δ_i`, which fixes the FORS cover set in advance.
5. **Classification.** The classical proof's Level A classification (`FORS.Classification`, a statement about any total function and the verifier's trace) shows that an accepted fresh forgery makes the verifier read, at an input answered by `G`, a value equal to the honest value at that tweak or a digest covered by the presampled digests.
6. **Bound.** The search bound of step 1, with `λ` the larger of `2^-128` and the cover probability, averaged over the data; plus the hybrid cost of step 3 and the guessing terms.
