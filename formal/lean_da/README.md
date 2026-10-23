# LeanDA security in Lean 4

**Credit: the security framework and its proofs are Benedikt Wagner's**, from [b-wagn/fv-pq-da](https://github.com/b-wagn/fv-pq-da) at `4475179c`, explained in his post [Formally verified security for PQ-DAS (LeanDA)](https://ethresear.ch/t/formally-verified-security-for-pq-das-leanda/25746).

**[LeanDa.lean](LeanDa.lean) proves that LeanDA, the erasure code commitment of [`crates/lean_da`](../../crates/lean_da) specified in `doc/leanvm` §sec:leanda, is complete, position binding and code binding, for every number of rows, assuming a knowledge-sound argument for its relation.** The proofs of the generic construction are Benedikt Wagner's, ported here as the library `PqDas`; this project instantiates them with LeanDA and proves the building blocks they assume. The root module pins the axioms of every front-page theorem to `propext`, `Classical.choice` and `Quot.sound` with `#guard_msgs`. There is no `sorry` and no `native_decide`.

## Theorems

For `r` rows, any hash `H` (the crate's is BLAKE2s-256), an argument `ps` for `Relation r H` and its extractor `ext`:

| Theorem | Statement |
| --- | --- |
| `leanDa_perfectlyComplete` | if `ps` is perfectly complete, every honest opening of an honest commitment verifies |
| `leanDa_positionBinding` | `Pr[position binding] ≤ Pr[collision of H]` for the explicit reduction `merkleCollider r H (posBindingReduction ps A)` |
| `leanDa_codeBinding` | `(Pr[code binding] - (ε_ks + ε₁))² ≤ (Q + 2) (ε₂ + 14 / 2^192 + 2^-2688)` for an adversary making at most `Q` random-oracle queries |

In the code-binding bound `ε_ks` is the success of the reduction `ksReduction` against the knowledge soundness of `ps`, and `ε₁`, `ε₂` are the successes of two explicit reductions finding collisions of `H`. `14 / 2^192` is the membership test's soundness and `2^2688 = |E|^14` the number of its challenges.

They rest on what this project proves about LeanDA's building blocks ([LeanDa/Security.lean](LeanDa/Security.lean)):

* `checker_complete`, `checker_sound`: the membership test accepts every codeword for every challenge, and a fixed matrix that is not a codeword for at most a `14 / 2^192` fraction of the challenges `z ∈ E^14`. This is Proposition prop:rs-membership of `doc/leanvm` Annex D: the additive Reed-Solomon code at rate one half is its own dual on the crate's domain (`orthogonal_rsCode`, by Lemma lem:domain-sum and Corollary cor:rs-dual), the dual codeword is the encoding of the tensor `⊗_j (1, z_j)` in the novel basis (`dual_eq_sum`), and the inner product with a row that is not a codeword is a nonzero multilinear polynomial of total degree at most 14 in `z`, so Schwartz-Zippel applies (`card_acceptSet_le`).
* `merkleVC_perfectlyComplete`, `posBindingExp_le_hashCollisionExp`: honest cell openings verify, and two openings of one cell to different values give a collision of the hash, which `merkleCollider` computes. Both hold for every hash function, as do the theorems.

## Assumptions

* **An argument of knowledge** for `Relation r`, the statement that the cells commit to the root and pass the membership test on the challenges: perfect completeness for `leanDa_perfectlyComplete`, and straightline knowledge soundness through `ε_ks`. Wagner's model of the argument makes no oracle queries. Discharging this assumption with leanVM, the aggregation guest proving the relation, is not done here: its own Fiat-Shamir transcript will need to be domain separated from the challenge oracle below.
* **Collision resistance of the hash**, through the explicit reductions. The theorems hold for every hash function `H`, so they are reductions, not bounds; LeanDA's is BLAKE2s, which `formal/lean_vm` defines and checks against the Rust (`LeanVM.Da.blake2s`).
* **The random-oracle model for the challenges.** The crate derives `z` with a BLAKE2s chain from the label `leanDA/rs-membership/v1` over the root (`membership_challenges`); the security game models this as one random oracle from roots to `E^14`.

## The model and the Rust code

[LeanDa/Scheme.lean](LeanDa/Scheme.lean) is the scheme, citing the crate at leanVM `b64b3d41f`. It is checked by reading both sides; it is not a mechanized refinement of the Rust.

* **The code.** A row's `2^14` payload symbols are the values of a polynomial of degree below `2^14` on the domain points `0 … 2^14 - 1` (the element of `K` whose bits are `b` is point `b`, the span of `e_c = x^c`), and its codeword is that polynomial's values on the `2^15` points. The crate computes these maps with the inverse and forward additive NTT; the model uses the maps themselves, so the NTT's correctness (Annex D, Proposition prop:ntt) is not mechanized here. Likewise the dual codeword is `∏_j (1 + z_j Ŵ_j(x))`, which `dual_eq_sum` shows is the encoding of the tensor that `dual_codeword` transforms.
* **The matrix.** The row count `r` is a parameter; the crate accepts `1 ≤ r ≤ 1024` and the theorems hold for every `r ≥ 1`. The erasure code's positions are the `128 r` cells of the `r` rows, the cells sampling opens. The commitment pads the rows to `2^⌈log₂ r⌉` with zero codewords and hashes the padded matrix, as `commit_codewords` does.
* **Openings.** The crate keeps the column tree for answering samples but verifies none. An opening is modelled as the cell's path in the column tree, of the tree's height, with the row root; it verifies when the path climbs to a column root that hashed after the row root gives the commitment.
* **The deployed algorithms.** `Scheme.lean` also transcribes, computably on lists, the crate's commitment (`commitCodewords`, each tree built level by level), the challenges' BLAKE2s chain (`membershipChallenges`), the membership vector by the additive NTT (`membershipVector`, `verifier/src/da.rs`) and its digest (`vectorDigest`). [LeanDa/Commitment.lean](LeanDa/Commitment.lean) proves the commitment is the model's: for every hash `H` and codewords of `2^15` symbols, `commitCodewords H rows = commitCells H (cellsOfRows rows)` (`commitCodewords_eq_commitCells`). That `membershipVector` computes the model's `dual` at the challenges, the NTT's correctness, is not proved; it is a follow-up.

`formal/lean_vm` imports `LeanDa/Scheme.lean` by path and states the aggregation node's DA claim with these definitions, on its own BLAKE2s (`formal/lean_vm/LeanVM/Spec/Da.lean`); its node vectors check `commitCodewords` and the membership vector's digest against the crate's. So `Scheme.lean` and `Field.lean` stay Lean modules, building on both projects.

## Build

```sh
cd formal/lean_da
lake exe cache get
lake build
```

## Libraries

| Library | What it is |
| --- | --- |
| [PqDas](PqDas) | Wagner's framework and proofs: erasure codes, vector commitments, code checkers, arguments of knowledge, the scheme, and its completeness, position binding and code binding (the latter through a forking argument). Ported from [b-wagn/fv-pq-da](https://github.com/b-wagn/fv-pq-da/tree/4475179c19296acf3469d7d552a3186ad1feda74) at `4475179c` to the VCVio and Lean pinned here; [NOTICE](NOTICE) says what changed. Apache-2.0, see [LICENSE](LICENSE). |
| [LeanDa](LeanDa) | LeanDA: the fields, the scheme and its deployed algorithms, the self-duality of the code, the membership test's soundness, the Merkle commitment and the deployed one's agreement with it, and the instantiation. |
