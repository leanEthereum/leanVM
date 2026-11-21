# Rounds: the transitions of the round-by-round theorem and the extractor step

The library `Rounds` of the Lake project in the parent directory. It states and proves the per-message transitions M1 to M5 of Theorem 5.2 of the paper (Section 5.4) in the relativised form that Theorem 5.6 needs, and one step of the descent of Theorem 5.6 (Section 5.5). It is built on `DeepFold` (Lemma 4.10) and, in one file, on `Protocol` (Lemma 4.11). The transition M0 is in `Protocol`, and the composition over a run in `Soundness`. The project's `README.md` has the conventions, the notation and the build.

## Shape of a statement

A state is `Doomed D O d A ex z v W σ B`: no tuple of `List(O; A, d)` with `B` satisfies the running claim `(W, σ)` and all carried point claims `(z_m, v_m)`. This is the invariant `(I_{i,j})` of Section 5.3 for `B` true and the relativised `(I^B_{i,j})` of Definition 5.4 in general. `Doomed₁` is the same at the end of a level, where the fold is one lane and a point claim is a plain evaluation. A transition says: if the state before a verifier message is doomed, the set of messages after which the state is not doomed has at most so many elements. Each has a density form with the error of Theorem 5.2.

## Files

| file | content | in the paper |
| --- | --- | --- |
| `Basic.lean` | `agr`, `InList`, `NearT`, `foldWord`, `foldTuple`, `pull`, `foldWeight`, `foldClaim`, `foldVal`, `exHalves`, `Doomed`, and the links with `agrL`, `agrPairL` of `DeepFold` | Definition 2.2; Definition 5.4; the conditions `(I_{i,j})` and `(I^B_{i,j})` of Sections 5.3 and 5.5; the updates (1) and (4) |
| `Fold.lean` | `fold_transition` (M2, relativised), `fold_transition_plain` (M2, `B` true), `fold_transition_density` (`(K₀ - 1)/q^2`) | transition M2 |
| `Batch.lean` | `card_powsum_zero_le`, `card_batch_zero_le` (root counts), `batch_transition` (M1, relativised), `batch_transition_density` (`(J - 1)/q`), `k2_hfalse` (the predicate of Corollary 5.7 satisfies the hypothesis of Theorem 5.6) | transition M1; the predicate of Corollary 5.7 |
| `Query.lean` | `card_queries_agree_le`, `density_queries_agree_le` (`((A - 1)/n)^t`), `card_batch3_zero_le`, `Doomed₁`, `Doomed.one_lane`, `nextW`, `nextC`, `query_transition` (M3, relativised), `query_transition_density` (`((A - 1)/n)^t + (s + t)/q`) | transition M3, with the conversion (5) |
| `Final.lean` | `final_transition` (M4, relativised: the conclusion of Theorem 5.6 for an accepting run), `final_transition_plain`, `final_transition_density`, `tail_round_transition` (M5), `tail_round_transition_density` (`2/q`) | transitions M4 and M5 |
| `Extract.lean` | `nearT_unique`, `NearT.inList`, `NearT.fold_eq`, `NearT.degree_lt`, `descent_step`, `existsUnique_nearT` | Lemma 5.5; the descent step of Theorem 5.6 |
| `Pinned.lean` | `sep_of_not_mem_nonSep`, `batch_transition_pinned`, `query_transition_pinned`: M1 and M3 with the separation hypothesis replaced by `z ∉ Protocol.NonSep (Protocol.listW ...)`, the conclusion of Lemma 4.11 | transitions M1 and M3 with the separation hypothesis taken from Lemma 4.11 |
| `Axioms.lean` | the axiom checks and the instantiations at `GF(2^128)` | |

`Pinned.lean` imports `Protocol.Pinning`, so building this library also compiles `Protocol/Lists.lean`, `Protocol/Potential.lean` and `Protocol/Pinning.lean`.
