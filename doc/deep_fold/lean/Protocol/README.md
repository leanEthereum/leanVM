# Protocol: the lemmas around the DEEP fold round

The library `Protocol` of the Lake project in the parent directory. It imports `DeepFold` and adds the lemmas the round-by-round theorem needs around the fold round: pinning (Lemma 4.11 of the paper), the potential for points reused across the fold rounds of a level, for one batch and for a schedule (Lemma 4.12), goodness of points and the error of the point message (row M0 of Theorem 5.2), the exponent maps `e_j` of Definition 4.1, and the arithmetic of the parameter claims at level 0 (Proposition 7.1). The per-message transitions and the extractor step are the library `Rounds`. The project's `README.md` has the conventions, the notation and the build.

For one batch the potential of `Level.lean` has the indicator of the exceptional set where equation (8) of the paper has the triple count over its threshold: a smaller potential with the same two bounds. `Ladder.lean` has the form of equation (8).

## Files

| file | content | in the paper |
| --- | --- | --- |
| `Potential.lean` | `avg`, `dens` (mean and probability under a uniform distribution on a finite type), Markov, Fubini; the abstract potential `pot` with `pot_step` and `pot_eq_sum`; the potential of one batch abstractly: `potT`, `potT_step`, `potT_init`, `potT_init_const`, `potT_eq_sum`, `probBad_eq_card` | Lemma 4.12 in abstract form |
| `Lists.lean` | `agrW`, `listW` (the finite set `List(O; A, d)`), `foldPair`, and the link with `DeepFold.fullT`: `mem_fullT_iff_mem_listW`, `card_fullT_fiber`, `fullT_fiber_le` | Definition 2.1 (lists) and its link with Definition 4.5 |
| `Pinning.lean` | `NonSep`, `card_nonSep_le`, `dens_nonSep_le`, `lemmaP`, `pinned_unique`, `card_pinned_le_one` | Lemma 4.11 |
| `Level.lean` | the lanes `Lane r`, the exponents `exL` with `exL_injective`, `exL_add_le`, `evL_exL_halves`; words, `half₀`, `half₁`, `foldW`; the potential of a level: `excW`, `levelPot`, `levelPot_step`, `levelPot_init`, `levelPot_eq_sum_card`; goodness of points: `Good`, `dens_not_good_le`; `listBound_level` | Definition 4.1 (the exponents `e_j`); (E2) of Lemma 4.4 and the bound behind (E4) for `e_j`; Lemma 4.12 and row M0 of Theorem 5.2 for one batch; Hypothesis 5.1 in its stated and diagonal forms |
| `Ladder.lean` | `potS`, `potS_step`, `potS_init` abstractly; for a level `NcountL`, `ladderCost`, `ladderPot`, `ladderPot_step`, `ladderPot_init`, `GoodS`, `dens_not_goodS_le` | Lemma 4.12 and row M0 of Theorem 5.2 for a schedule |
| `Params.lean` | the numbers at level 0: `point_error_level0_arith`, `point_error_level0_arith_11`, `ladder_error_level0_arith`, `fold_error_arith`, `fold_error_last_arith`, and the deployed statements `level0_point_error`, `level0_ladder_error` | Proposition 7.1 |
| `Axioms.lean` | the axiom checks and the instantiation at `GF(2^128)` | |

## Conventions

- A state of a level is indexed by `k`, the number of fold rounds played, and `r`, the number still to come. A word with `r` lane variables is `Word K r = K → Lane r → K`, with `Lane (r + 1) = Lane r ⊕ Lane r`; the first summand is the half `O₀` (folded variable equal to 0), as in `DeepFold.evL_halves` and in `Rounds`. `foldW O c` is `O₁ + (α + β x) O₀`.
- `exL k r` is the exponent map `e_k` of Definition 4.1 on `r` lane variables, and `thr k` the agreement threshold of the lists of the words folded `k` times. The exceptional set of the round played from a word `O` folded `k` times is `ExcL (fullT D (half₀ O) (half₁ O) d (thr (k + 1))) (exL (k + 1) r) s B`, the form `DeepFold.lemmaF_round` takes with `B = K₀ (K₀ - 1) (K₀ - M)`.
- Probabilities are `dens p`, the number of elements satisfying `p` over the size of the type, in `ℚ`. `dens_mem` turns it into the form `card / Fintype.card` that `DeepFold` uses.
- The potential is a function of the current word and the points only. The prover's messages are not among its arguments, and the next word is `foldW O c`, a function of the word and the challenge.
