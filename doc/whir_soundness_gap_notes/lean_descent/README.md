# Period descent: the Lean 4 development

This directory is a Lean 4 + Mathlib development of the period descent for list sizes of Reed-Solomon codes on subspace domains in characteristic two, the conditional result of notes 37 and 39 of the parent directory in the form the referee signed (Theorem R of note 46), and of the three-wise Johnson bound of note 44. It is one Lake project, `perioddescent`, with one library `PeriodDescent` of twelve files and about 3900 lines, over Mathlib and nothing else: it does not depend on `doc/deep_fold/lean` nor on leanVM's own formal development. The report on it is `../47-lean-period-descent.md`.

"The notes" are the files of the parent directory: `04-list-bounds-beyond-johnson.md`, `37-dimension-induction.md`, `39-period-descent.md`, `44-period-conjecture-divisors.md` and `46-referee-notes-37-39.md`.

## What is proved

The end statement is `PeriodDescent.theoremR` (`PeriodDescent/TheoremR.lean`): Theorem R of note 46, section 1.5. Let `F` be a field of characteristic two, `D` a subspace of `F` with `2^N` elements, `1 ≤ k ≤ T ≤ 2^N`, `Δ = T - k + 1`, `f ≥ 2` and `j₀ ≤ N - 1`. Assume PL`(f, j₀)` (`PLsub`): for every `j < j₀`, every subspace `U ⊆ D` with `2^j` elements, every degree bound `κ ≤ ⌊(k - 1) / 2^j⌋` (`κ = k - 1` if `j = 0`) and every word `v : D → F ∪ {⊥}`, every set of more than `f` polynomials `P` of degree at most `κ` with `#{x ∈ D : v(x) = P(L_U(x))} ≥ 2^j κ + Δ` contains three distinct members whose function `(P_c - P_a) / (P_b - P_a)` is constant or unchanged by `Y ↦ Y + a'` for some nonzero `a' ∈ L_U(D)`. Then for every word `w : D → F`, the polynomials of degree `< k` that agree with `w` on at least `T` points of `D` number at most `C(f + 1, 3)^{j₀} 2^(N j₀ - j₀ (j₀ - 1) / 2) (B_{j₀} + 1)`, with `B_{j₀} = max_{0 ≤ κ ≤ ⌊(k - 1) / 2^{j₀}⌋} ∏_{i = 0}^{κ} (n - 2^{j₀} i) / (Δ + 2^{j₀} (κ - i))` (`baseB`).

| file | content | in the notes |
| --- | --- | --- |
| `Johnson3.lean` | The three-wise Johnson bound: the count over triples as `∑_x 6 h_M(d_x)` (`threewise_identity`), convexity of `h_M` at the integers (`H3_tangent`), inequality (3) in division-free form (`threewise_jensen`), the closed form cross-multiplied in `ℤ` (`threewise_johnson`) and as stated, in `ℚ` (`threewise_johnson_rat`). | note 44 Lemma 5.2 |
| `Base.lean` | The base bound by pinning one more point at each step, for any family of functions two of which never agree at `κ + 1` points of the quotient (`pinned_bound`, `list_bound_nat`); for polynomials through a map with fibres of at most `m` points, in `ℕ` and as the product in `ℚ` (`base_bound_nat`, `base_bound`); the ordinary case (`ordinary_bound`) and collinear members (`collinear_bound`). | note 37 Lemma 3.2; note 04 Theorem 1.2 for `r = k` and `r = 1` |
| `Affine.lean` | The same bound for an affine space of dimension `r` of members, by induction on `r` (`affine_bound`), with the MDS property of polynomials of degree `< k` (`finrank_add_card_common_zeros_le`, `card_common_zeros_le`): `affine_poly_bound` and `affine_ordinary_bound`. | note 04 Theorem 1.2; the proof of note 37 Lemma 3.2 as written |
| `Core.lean` | With `q = X² + a X`: every polynomial is uniquely `u₀(q) + X u₁(q)` (`exists_decomp`, `decomp_unique`); in characteristic two `P(X + a) = P + a u₁(q)`, so invariance under `X ↦ X + a` is `u₁ = 0` (`comp_shift`, `invariant_iff_part1`, `invariant_iff_exists`); `Periodic`, `rho`, and the members periodic for a pair are exactly `c₀ + ϱ Q(q)` (`periodic_iff_exists`, `periodic_triple_iff`); degrees and values (`natDegree_le_of_descent`, `agree_iff_of_ne_zero`); the symmetries (`Periodic.swap`, `Periodic.base_swap`, `periodic_of_const`). | note 37 Proposition 3.3, first half; note 46 section 1.1 and section 1.2 steps 1 to 3 |
| `Level.lean` | `IsSubspace`, the level polynomials `IsLevel` (`X`, then `ℓ² + a ℓ` for a nonzero value `a` of `ℓ` on `D`), which are the subspace polynomials `L_U` of subspaces `U ⊆ D` with `2^j` elements (`IsLevel.exists_subspace`); additivity, kernel, fibres, number of values and of directions. | note 37 Definition 3.1; `L_{U'} = q'(L_U)` in Proposition 3.3 |
| `Step.lean` | The word of the next level (`nextWord`), the agreements exactly (`polyAgr_descent_eq`, `card_zeros_le`), the slack (`slack_arith`), level problems (`LevelPb`, `LevelPb.Mem`, `LevelPb.next`), and the descent step as one statement (`LevelPb.descent_step`). | note 37 Proposition 3.3, second half; note 46 section 1.2 steps 4 and 5 |
| `Induction.lean` | Without polynomials: `greedy_cover`, `one_step`, `supersaturation` (note 39 Lemma 1.2 as stated), the recursion unrolled (`bnd_le`, `bnd_closed`), Theorem R in abstract form (`abstract_descent`, `abstract_descent_notes`, `abstract_descent_sharp`) and note 37 Theorem 3.5 in abstract form (`abstract_descent_DP`). | note 39 Lemma 1.2, Theorem 1.3; note 37 Corollary 3.4, Theorem 3.5; note 46 section 1.3 |
| `TheoremR.lean` | `BadTriple`, `PLsub`, `PL`, `baseB`, and Theorem R: `theoremR`, `theoremR_top` (the level `J`, with `B_J = n / Δ`), `theoremR_gen`, `theoremR_sharp`. | note 46 Theorem R; note 39 Theorem 1.3 |
| `Theorem35.lean` | `DPsub` and `theorem35`. | note 37 Theorem 3.5 |
| `Numbers.lean` | The arithmetic at `N = 25`, `k = 2^24`, `T = ⌈0.64 n⌉`: the bounds for `f = 7, 16, 133, 134` at `j₀ = 24` and for `f = 7, 16, 134` at `j₀ = 20`, with `B_{20} ≤ 328734`; Theorem R at these parameters (`theoremR_N25_f7`, `theoremR_N25_f7_j20`). | note 39 section 1 "Numbers"; note 46 section 1.5 "Numbers" |
| `Instance.lean` | The hypotheses of `theoremR` can be met together: PL`(f, 1)` from the elementary bound (`PLsub_one_of_prod_le`), and `theoremR` applied on `GaloisField 2 64` with its hypothesis discharged (`concrete_K64`). | |
| `Axioms.lean` | The axiom checks of every public theorem of the library. | |

## Where to start

- `PeriodDescent.theoremR` and the definitions it uses: `IsSubspace` (`Level.lean`), `subPoly` (`Level.lean`), `polyAgr` (`Base.lean`), `Periodic` (`Core.lean`), `BadTriple`, `PLsub`, `baseB` (`TheoremR.lean`). `theoremR_top` is the case `k ≤ 2^{j₀}`, where the bound is that of note 39 Theorem 1.3, `C(f + 1, 3)^{j₀} 2^(N j₀ - j₀ (j₀ - 1) / 2) (n / Δ + 1)`.
- `PeriodDescent.theoremR_N25_f7`: on every subspace of dimension 25 of every field of characteristic two, under PL`(7, 24)` every word has at most `2^467` polynomials of degree `< 2^24` agreeing with it on at least `21474837 = ⌈0.64 · 2^25⌉` points. `theoremR_N25_f7_j20`: at most `2^445` under PL`(7, 20)`.
- `PeriodDescent.LevelPb.descent_step`: note 37 Proposition 3.3. `PeriodDescent.periodic_triple_iff`: the members periodic for a pair are exactly `c₀ + ϱ Q(X² + a X)`.
- `PeriodDescent.abstract_descent`: the induction with nothing but finite sets, from which `theoremR` is an instance.
- `PeriodDescent.base_bound` and `PeriodDescent.affine_ordinary_bound`: note 37 Lemma 3.2 and note 04 Theorem 1.2.
- `PeriodDescent.threewise_johnson` and `PeriodDescent.threewise_johnson_rat`: note 44 Lemma 5.2.

## How the statements are modelled

- A subspace domain is a finite set `D : Finset F` with `IsSubspace D` (it contains `0` and is closed under addition) over a field with `[CharP F 2]`. In characteristic two this is an `𝔽₂`-subspace, and `D.card = 2 ^ N` says that its dimension is `N`.
- A word that may be blank is a function `F → Option F`; only its values on `D` are read, and `none` is the blank `⊥`. The agreement of `P ∘ ℓ` with `v` is `polyAgr D ℓ v P = #{x ∈ D : v x = some (P(ℓ(x)))}`.
- "The rational function `v / u` is unchanged by `X ↦ X + a`" is stated without fractions: `Periodic a u v` is `v(X) u(X + a) = v(X + a) u(X)`. For `u ≠ 0` this is the equality of `v / u` and its translate in `F(X)`. A triple `(P_a, P_b, P_c)` has `u = P_b - P_a` and `v = P_c - P_a`; `Periodic.swap` and `Periodic.base_swap` show that the property does not depend on the order of the three, and `periodic_of_const` that a constant function has every period.
- The levels are given by their polynomials. `IsLevel D j ℓ` is generated by `X` and `ℓ ↦ ℓ² + a ℓ`, the polynomials that the descent reaches; `IsLevel.exists_subspace` shows that each is `L_U` for a subspace `U ⊆ D` with `2^j` elements, so the hypothesis over all such `U` (`PLsub`, the one of the referee) implies the hypothesis the proof uses (`PL`).
- Bounds are stated cross-multiplied in `ℕ` or `ℤ` where the notes divide, and again with division in `ℚ` for the statements that are cited: `base_bound`, `threewise_johnson_rat`, `theoremR`.
- `Numbers.lean` uses `norm_num`, `decide` and `omega` on explicit numerals. Powers of two beyond `2^256` need `set_option exponentiation.threshold 1000`, which lifts a guard of the elaborator and adds no axiom.

## What the Lean statements add to the notes, and what differs

- `theoremR` needs `k ≥ 1`, `k ≤ T ≤ 2^N`, `f ≥ 2` and `j₀ ≤ N - 1`. The conditions `k ≥ 2`, `j₀ ≥ 1` and `j₀ ≤ ⌈log₂ k⌉` of note 46 are not used. `theoremR_gen` has the bound minus one.
- `one_step` gives `L ≤ f + C(f, 2) W` for a list in which every pair has at most `W` bad thirds, by taking a largest sublist without bad triple. The constant of note 39 Lemma 1.2 is `C(f + 1, 3)`; that lemma is proved as stated (`supersaturation`), from the same argument and not by the count of bad triples of the note. `theoremR_sharp` is Theorem R with `C(f, 2)^{j₀}` in place of `C(f + 1, 3)^{j₀}`; it is not in the notes.
- `list_bound_nat` shows that note 37 Lemma 3.2 uses nothing of the code but that two members that agree at `κ + 1` points of the quotient are equal.
- In note 44 Lemma 5.2 the hypothesis `α ≥ ϱ` follows from `α² (3 - α) > 2 ϱ` and `α ≤ 1`, and `M ≥ 3` is not needed; the sets may have more than `a` points.

## What is not formalized

- The hypothesis PL itself, which is a conjecture, and DP.
- Note 39 Lemma 1.4 (multi-valued words reduce to ordinary words), Corollary 1.5 and Corollary R0 of note 46: the reduction of the hypothesis to ordinary words.
- Note 39 Proposition 1.6 beyond (a) implies (b), which is `supersaturation`; Remark 1.7.
- Note 37 Corollary 3.6 (bounded index), and everything outside section 3 of note 37 and section 1 of note 39.
- Note 44 beyond Lemma 5.2: Lemma 5.1, Lemma 5.4 and Theorem 5.5 are not formalized.
- The numbers of note 46 for `j₀ = 18, 19, 21` and for `f = 1000`, and those of Corollary R0.
- The interleaved case and leanVM's concrete field and domain. The theorems are quantified over every field of characteristic two and every subspace, so they apply to them; no statement about leanVM's tower is made.

## Conventions

- No `sorry`, no `axiom`, no `admit`, no `native_decide`. `lakefile.toml` sets `warningAsError`, so a `sorry` fails the build, and turns `autoImplicit` and `relaxedAutoImplicit` off.
- `PeriodDescent/Axioms.lean` prints, under `#guard_msgs`, the axioms of every public theorem of the library, 140 in all. Each depends on Lean's three standard axioms `propext`, `Classical.choice`, `Quot.sound` or a subset, and the build fails if one gains an axiom. The expected messages are the docstrings before `#guard_msgs`; they are checked by Lean and are not comments.
- In the sources `K` or `F` is the field, `D` the domain, `n = D.card`, `ℓ` a level polynomial, `m = 2^j` the size of its fibres, `κ` a degree bound, `A` an agreement, `Δ` the slack, `ϱ` the polynomial `rho a (c₁ - c₀)`, `q = qPoly a = X² + a X`.

## Build

The toolchain is `leanprover/lean4:v4.36.0` (`lean-toolchain`) and Mathlib is the tag `v4.36.0`, revision `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`; `lean-toolchain` and `lake-manifest.json` are copies of those of `doc/deep_fold/lean`, so the two projects can share one `.lake/packages`. On a machine where fetching the toolchain and Mathlib's prebuilt cache is acceptable:

```sh
cd doc/whir_soundness_gap_notes/lean_descent
lake exe cache get
lake build
```

`lake build` with no target builds the library `PeriodDescent`, the default target of `lakefile.toml`, and ends with `Build completed successfully`. Build outputs go to `.lake/`, which `.gitignore` ignores. Lake prints an advisory that the files import `Mathlib` without the module system; it is not a Lean warning.

## How it was checked

On the build host `h4`, with a copy of this directory and the `.lake/packages` of the build of `doc/deep_fold/lean` (same manifest, nothing downloaded): the project's build directory removed, then `lake build` on eight cores at nice 10, ending with `Build completed successfully` and exit status 0; the SHA-256 of every file of this directory equal in the repository and in the copy that was built; and a negative control, a theorem proved by `sorry` added to the copy, on which the same build fails. The report `../47-lean-period-descent.md` has the commands, the job count and the hashes.
