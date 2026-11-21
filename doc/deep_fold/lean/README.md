# DEEP folds: the Lean 4 development

This directory is the Lean 4 + Mathlib development that accompanies the paper "DEEP folds: WHIR soundness from list size alone" (`../main.tex`). It is one Lake project, `deepfold`, of six libraries and about 12,300 lines, over Mathlib and nothing else: it does not depend on leanVM's own formal development.

In the sources and in these READMEs, "the paper" is that paper, cited by section and statement number, and "Annex B" is Annex B of the leanVM specification, whose protocol the paper modifies. Section 8 of the paper says what is machine-checked and what is not. Appendix A lists, for every statement of the paper and for every Lean file, what corresponds to what, and quotes the main statements verbatim.

## The six libraries

| library | what it proves | in the paper |
| --- | --- | --- |
| `DeepFold` | The evaluation functional, the determinant lemma, the class trichotomy, the counting theorem, and the fold round with its claims and the predicate `B`, with lanes and monomial lane weights. | Definition 4.1, Lemma 4.4, Definition 4.5, Lemma 4.6, Lemma 4.7, Definition 4.8, Theorem 4.9, Lemma 4.10 |
| `Protocol` | Pinning, the potential for one batch and for a schedule, goodness of points and the error of the point message, the exponent maps `e_j`, and the arithmetic of the parameter claims at level 0. | Lemma 4.11, Lemma 4.12, row M0 of Theorem 5.2, Proposition 7.1 |
| `Rounds` | The transitions M1 to M5 in the relativised form that knowledge soundness needs, each as a counting statement and as a density with exactly the stated error; uniqueness of near tuples and the descent step. | rows M1 to M5 of Theorem 5.2 (Section 5.4), Definition 5.4, Lemma 5.5, Theorem 5.6 |
| `Soundness` | The composition. A definition of round-by-round soundness for a public-coin protocol given as a transition system, with the bound of every prover strategy's winning probability by the sum of the errors; an abstract model of the protocol with one batch of points per level, over any ladder of levels and with its tail; its state function; and the theorem that the model is round-by-round sound with exactly the errors of the paper, hence sound, and knowledge sound in the relativised form, with their sum. Versions from the single-lane hypothesis, with no list hypothesis in the unique-decoding range, and two concrete instances with no hypothesis at all (one level with no tail; two levels with a tail). Prover strategies exist on every ladder and with every tail that satisfy two conditions on the abstract maps. | Section 2.2, Protocol 4.2, Hypothesis 5.1, Theorem 5.2, Sections 5.3 and 5.4, Theorem 5.6, Hypothesis 6.4, Section 8.2 |
| `Interleave` | The interleaving reductions: the tree bound with its special cases and closed forms, the projection bound, the two-lane bound, their forms for Reed-Solomon codes with lanes and values in an extension, and the bridge that feeds a single-lane hypothesis over the small field into the fold-round lemma. | Theorem 6.1, Proposition 6.2, Proposition 6.3, Hypothesis 6.4, Lemma 4.10(1) |
| `Constructions` | The attack side: subspace polynomials are linearized, the flats lemma, the pole collapse for the affine and for any polynomial combiner, and three forms of the families at agreement `5n/8`. | Proposition 3.3, Proposition 3.4(a) and (c), Proposition 3.5 |

`Protocol` imports `DeepFold`, `Rounds` imports both, and `Soundness` imports `Protocol`, `Rounds` and `Interleave`. `Interleave` imports `DeepFold` in one file (`Interleave/Bridge.lean`). `Constructions` imports Mathlib only. Each library has a `README.md` that says what each of its files contains.

## Where to start

- `DeepFold.lemmaF_exc` and `DeepFold.lemmaF_round` (`DeepFold/Main.lean`): Lemma 4.10(1) and (2), the fold round. The exceptional set of points is defined from the word alone, and outside it fewer than `K₀` fold challenges let a doomed state escape.
- `Soundness.protocolD_rbr` (`Soundness/ProtocolD.lean`): the model of Protocol 4.2 has a state function with properties (i) to (iv) and the errors of rows M0 to M5 of Theorem 5.2.
- `Soundness.protocolD_sound` (`Soundness/Sound.lean`): for every prover strategy, the probability that the verifier accepts while the final polynomial does not descend to a member of the level-0 list that matches the commit-phase answers and satisfies all input claims is at most the sum of those errors over the run. `protocolD_sound_plain` is the same bound for "the verifier accepts false input claims" and `protocolD_sound_extract` for "the verifier accepts and the descent fails". They follow from `protocolD_rbr` and the union bound `StateFunction.winProb_le` (`Soundness/RBR.lean`).
- `Soundness.protocolD_sound_of_HK`, `protocolD_sound_unique`, `protocolD_sound_concrete_unique_le`, `protocolD_sound_concrete_ladder` and `err_level0` (`Soundness/Hypothesis.lean`): the same from Hypothesis 6.4; with no list hypothesis in the unique-decoding range; on one concrete level with no tail over a field of `2^128` elements with every hypothesis discharged and the bound `2^-109`, which shows that the hypotheses can be met together; on two concrete levels with a tail of two rounds, again with every hypothesis discharged, so that a run has a message of every row M0 to M5; and the level-0 errors before their grinds. Neither concrete instance is a deployed parameter set.
- `Soundness.strategy_nonempty_ladder` (`Soundness/Sound.lean`): prover strategies exist on every ladder and with every tail such that the tail admits the zero polynomial (`Terminal.AdmitsZero`) and each level fits the one before it (`Level.Fits`), so the bounds "for every strategy" are not about an empty set. `finalMsg_isEmpty` and `handover_isEmpty` show that without these conditions the prover can have no message.
- `Protocol.lemmaP` (Lemma 4.11), `Protocol.levelPot_step` (Lemma 4.12(b)), `Protocol.dens_not_good_le` and `Protocol.dens_not_goodS_le` (row M0 of Theorem 5.2, for one batch and for a schedule), `Protocol.level0_point_error` (Proposition 7.1).
- `Rounds.batch_transition`, `fold_transition`, `query_transition`, `final_transition`, `tail_round_transition` (transitions M1 to M5) and `Rounds.descent_step` (the descent step of Theorem 5.6).
- `Interleave.interleave_listBound` (Theorem 6.1), `Interleave.descent` (Proposition 6.2), `Interleave.rs_listBound_min` (Hypothesis 6.4 implies Hypothesis 5.1), `Interleave.lemmaF_exc_of_HK` (Lemma 4.10(1) from Hypothesis 6.4).
- `Constructions.flats_quarter` (Proposition 3.3 at rate 1/4), `Constructions.five_eighths_slack` and `Constructions.glued_list_card` (Proposition 3.4), `Constructions.list_gives_bad_challenges` (Proposition 3.5).

## What is formalized, and what is not

This section follows Sections 8.2 and 8.4 of the paper, which are the reference.

The Lean statements are counting statements over an arbitrary finite field, of characteristic two only where needed: a probability is the cardinality of a set of verifier messages divided by the number of messages, in `ℚ`. Where a Lean statement is weaker than the text or covers part of it, the status line of the statement in the paper says so: Lemma 4.7(a), (b) is checked through its consequence, the one-batch potential of Lemma 4.12 uses the indicator of the exceptional set, and the lists of Section 3 are lower bounds. Otherwise the Lean statements are more general than the text: any `M ≥ max(2q, C(n, 2))`, weights as arbitrary linear functionals on tuples, exponents as an arbitrary injective bounded map (with the concrete `e_j` proved to be one), and a finite set of points of any field as the domain.

The composed theorem is about a model of Protocol 4.2, and the model is abstract in these respects.

- A committed word is a function sent by the prover, as in the interactive oracle model. There are no Merkle trees.
- The map from tuples to polynomials of each level is any linear map. The high part sent at a level boundary is any polynomial on which the running weight vanishes and which keeps the sum with the image of every list member within the degree bound. The tail is a sumcheck on two tables whose inner product is the running weight applied to the final polynomial. That the real encoder has these properties is not formalized.
- A weighted claim is any linear functional on tuples with a value, and the claims may depend on the level-0 points.
- Errors are those of the interactive protocol with uniform verifier messages, before any grind. Row M1 is `(J - 1)/q`: the ring-switching scalars of leanVM's stacked opening are not modeled.
- Each level has one batch of points. The ladder schedules are not composed in Lean; for them only the potential lemma and the error of the first point message are checked.
- The bound is over the prover strategies of the model, and the prover's messages are typed: a high part and a final polynomial must have the properties above. At every other position the prover has a message outright. A final polynomial exists if the tables of the tail at the zero polynomial have inner product zero (`Terminal.AdmitsZero`; true with no tail), and a high part exists if the map of each later level sends the tuples within its degree bound to polynomials within the degree bound of the level before (`Level.Fits`). Under these two conditions strategies exist from every position, for every ladder and every tail length (`strategy_nonempty_of_fits`, `strategy_nonempty_ladder`). For abstract data that violates them the prover can have no message (`finalMsg_isEmpty`, `handover_isEmpty`), and the statement is then true and empty.

Not machine-checked:

- The list hypothesis itself. Below the Johnson radius it is taken as a hypothesis (Hypothesis 5.1, or Hypothesis 6.4), exactly as in the paper, and discharged only in the unique-decoding range. The Johnson bound and the counting bound are not connected to the composed theorem, so Corollary 5.3 is by hand. None of the list bounds of Section 6.2 for special classes of words is formalized, nor the statements of Section 6.3.
- The link from the model to the protocol: the identities of Annex B for the real encoder and weights, and that the verifier's folded column value is the folded word.
- Completeness (Proposition 4.3). No honest prover is defined in Lean.
- The Fiat-Shamir transformation, grinding and Merkle commitments.
- The outer protocol: the ring switch, the stacking, whatever happens between the commitment and the opening, the recursion.
- The ladder schedules as a composed protocol, and the composition for a predicate other than the canonical one of Section 5.3.
- The extractor as an algorithm. The extraction predicate, the existence and uniqueness of the near tuple at each step, and that it folds back, are checked; that it is found by one-error decoding in polynomial time is not.
- Exact counts on the attack side (`56n - 392`, `35n - 245`, the Gaussian binomials). For the families at `5n/8` lower bounds linear in `n` are checked, and for the flats the count of hyperplanes. Proposition 3.4(b) is by hand.
- The numbers of Section 7 other than the entries of Proposition 7.1.
- leanVM's concrete field and domain. The theorems are quantified over every finite field of characteristic two and every finite additive subgroup, so they apply to them; no isomorphism between Mathlib's `GaloisField 2 128` and leanVM's tower is stated.
- Lemmas 3.1 and 3.2, Theorem 6.6, Propositions 6.7 to 6.9 and Proposition 7.2, which are proved by hand in the paper.

## Conventions

- No `sorry`, no `axiom`, no `admit`, no `native_decide`. `lakefile.toml` sets `warningAsError`, so a `sorry` fails the build, and turns `autoImplicit` and `relaxedAutoImplicit` off.
- Each library has an `Axioms.lean` that prints, under `#guard_msgs`, the axioms of a selection of its statements that includes every theorem cited in the paper: 50 in `DeepFold`, 99 in `Protocol`, 39 in `Rounds`, 93 in `Soundness`, 65 in `Interleave` (three of them in `Interleave/Bridge.lean`), 79 in `Constructions`. Each depends on Lean's three standard axioms `propext`, `Classical.choice`, `Quot.sound` or a subset, and the build fails if one gains an axiom. The expected messages are the docstrings before `#guard_msgs`; they are checked by Lean and are not comments.
- The same files instantiate the main statements at `GaloisField 2 128` (and at `GaloisField 2 64` with a quadratic extension for the interleaving reductions and for the concrete instances of the composed theorem), so that no typeclass hypothesis is vacuous at the deployed field sizes. Every typeclass argument of an instantiation is discharged, the characteristic included, by Mathlib's instances; for the round-by-round statement the hypotheses on the analysis constants are discharged too. These instances fix the fields, not leanVM's parameters: the ones of `Interleave/Axioms.lean` are named `concrete_*`, and the concrete levels of `Soundness/Hypothesis.lean` are not deployed parameter sets.

The sources keep their own notation, which differs from the paper's as follows (Appendix A has the same list).

| Lean sources and their comments | paper |
| --- | --- |
| the field `K`, with `q` elements (in `Interleave`, `K` is the small field and `F` or `E` an extension; in `protocolD_sound_of_HK` the small field is `F`) | the field `E` |
| a word `O`, with halves `O₀`, `O₁` and fold `O_c` | `Z`, `Z_0`, `Z_1`, `Z_c` |
| the degree bound `d` | the sans-serif `d` |
| an agreement `A`; the thresholds `thr k`, written `A^{(i,k)}` | `t`, `t^{(i,k)}` |
| a fold challenge `c = (c.1, c.2)`, written `(α, β)` | `(a, b)` in sans-serif |
| the running claim's value `σ` | `c` |
| the prover's scalars `vG`, `vF`, `σ₀`, `σ₁`, `φm` | `v_G`, `v_F`, `v_{X,0}`, `v_{X,1}`, `φ_m` |
| the number of queries `t` | `ω` |
| the discount `τ` | `τ` |
| the threshold `B` of the triple count | `Θ = K₀ (K₀ - 1) (K₀ - M)` |
| the bound `Λ` on the lists of the folds (in `lemmaF_exc`) | `L` |
| `dens p`, the fraction of the elements of a finite type that satisfy `p` | a probability over a uniform verifier message |

## Build

The toolchain is `leanprover/lean4:v4.36.0` (`lean-toolchain`) and Mathlib is the tag `v4.36.0`, revision `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`; `lake-manifest.json` records it and the revisions of its dependencies. On a machine where fetching the toolchain and Mathlib's prebuilt cache is acceptable:

```sh
cd doc/deep_fold/lean
lake exe cache get
lake build
```

`lake build` with no target builds the six libraries, the default targets of `lakefile.toml`, and ends with `Build completed successfully`. Build outputs go to `.lake/`, which `.gitignore` ignores.
