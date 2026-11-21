# DeepFold: the DEEP fold round

The library `DeepFold` of the Lake project in the parent directory. It proves the fold-round lemma of the paper, Lemma 4.10, with what it rests on: the evaluation functional (Definition 4.1, Lemma 4.4), candidates, classes and the determinant (Definition 4.5, Lemma 4.6), the class trichotomy (Lemma 4.7) and the counting theorem (Definition 4.8, Theorem 4.9). It imports Mathlib only. The end statements are `lemmaF_exc` and `lemmaF_round` in `Main.lean`. The project's `README.md` has the conventions, the notation and the build.

The single-lane files (`Basic.lean`, `Class.lean`, `Agreement.lean`, `Theorem.lean`) come first, and `Lanes.lean` proves the statements again for interleaved words. The determinant lemma is proved over an arbitrary field, with the signs of the determinant. Lemma 4.7(a) and (b) are checked in the form the fold round uses: `class_trichotomy` states the three alternatives, and with lanes only the consequence is checked, that a class with more than `q` elements is a polynomial pair of degrees below `d` and at most `d` (`classL_poly_of_card_gt`). The Lean form of Lemma 4.10 takes any `M ≥ max(2q, C(n, 2))`, two arbitrary linear functionals for the weight, an arbitrary injective exponent map, and a hypothesis restricted to pairs with `deg F < d`. Characteristic two is used in one place.

## Files

In dependency order.

| file | content | in the paper |
| --- | --- | --- |
| `Basic.lean` | `aff`, `Cons`, the determinant `Delta`, its vanishing at a consistent point, its degree | Definition 4.5 (the polynomial `Δ`); Lemma 4.6(c) and the degree of `Δ`, one lane |
| `Class.lean` | folds of a rational pair over `RatFunc K`, `Delta = 0` exactly for one class, uniqueness, the trichotomy (pole line, common `β`, polynomial pair) | Lemma 4.6(a), (b); Lemma 4.7(a), (b), one lane |
| `Agreement.lean` | two agreement columns outside the common agreement set of a pair determine the challenge | Lemma 4.7(c), one lane |
| `Counting.lean` | roots at `s` points, the triple count `N(z)`, the exceptional set, Markov, the count of triples not in one class, the counting theorem in abstract form | Lemma 4.6(d); Definition 4.8; Theorem 4.9 in abstract form |
| `Theorem.lean` | the single-lane theorem | Theorem 4.9 and the first half of the proof of Lemma 4.10(2), one lane |
| `Lanes.lean` | lanes with monomial weights: (E1) to (E4), the tuple `Δ`, classes, agreement, the theorem | Definition 4.1; Lemma 4.4; Lemmas 4.6, 4.7 and Theorem 4.9 with lanes |
| `Claim.lean` | zeros of the residual, the fold round with its claims and the predicate `B` | Lemma 4.10(2) for any finite set of candidates |
| `Full.lean` | the set `𝒯` of all candidates is finite | Definition 4.5 |
| `Main.lean` | the end statements for `𝒯`: `lemmaF_exc`, `lemmaF_round`, and `lemmaD4_exc`, `lemmaD4_round` with the threshold `⌈K₀^3 / 4⌉` | Lemma 4.10 |
| `Axioms.lean` | the axiom checks, and an instantiation at `GF(2^128)` with four lanes | |
