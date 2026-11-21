# Constructions: the attack side

The library `Constructions` of the Lake project in the parent directory. It machine-checks the explicit constructions of Section 3 of the paper, which show that the Johnson radius cannot be beaten for the protocol of Annex B: subspace polynomials and the flats lemma (Proposition 3.3), the pole collapse of the affine combiner and of every polynomial combiner, with its consequence that lists are pole pairs (Proposition 3.5), and three forms of the families at agreement `5n/8` for rate 1/2 (Proposition 3.4(a) and (c)). It imports Mathlib only and uses none of the other libraries. The project's `README.md` has the conventions and the build.

The exact counts of the paper (`56n - 392` members in Proposition 3.4(a), the Gaussian binomials in Proposition 3.3) are not checked: `GluedCount.lean` proves a lower bound of `n / 8 - 1` members, with agreement at least, not exactly, `5n/8`, and the number of subspaces is checked for hyperplanes only. Proposition 3.4(b) is not formalized. The count of bad challenges in Proposition 3.5 assumes the field large enough for some pole to separate the list.

## Files

In dependency order. `L_V` is the subspace polynomial of `V`, and `m` the size of `V`.

| file | content | in the paper |
| --- | --- | --- |
| `Subspace.lean` | locators, `subPoly V = ∏_{v ∈ V} (X - v)`, additivity over any field, the recursion `L_{W + {0, a}} = L_W² + L_W(a) L_W`, induction on finite subspaces, `L_V` is linearized, `deg (L_V - X^m) ≤ m / 2` | Proposition 3.3 (subspace polynomials are linearized) |
| `Flats.lean` | lists (`agree`, `RSList`), `Q_V = (X^m - L_V) / X`, the flats lemma, at least `n - 1` hyperplanes in a domain of `n` points, the rate-1/4 statement `flats_quarter` | Proposition 3.3 |
| `Pole.lean` | folds, the pole collapse for the affine combiner and for any polynomial combiner, a list member gives a line of bad challenges (`lemmaA`) with its witness and its count, a pole separating a finite list | Proposition 3.5 |
| `Padded.lean` | a fixed set `P` and a free flat, at least `n - 2` list members at agreement `p + n / 4` for `p` the size of `P`, the two `5n/8` corollaries | Proposition 3.4(c) |
| `Gap.lean` | the gap lemma for products and for locators of disjoint unions, the gaps of a free flat and of a coset | the degree count in the proof of Proposition 3.4(c) |
| `UnionOfFlats.lean` | unions of cosets of `W` and of larger flats share the top of a power of `X` times `L_W` | Proposition 3.4(a) in its description by unions of flats |
| `Glued.lean` | `L_S = V_Y(L_W)` for a union of cosets, the degree bound for the word `L_U^g`, one list member per label set, members of different hyperplanes | Proposition 3.4(a), one list member per label set |
| `GluedCount.lean` | a label set per hyperplane that is not invariant under `U`, at least `n / 8 - 1` list members of `L_U^5` | Proposition 3.4(a), a lower bound on the count |
| `Concrete.lean` | flats as a failure of mutual correlated agreement, and the end statements in `GaloisField 2 128` at `n = 2^26` and `n = 2^25` | Propositions 3.3, 3.4, 3.5 at the deployed sizes |
| `Axioms.lean` | the axiom checks | |
