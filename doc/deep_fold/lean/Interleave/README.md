# Interleave: the interleaving reductions

The library `Interleave` of the Lake project in the parent directory. It proves the reductions of Section 6.1 of the paper, which let the list hypothesis be stated for single words with values in the small field: the tree bound (Theorem 6.1), the projection bound (Proposition 6.2) and the two-lane bound (Proposition 6.3), and that Hypothesis 6.4 implies Hypothesis 5.1. The project's `README.md` has the conventions and the build.

Theorem 6.1 uses nothing of the code but a bound on the agreement of two distinct codewords, and is proved for any such code; Proposition 6.2 is proved for any code with a generator matrix. `ReedSolomon.lean` reads both for Reed-Solomon codes with lanes and values in an extension field. In this library `K` is the small field and `F` or `E` an extension.

## Files

| file | content | in the paper |
| --- | --- | --- |
| `Basic.lean` | `agr`, `AgreeLE`, `ListBound`, `interleave`; the interleaved code keeps the agreement bound; unique decoding; interleaving cannot shrink lists | the setting of Section 6.1 |
| `Tree.lean` | the recursion `treeN`, its values on `[g, 5g)`, the tree claim `tree_core`, the tree bound `interleave_listBound` and its four special cases | Theorem 6.1 |
| `Closed.lean` | the closed forms `∑ C(b,k)(L-1)^k` and `C(b+r,r) L^r` | the closed forms of Theorem 6.1 |
| `Projection.lean` | collisions of a map, the count of linear maps killing a vector, the averaging step, codes given by a generator (`enc`, `GenListBound`), the projection bound (`descent`, `descent_div`) | Proposition 6.2 |
| `Extension.lean` | the tree bound for a generated code and values in any finite-dimensional space, through a basis | Theorem 6.1 with the first paragraph of Section 6.1 |
| `ReedSolomon.lean` | polynomials and coefficient vectors, `RSListBound₁` (the hypothesis `H_K`), `RSListBound` (lanes and extensions), the tree bound and the projection bound for Reed-Solomon codes, the reduction `rs_listBound_min` | Hypothesis 6.4; Theorem 6.1 and Proposition 6.2 for Reed-Solomon codes; Hypothesis 6.4 implies Hypothesis 5.1 |
| `TwoLanes.lean` | two lanes against one, for the product of two codes | Proposition 6.3 |
| `Bridge.lean` | the hypothesis `hΛ` of `DeepFold.lemmaF_exc` from `RSListBound`, and `lemmaF_exc_of_HK`; the axiom checks of its three statements | Lemma 4.10(1) from Hypothesis 6.4 |
| `Axioms.lean` | the axiom checks, and the instantiation at `GF(2^64)` and a quadratic extension with four lanes (`concrete_unique`, `concrete_two_mul`, `concrete_descent`; the field sizes are leanVM's, the lane count is fixed at four and the domain is any set of points, so they are not deployed parameters) | |

`Bridge.lean` is the only file that imports `DeepFold` (`DeepFold.Main`), and no other file of this library depends on it.
