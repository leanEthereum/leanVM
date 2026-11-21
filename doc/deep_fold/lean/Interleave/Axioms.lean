/-
The axioms of the named statements of the library `Interleave` listed below: Lean's three
(`propext`, `Classical.choice`, `Quot.sound`) and nothing else (the five statements about the
recursion `treeN` alone do not use `Classical.choice`). Each check is under `#guard_msgs`, so the
build fails if a statement gains an axiom (a `sorry` would show as `sorryAx`).

The first statements, `concrete_unique`, `concrete_two_mul` and `concrete_descent`, instantiate
the reductions at `K = GF(2^64)` and a quadratic extension `E` of it (a field with `2^128`
elements), with four lanes: the typeclass hypotheses are satisfiable there, and so is the list
hypothesis `H_K` (Hypothesis 6.4 of the paper), by unique decoding. The field sizes are leanVM's.
The instances are not its deployed parameters: the fields are Mathlib's `GaloisField 2 64` and
`FiniteField.Extension` and not leanVM's tower, the lane count is fixed at four, and the domain
is any set of points.
-/
import Interleave.Closed
import Interleave.TwoLanes

namespace Interleave

/-- `GF(2^64)`. -/
abbrev K64 : Type := GaloisField 2 64

/-- A quadratic extension of `GF(2^64)`: a field with `2^128` elements and a `K64`-algebra. -/
abbrev E128 : Type := FiniteField.Extension K64 2 2

/-- `E128` has `2^128` elements. -/
theorem natCard_E128 : Nat.card E128 = 2 ^ 128 := by
  rw [FiniteField.natCard_extension K64 2 2, GaloisField.card 2 64 (by norm_num)]
  norm_num

/-- Unconditional: on any set `D` of points of `GF(2^64)`, beyond half the distance, words with
values in `E128^4` have at most one tuple of polynomials. `H_K` is proved (`rsListBound₁_one`) and
Theorem 6.1 of the paper applied, so the hypotheses of `rs_interleave_same` are satisfiable
together. -/
theorem concrete_unique (D : Finset K64) (d a : ℕ) (hda : d < a) (h : D.card + d < 2 * a) :
    RSListBound D E128 (Fin 4) d a 1 :=
  rs_interleave_same E128 (Fin 4) (rsListBound₁_one D h) hda (by omega)

/-- Theorem 6.1 of the paper at these fields: from `H_K` at `a > (n + 3d)/4`, any `L`. -/
theorem concrete_two_mul (D : Finset K64) (d a L : ℕ) (hL : RSListBound₁ D d a L) (hda : d < a)
    (h4 : D.card + 3 * d < 4 * a) : RSListBound D E128 (Fin 4) d a (2 * L - 1) :=
  rs_interleave_two_mul E128 (Fin 4) hL hda h4

/-- Proposition 6.2 of the paper at these fields: from `H_K` with `L ≤ 2^63`, every list
`S` of a word with values in `E128^4` has `|S|·(2^64 - L) ≤ L·2^64`. -/
theorem concrete_descent (D : Finset K64) (d a L : ℕ) (hL : RSListBound₁ D d a L)
    (h2 : L ≤ 2 ^ 63) (w : K64 → Fin 4 → E128) (S : Finset (Fin 4 → Polynomial E128))
    (hS : ∀ P ∈ S, (∀ u, (P u).natDegree ≤ d) ∧
      a ≤ (agr D w (fun x u => (P u).eval (algebraMap K64 E128 x))).card) :
    S.card ≤ 2 * L - 1 ∧ S.card * (2 ^ 64 - L) ≤ L * 2 ^ 64 := by
  have := Fintype.ofFinite K64
  have hcard : Fintype.card K64 = 2 ^ 64 := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 64 (by norm_num)
  have h := rs_descent₁ E128 (Fin 4) hL (by rw [hcard]; omega) w S hS
  rwa [hcard] at h

/-- info: 'Interleave.natCard_E128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms natCard_E128

/-- info: 'Interleave.concrete_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms concrete_unique

/-- info: 'Interleave.concrete_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms concrete_two_mul

/-- info: 'Interleave.concrete_descent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms concrete_descent

/-- info: 'Interleave.AgreeLE.interleave' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AgreeLE.interleave

/-- info: 'Interleave.AgreeLE.listBound_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AgreeLE.listBound_one

/-- info: 'Interleave.ListBound.interleave_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ListBound.interleave_zero

/-- info: 'Interleave.treeN_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms treeN_mono

/-- info: 'Interleave.treeN_eq_L' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms treeN_eq_L

/-- info: 'Interleave.treeN_eq_two_mul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms treeN_eq_two_mul

/-- info: 'Interleave.treeN_eq_sq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms treeN_eq_sq

/-- info: 'Interleave.tree_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tree_core

/-- info: 'Interleave.interleave_listBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interleave_listBound

/-- info: 'Interleave.interleave_listBound_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interleave_listBound_one

/-- info: 'Interleave.interleave_listBound_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interleave_listBound_same

/-- info: 'Interleave.interleave_listBound_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interleave_listBound_two_mul

/-- info: 'Interleave.interleave_listBound_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interleave_listBound_sq

/-- info: 'Interleave.two_mul_card_le_image_add_collisions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_mul_card_le_image_add_collisions

/-- info: 'Interleave.card_vanish_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_vanish_mul_le

/-- info: 'Interleave.exists_linearMap_collisions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_linearMap_collisions

/-- info: 'Interleave.exists_linearMap_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_linearMap_image

/-- info: 'Interleave.descent_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms descent_arith

/-- info: 'Interleave.descent_ineq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms descent_ineq

/-- info: 'Interleave.descent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms descent

/-- info: 'Interleave.descent_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms descent_div

/-- info: 'Interleave.gen_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gen_unique

/-- info: 'Interleave.gen_interleave' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gen_interleave

/-- info: 'Interleave.gen_interleave_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gen_interleave_same

/-- info: 'Interleave.gen_interleave_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gen_interleave_two_mul

/-- info: 'Interleave.gen_interleave_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gen_interleave_sq

/-- info: 'Interleave.rs_agree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rs_agree_le

/-- info: 'Interleave.rsListBound₁_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rsListBound₁_iff

/-- info: 'Interleave.rsListBound_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rsListBound_iff

/-- info: 'Interleave.RSListBound.image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms RSListBound.image

/-- info: 'Interleave.rsListBound₁_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rsListBound₁_one

/-- info: 'Interleave.rs_interleave' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rs_interleave

/-- info: 'Interleave.rs_interleave_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rs_interleave_same

/-- info: 'Interleave.rs_interleave_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rs_interleave_two_mul

/-- info: 'Interleave.rs_interleave_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rs_interleave_sq

/-- info: 'Interleave.rs_descent₁' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rs_descent₁

/-- info: 'Interleave.rs_descent₁_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rs_descent₁_div

/-- info: 'Interleave.rs_descent₁_listBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rs_descent₁_listBound

/-- info: 'Interleave.rs_descent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rs_descent

/-- info: 'Interleave.rs_descent_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rs_descent_div

/-- info: 'Interleave.treeSum_eq_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSum_eq_min

/-- info: 'Interleave.treeN_le_treeSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeN_le_treeSum

/-- info: 'Interleave.treeSum_le_choose_mul_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSum_le_choose_mul_pow

/-- info: 'Interleave.treeN_le_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeN_le_closed

/-- info: 'Interleave.treeN_le_choose_mul_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeN_le_choose_mul_pow

/-- info: 'Interleave.interleave_listBound_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interleave_listBound_closed

/-- info: 'Interleave.interleave_listBound_choose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interleave_listBound_choose

/-- info: 'Interleave.rs_interleave_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rs_interleave_closed

/-- info: 'Interleave.listBound_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms listBound_prod

/-- info: 'Interleave.listBound_prod_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms listBound_prod_self

/-- info: 'Interleave.listBound_prod_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms listBound_prod_two_mul

/-- info: 'Interleave.ListBound.of_interleave' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ListBound.of_interleave

/-- info: 'Interleave.interleave_listBound_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms interleave_listBound_iff

/-- info: 'Interleave.rs_listBound_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rs_listBound_min

/-- info: 'Interleave.treeN_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms treeN_pos

/-- info: 'Interleave.sum_choose_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sum_choose_le

/-- info: 'Interleave.map_enc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms map_enc

/-- info: 'Interleave.GenListBound.pos_or' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GenListBound.pos_or

end Interleave
