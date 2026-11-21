/-
Glued coset unions: the word `L_U ^ g`, which for `g = 5` and `|U| = n / 8` is the word of
Proposition 3.4(a) of the paper. `UnionOfFlats.lean` describes the same family as unions of flats;
`L_U ^ 5` and `X ^ (n / 2) L_W` differ by degree at most `n / 2`.

`W` is a hyperplane of the subspace `U`, `a ∈ U \ W`, `η = L_W(a)`, so `L_U = L_W² + η L_W`. For a
set `Y` of `2g` labels in `L_W(D)` with `∑ Y = g η`, the union `S = D ∩ L_W⁻¹(Y)` of `2g` cosets of
`W` has `L_S = V_Y(L_W)` with `V_Y = ∏_{y ∈ Y} (X - y)`, and `L_U ^ g - L_S` has degree at most
`(2g - 2) |W| = (g - 1) |U|` (`natDegree_gluedPoly_le`). So the word `L_U ^ g` has one list
member per such `Y`, at agreement `g |U|` and degree at most `(g - 1) |U|` (`glued_list`); for
`|U| = n / 8` and `g = 5` this is agreement `5n/8` and degree at most `n / 2`
(`glued_five_eighths`). Members from different hyperplanes `W` of `U` coincide only if they are
invariant under `U` (`glued_eq_imp_invariant`).
-/
import Constructions.Padded

open Polynomial
open scoped Classical

namespace Constructions

variable {K : Type*} [Field K]

/-- Two monic polynomials of the same degree `n` with the same second coefficient differ by a
polynomial of degree at most `n - 2`. -/
theorem natDegree_sub_le_of_nextCoeff_eq {p q : K[X]} (hp : p.Monic) (hq : q.Monic) {n : ℕ}
    (hpn : p.natDegree = n) (hqn : q.natDegree = n) (h : p.nextCoeff = q.nextCoeff) :
    (p - q).natDegree ≤ n - 2 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_sub, sub_eq_zero]
  rcases lt_trichotomy N n with hlt | heq | hgt
  · have hn : 0 < n := by omega
    have hN1 : N = n - 1 := by omega
    rw [nextCoeff_of_natDegree_pos (by omega), nextCoeff_of_natDegree_pos (by omega), hpn, hqn] at h
    rw [hN1]
    exact h
  · rw [heq]
    have h1 := hp.coeff_natDegree
    have h2 := hq.coeff_natDegree
    rw [hpn] at h1
    rw [hqn] at h2
    rw [h1, h2]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

/-- `L_W` is constant on a coset of `W`. -/
theorem subPoly_eval_of_mem_flat {W : AddSubgroup K} [Finite W] {a x : K} (hx : x ∈ flat W a) :
    (subPoly W).eval x = (subPoly W).eval a := by
  have h := subPoly_eval_add_mem W (mem_flat.mp hx) a
  rwa [add_sub_cancel] at h

/-- The points with the same value of `L_W` as `a` are the coset `a + W`. -/
theorem mem_flat_iff_subPoly_eval {W : AddSubgroup K} [Finite W] {a x : K} :
    x ∈ flat W a ↔ (subPoly W).eval x = (subPoly W).eval a := by
  refine ⟨subPoly_eval_of_mem_flat, fun h => ?_⟩
  rw [mem_flat, ← subPoly_eval_eq_zero]
  have h2 := subPoly_eval_add W (x - a) a
  rw [sub_add_cancel, h] at h2
  exact right_eq_add.mp h2

/-- The union of the cosets of `W` in `D` with labels in `Y`: `S = D ∩ L_W⁻¹(Y)`. -/
noncomputable def glued (D W : AddSubgroup K) (Y : Finset K) : Finset K :=
  (pts D).filter (fun x => (subPoly W).eval x ∈ Y)

/-- `L_S = V_Y(L_W)`: the locator of a union of cosets of `W` is a polynomial in `L_W`. -/
theorem locator_glued (D W : AddSubgroup K) [Finite D] [Finite W] (hWD : W ≤ D) (Y : Finset K)
    (hY : ∀ y ∈ Y, ∃ a ∈ D, (subPoly W).eval a = y) :
    locator (glued D W Y) = (locator Y).comp (subPoly W) := by
  have hex : ∀ y : K, ∃ a : K, y ∈ Y → a ∈ D ∧ (subPoly W).eval a = y := by
    intro y
    by_cases hy : y ∈ Y
    · obtain ⟨a, ha⟩ := hY y hy
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => absurd h hy⟩
  choose a ha using hex
  have hS : glued D W Y = Y.biUnion (fun y => flat W (a y)) := by
    ext x
    rw [glued, Finset.mem_filter, Finset.mem_biUnion, mem_pts]
    constructor
    · rintro ⟨-, hxY⟩
      exact ⟨_, hxY, mem_flat_iff_subPoly_eval.mpr (ha _ hxY).2.symm⟩
    · rintro ⟨y, hy, hx⟩
      have hval := subPoly_eval_of_mem_flat hx
      rw [(ha y hy).2] at hval
      refine ⟨?_, hval ▸ hy⟩
      have := D.add_mem (hWD (mem_flat.mp hx)) (ha y hy).1
      rwa [sub_add_cancel] at this
  have hdisj : (Y : Set K).PairwiseDisjoint (fun y => flat W (a y)) := by
    intro y hy y' hy' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    apply hne
    have h1 := subPoly_eval_of_mem_flat hx
    have h2 := subPoly_eval_of_mem_flat hx'
    rw [(ha y hy).2] at h1
    rw [(ha y' hy').2] at h2
    exact h1.symm.trans h2
  rw [hS, locator, Finset.prod_biUnion hdisj, locator, prod_comp]
  refine Finset.prod_congr rfl fun y hy => ?_
  have := locator_coset W (a y)
  rw [(ha y hy).2] at this
  rw [sub_comp, X_comp, C_comp, ← this]
  rfl

theorem card_glued (D W : AddSubgroup K) [Finite D] [Finite W] (hWD : W ≤ D) (Y : Finset K)
    (hY : ∀ y ∈ Y, ∃ a ∈ D, (subPoly W).eval a = y) :
    (glued D W Y).card = Y.card * Nat.card W := by
  rw [← locator_natDegree, locator_glued D W hWD Y hY, natDegree_comp, locator_natDegree,
    subPoly_natDegree]

/-- The label set is recovered from the union. -/
theorem glued_injective (D W : AddSubgroup K) {Y Y' : Finset K}
    (hY : ∀ y ∈ Y, ∃ a ∈ D, (subPoly W).eval a = y)
    (hY' : ∀ y ∈ Y', ∃ a ∈ D, (subPoly W).eval a = y) [Finite D]
    (h : glued D W Y = glued D W Y') : Y = Y' := by
  have key : ∀ Y Y' : Finset K, (∀ y ∈ Y, ∃ a ∈ D, (subPoly W).eval a = y) →
      glued D W Y = glued D W Y' → Y ⊆ Y' := by
    intro Y Y' hY h y hy
    obtain ⟨a, haD, rfl⟩ := hY y hy
    have : a ∈ glued D W Y := Finset.mem_filter.mpr ⟨mem_pts.mpr haD, hy⟩
    rw [h] at this
    exact (Finset.mem_filter.mp this).2
  exact Finset.Subset.antisymm (key Y Y' hY h) (key Y' Y hY' h.symm)

/-- A union of cosets of `W` is invariant under translation by `W`. -/
theorem glued_add_mem (D W : AddSubgroup K) [Finite D] [Finite W] (hWD : W ≤ D) (Y : Finset K)
    {x w : K} (hx : x ∈ glued D W Y) (hw : w ∈ W) : x + w ∈ glued D W Y := by
  obtain ⟨hxD, hxY⟩ := Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨mem_pts.mpr (D.add_mem (mem_pts.mp hxD) (hWD hw)), ?_⟩
  rwa [subPoly_eval_add_mem W hw x]

/-- The polynomial of a glued union: `L_U ^ g - L_S`. -/
noncomputable def gluedPoly (D U W : AddSubgroup K) (g : ℕ) (Y : Finset K) : K[X] :=
  subPoly U ^ g - locator (glued D W Y)

section CharTwo

variable [CharP K 2]

/-- A subgroup of index two is extended to the whole group by any element outside it. -/
theorem eq_adjoin_of_card {U W : AddSubgroup K} [Finite U] (hWU : W ≤ U)
    (hc : 2 * Nat.card W = Nat.card U) {a : K} (haU : a ∈ U) (haW : a ∉ W) : U = adjoin W a := by
  have : Finite W := Set.finite_coe_iff.mpr ((Set.toFinite (U : Set K)).subset hWU)
  have hle : adjoin W a ≤ U := by
    rintro x (hx | hx)
    · exact hWU hx
    · have := U.sub_mem (hWU hx) haU
      rwa [add_sub_cancel_right] at this
  have hsub : pts (adjoin W a) ⊆ pts U := fun x hx => mem_pts.mpr (hle (mem_pts.mp hx))
  have hcard : (pts U).card ≤ (pts (adjoin W a)).card := by
    rw [card_pts, card_pts, card_adjoin W haW, hc]
  exact (pts_injective (Finset.eq_of_subset_of_card_le hsub hcard)).symm

/-- `L_U = L_W² + η L_W` as a composition: `L_U = (X² + η X) ∘ L_W`. -/
theorem subPoly_eq_comp {U W : AddSubgroup K} [Finite U] (hWU : W ≤ U)
    (hc : 2 * Nat.card W = Nat.card U) {a : K} (haU : a ∈ U) (haW : a ∉ W) :
    subPoly U = (X ^ 2 + C ((subPoly W).eval a) * X).comp (subPoly W) := by
  have : Finite W := Set.finite_coe_iff.mpr ((Set.toFinite (U : Set K)).subset hWU)
  rw [eq_adjoin_of_card hWU hc haU haW, subPoly_adjoin W haW]
  simp only [add_comp, pow_comp, X_comp, mul_comp, C_comp]

/-- **The degree bound behind Proposition 3.4(a) of the paper.** For `2g` labels `Y ⊆ L_W(D)` with
`∑ Y = g η`, `deg (L_U ^ g - L_S) ≤ (2g - 2) |W|`. -/
theorem natDegree_gluedPoly_le (D U W : AddSubgroup K) [Finite D] [Finite U] (hUD : U ≤ D)
    (hWU : W ≤ U) (hc : 2 * Nat.card W = Nat.card U) {a : K} (haU : a ∈ U) (haW : a ∉ W)
    {g : ℕ} (Y : Finset K) (hY : ∀ y ∈ Y, ∃ b ∈ D, (subPoly W).eval b = y)
    (hYc : Y.card = 2 * g) (hYs : ∑ y ∈ Y, y = g • (subPoly W).eval a) :
    (gluedPoly D U W g Y).natDegree ≤ (2 * g - 2) * Nat.card W := by
  have : Finite W := Set.finite_coe_iff.mpr ((Set.toFinite (U : Set K)).subset hWU)
  set η := (subPoly W).eval a with hη
  have hq : (X ^ 2 + C η * X : K[X]).Monic := by
    refine (monic_X_pow 2).add_of_left ?_
    rw [degree_X_pow]
    exact lt_of_le_of_lt (degree_C_mul_X_le η) (by norm_num)
  have hqdeg : (X ^ 2 + C η * X : K[X]).natDegree = 2 := by
    rw [natDegree_add_eq_left_of_natDegree_lt]
    · exact natDegree_X_pow 2
    · rw [natDegree_X_pow]
      exact lt_of_le_of_lt ((natDegree_C_mul_le _ _).trans natDegree_X_le) (by norm_num)
  have hqnext : (X ^ 2 + C η * X : K[X]).nextCoeff = η := by
    rw [nextCoeff_of_natDegree_pos (by rw [hqdeg]; norm_num), hqdeg]
    simp [coeff_X_pow]
  have hdeg : ((X ^ 2 + C η * X : K[X]) ^ g - locator Y).natDegree ≤ 2 * g - 2 := by
    refine natDegree_sub_le_of_nextCoeff_eq (hq.pow g) (locator_monic Y) ?_ ?_ ?_
    · rw [hq.natDegree_pow, hqdeg, mul_comm]
    · rw [locator_natDegree, hYc]
    · rw [hq.nextCoeff_pow, hqnext, locator, prod_X_sub_C_nextCoeff, CharTwo.neg_eq]
      exact hYs.symm
  have e : gluedPoly D U W g Y =
      ((X ^ 2 + C η * X : K[X]) ^ g - locator Y).comp (subPoly W) := by
    rw [gluedPoly, locator_glued D W (hWU.trans hUD) Y hY, subPoly_eq_comp hWU hc haU haW,
      sub_comp, pow_comp]
  rw [e]
  refine natDegree_comp_le.trans ?_
  rw [subPoly_natDegree]
  exact Nat.mul_le_mul_right _ hdeg

/-- **One list member** (Proposition 3.4(a) of the paper for `g = 5`). The word `L_U ^ g` agrees
with `L_U ^ g - L_S`, of degree at most `(2g - 2) |W| = (g - 1) |U|`, on the `2g |W| = g |U|`
points of `S`. -/
theorem gluedPoly_mem_RSList (D U W : AddSubgroup K) [Finite D] [Finite U] (hUD : U ≤ D)
    (hWU : W ≤ U) (hc : 2 * Nat.card W = Nat.card U) {a : K} (haU : a ∈ U) (haW : a ∉ W)
    {g : ℕ} (Y : Finset K) (hY : ∀ y ∈ Y, ∃ b ∈ D, (subPoly W).eval b = y)
    (hYc : Y.card = 2 * g) (hYs : ∑ y ∈ Y, y = g • (subPoly W).eval a) :
    gluedPoly D U W g Y ∈ RSList (pts D) (fun x => (subPoly U).eval x ^ g)
      ((2 * g - 2) * Nat.card W + 1) (2 * g * Nat.card W) := by
  have : Finite W := Set.finite_coe_iff.mpr ((Set.toFinite (U : Set K)).subset hWU)
  constructor
  · refine lt_of_le_of_lt degree_le_natDegree ?_
    exact_mod_cast Nat.lt_succ_of_le
      (natDegree_gluedPoly_le D U W hUD hWU hc haU haW Y hY hYc hYs)
  · rw [← hYc, ← card_glued D W (hWU.trans hUD) Y hY]
    refine Finset.card_le_card fun x hx => ?_
    rw [agree, Finset.mem_filter]
    refine ⟨(Finset.mem_filter.mp hx).1, ?_⟩
    rw [gluedPoly, eval_sub, eval_pow, locator_eval_eq_zero.mpr hx, sub_zero]

/-- **The list for one hyperplane** (Proposition 3.4(a) of the paper for `g = 5`). The word
`L_U ^ g` has at least as many polynomials of degree at most `(g - 1) |U|` agreeing with it on at
least `g |U|` points of `D` as there are sets of `2g` labels in `L_W(D)` with sum `g η`. -/
theorem glued_list (D U W : AddSubgroup K) [Finite D] [Finite U] (hUD : U ≤ D)
    (hWU : W ≤ U) (hc : 2 * Nat.card W = Nat.card U) {a : K} (haU : a ∈ U) (haW : a ∉ W)
    (g : ℕ) :
    {Y : Finset K | (∀ y ∈ Y, ∃ b ∈ D, (subPoly W).eval b = y) ∧ Y.card = 2 * g ∧
        ∑ y ∈ Y, y = g • (subPoly W).eval a}.encard ≤
      (RSList (pts D) (fun x => (subPoly U).eval x ^ g)
        ((g - 1) * Nat.card U + 1) (g * Nat.card U)).encard := by
  have e1 : (g - 1) * Nat.card U = (2 * g - 2) * Nat.card W := by
    rw [← hc, ← mul_assoc]
    congr 1
    omega
  have e2 : g * Nat.card U = 2 * g * Nat.card W := by
    rw [← hc]
    ring
  rw [e1, e2]
  refine Set.encard_le_encard_of_injOn (f := gluedPoly D U W g) ?_ ?_
  · rintro Y ⟨hY, hYc, hYs⟩
    exact gluedPoly_mem_RSList D U W hUD hWU hc haU haW Y hY hYc hYs
  · rintro Y ⟨hY, -, -⟩ Y' ⟨hY', -, -⟩ h
    exact glued_injective D W hY hY' (locator_injective (sub_right_injective h))

/-- **Rate 1/2 at `5n/8`, the word `L_U ^ 5`.** With `|U| = n / 8`: one polynomial of degree at
most `n / 2` at agreement `5n/8` for each set of ten labels with sum `η`. -/
theorem glued_five_eighths (D U W : AddSubgroup K) [Finite D] [Finite U] (hUD : U ≤ D)
    (hWU : W ≤ U) (hc : 2 * Nat.card W = Nat.card U) {a : K} (haU : a ∈ U) (haW : a ∉ W)
    {m : ℕ} (hU : Nat.card U = m) :
    {Y : Finset K | (∀ y ∈ Y, ∃ b ∈ D, (subPoly W).eval b = y) ∧ Y.card = 10 ∧
        ∑ y ∈ Y, y = (subPoly W).eval a}.encard ≤
      (RSList (pts D) (fun x => (subPoly U).eval x ^ 5) (4 * m + 1) (5 * m)).encard := by
  have h := glued_list D U W hUD hWU hc haU haW 5
  rw [hU] at h
  have e : (5 : ℕ) • (subPoly W).eval a = (subPoly W).eval a := by
    rw [show (5 : ℕ) = 2 * 2 + 1 by norm_num, add_smul, mul_smul, one_smul, two_smul,
      CharTwo.add_self_eq_zero, zero_add]
  simpa only [e] using h

/-- Members from two different hyperplanes `W ≠ W'` of `U` coincide only if they are invariant
under all of `U`. -/
theorem glued_eq_imp_invariant (D U W W' : AddSubgroup K) [Finite D] [Finite U] (hUD : U ≤ D)
    (hWU : W ≤ U) (hc : 2 * Nat.card W = Nat.card U) (hWU' : W' ≤ U)
    (hne : W ≠ W') (hc' : 2 * Nat.card W' = Nat.card U) {Y Y' : Finset K}
    (h : glued D W Y = glued D W' Y') {x u : K} (hx : x ∈ glued D W Y) (hu : u ∈ U) :
    x + u ∈ glued D W Y := by
  have : Finite W := Set.finite_coe_iff.mpr ((Set.toFinite (U : Set K)).subset hWU)
  have : Finite W' := Set.finite_coe_iff.mpr ((Set.toFinite (U : Set K)).subset hWU')
  by_cases huW : u ∈ W
  · exact glued_add_mem D W (hWU.trans hUD) Y hx huW
  -- an element of `W'` outside `W`
  obtain ⟨b, hbW', hbW⟩ : ∃ b ∈ W', b ∉ W := by
    by_contra hcon
    have hle : W' ≤ W := fun y hy => by
      by_contra hy'
      exact hcon ⟨y, hy, hy'⟩
    have hsub : pts W' ⊆ pts W := fun y hy => mem_pts.mpr (hle (mem_pts.mp hy))
    have hcard : (pts W).card ≤ (pts W').card := by
      rw [card_pts, card_pts]
      omega
    exact hne (pts_injective (Finset.eq_of_subset_of_card_le hsub hcard)).symm
  -- `u + b ∈ W` since `U = W ∪ (b + W)`
  have hU := eq_adjoin_of_card hWU hc (hWU' hbW') hbW
  have hub : u + b ∈ W := by
    have := hU ▸ hu
    rcases mem_adjoin.mp this with h1 | h1
    · exact absurd h1 huW
    · exact h1
  have h1 : x + b ∈ glued D W Y := by
    rw [h] at hx ⊢
    exact glued_add_mem D W' (hWU'.trans hUD) Y' hx hbW'
  have h2 := glued_add_mem D W (hWU.trans hUD) Y h1 hub
  have e : x + b + (u + b) = x + u := by
    linear_combination CharTwo.add_self_eq_zero b
  rwa [e] at h2

end CharTwo

end Constructions
