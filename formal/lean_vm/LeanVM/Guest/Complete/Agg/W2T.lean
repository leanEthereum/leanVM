module

public import LeanVM.Guest.Complete.Agg.W2V

/-!
# `aggregate_claims`' second run, `eq_col_tree`

`aTree_lvl`: `eq_col_tree`'s words hold level `t` of `eqtree` from `2^(t+1) - 2`. On the honest
valuation, every load of `w2Tree` through `eq_col_tree` reads or writes its honest word
(`w2_tree235`), every load through `col` its column challenge (`w2_tree156`): the previous level's
words and the challenges are read, and each product is the next level's word.
-/

namespace LeanVM.Guest.Complete.Agg

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Guest.B1.Main LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.VsC LeanVM.Guest.Complete
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

attribute [local instance high] LeanVM.Guest.Core.instDecidableEqAtom

theorem eqLevels_flat_len (cc : ℕ → E) : ∀ n, ((List.range n).flatMap (eqLevels cc)).length = 2 ^ (n + 1) - 2
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, eqLevels_flat_len cc n, List.flatMap_singleton,
      length_eqLevels]
    have : 2 ≤ 2 ^ (n + 1) := Nat.le_self_pow (by omega) 2
    rw [pow_succ 2 (n + 1)]
    omega

/-- **`eqtree`'s levels laid out**: level `t` from `2^(t+1) - 2`. -/
theorem aTree_lvl_gen (cc : ℕ → E) : ∀ n t, t < n → ∀ j < 2 ^ (t + 1),
    ((List.range n).flatMap (eqLevels cc)).getD (2 ^ (t + 1) - 2 + j) 0 = (eqLevels cc t).getD j 0
  | 0, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, t, h, j, hj => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have hl := eqLevels_flat_len cc n
    by_cases htn : t < n
    · have hmono : 2 ^ (t + 1 + 1) ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      rw [List.getD_append _ _ _ _ (by rw [hl, pow_succ 2 (t + 1)] at *; omega)]
      exact aTree_lvl_gen cc n t htn j hj
    · obtain rfl : t = n := by omega
      rw [List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl, show 2 ^ (t + 1) - 2 + j - (2 ^ (t + 1) - 2) = j by omega]

theorem aTree_lvl (cols : List E) {t j : ℕ} (ht : t < 6) (hj : j < 2 ^ (t + 1)) :
    (aTree cols).getD (2 ^ (t + 1) - 2 + j) 0 = (eqLevels (fun k => cols.getD k 0) t).getD j 0 :=
  aTree_lvl_gen _ 6 t ht j hj

theorem eqLevels_lo (cc : ℕ → E) (t : ℕ) {i : ℕ} (hi : i < 2 ^ (t + 1)) :
    (eqLevels cc (t + 1)).getD i 0 = (eqLevels cc t).getD i 0 * (1 + cc (t + 1)) := by
  rw [eqLevels, List.getD_append _ _ _ _ (by simp [length_eqLevels, hi]),
    getD_map_lt (by rw [length_eqLevels]; exact hi)]

theorem eqLevels_hi (cc : ℕ → E) (t : ℕ) {i : ℕ} (hi : i < 2 ^ (t + 1)) :
    (eqLevels cc (t + 1)).getD (2 ^ (t + 1) + i) 0 = (eqLevels cc t).getD i 0 * cc (t + 1) := by
  rw [eqLevels, List.getD_append_right _ _ _ _ (by simp [length_eqLevels]), List.length_map, length_eqLevels,
    Nat.add_sub_cancel_left, getD_map_lt (by rw [length_eqLevels]; exact hi)]

theorem mem_trE {t i : ℕ} (ht : t < 5) (hi : i < 2 ^ (t + 1)) {x : Atom} (hx : x ∈ trE (t + 1) i) : x ∈ w2Tree := by
  simp only [w2Tree, trL, List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inr ⟨t, ht, Or.inr ⟨i, hi, hx⟩⟩

theorem mem_trL {t : ℕ} (ht : t < 5) {x : Atom}
    (hx : x ∈ [Atom.load (.n (trB (t + 1))) (.n 156) (t + 1), .const (.n (trB (t + 1) + 1)) (word 1 0),
      .add (.n (trB (t + 1) + 2)) (.n (trB (t + 1) + 1)) (.n (trB (t + 1)))]) : x ∈ w2Tree := by
  simp only [w2Tree, trL, List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inr ⟨t, ht, Or.inl hx⟩

section
variable {al : String → Bool} {s : NodeStatement} {w : NodeWitness} {cover : List E} {c : ℕ}

set_option linter.unusedTactic false in
/-- **The tree's words**: every load of `w2Tree` through `eq_col_tree` reads or writes its honest
word, every load through `col` its column challenge. -/
theorem w2_treeV (hl : (aLists s w).map List.length = aBufs w.children.length) (hc : c < 2 ^ 62)
    (hn : w.children.length ≤ 16) :
    (∀ x ∈ w2Tree, ∀ d off, x = .load d (.n 235) off → aV al s w cover c d = (aTree (aCols w)).getD off 0) ∧
      ∀ x ∈ w2Tree, ∀ d off, x = .load d (.n 156) off → aV al s w cover c d = (aCols w).getD off 0 := by
  obtain ⟨-, -, -, -, p156, p235, -⟩ := aV_ptrs (al := al) (s := s) (w := w) (cover := cover) (c := c)
  obtain ⟨-, -, f236, fcol, fprev⟩ := w2_fresh
  set cc : ℕ → E := fun k => (aCols w).getD k 0 with hcc
  have hcol : ∀ {d : V} {k : ℕ}, Atom.load d (.n 156) k ∈ w2Tree → Atom.load d (.n 156) k ∉ storesOf 6 aggP →
      k < 6 → aV al s w cover c d = cc k := fun hx hS hk => by
    rw [freshAt (q := 0) hl hc hn (mem_tree hx) hS (by rw [p156, Nat.add_zero]) (by norm_num)
      (by simpa [aBufs] using hk), Nat.zero_add]
    rfl
  have hprev : ∀ t < 5, ∀ i < 2 ^ (t + 1),
      aV al s w cover c (.n (trB (t + 1) + 3 + 3 * i)) = (eqLevels cc t).getD i 0 := fun t ht i hi => by
    have hx : Atom.load (.n (trB (t + 1) + 3 + 3 * i)) (.n 235) (2 ^ (t + 1) - 2 + i) ∈ w2Tree :=
      mem_trE ht hi (by simp [trE])
    have hb : 2 ^ (t + 1) - 2 + i < 126 := by
      have : 2 ^ (t + 1) ≤ 32 := by
        calc 2 ^ (t + 1) ≤ 2 ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
          _ = 32 := by norm_num
      omega
    rw [freshAt (q := 0) hl hc hn (mem_tree hx) (fprev t ht i hi) (by rw [p235, Nat.add_zero]) (by norm_num)
      (by simpa [aBufs] using hb), Nat.zero_add]
    exact aTree_lvl (aCols w) (by omega) hi
  have cst : ∀ {d : ℕ} {e : E}, Atom.const (.n d) e ∈ w2Tree → aV al s w cover c (.n d) = e := fun h =>
    aGood_const (aggArgs_length _ _) (mem_tree h)
  have add : ∀ {d x y : ℕ}, Atom.add (.n d) (.n x) (.n y) ∈ w2Tree →
      aV al s w cover c (.n d) = aV al s w cover c (.n x) + aV al s w cover c (.n y) := fun h =>
    aV_good (al := al) (s := s) (w := w) (cover := cover) (c := c) (mem_tree h)
  have hone : ∀ t < 5, aV al s w cover c (.n (trB (t + 1) + 2)) = 1 + cc (t + 1) := fun t ht => by
    rw [add (d := trB (t + 1) + 2) (x := trB (t + 1) + 1) (y := trB (t + 1)) (mem_trL ht (by simp)),
      cst (d := trB (t + 1) + 1) (e := word 1 0) (mem_trL ht (by simp)), word_one,
      hcol (mem_trL ht (by simp)) (fcol t ht) (by omega)]
  have mul : ∀ {d x y : ℕ}, Atom.mul (.n d) (.n x) (.n y) ∈ w2Tree → x < d → y < d →
      aV al s w cover c (.n d) = aV al s w cover c (.n x) * aV al s w cover c (.n y) := fun h hx hy =>
    aGood_mul (aggArgs_length _ _) (mem_tree h) hx hy
  have h236 : aV al s w cover c (.n 236) = cc 0 := hcol (by simp [w2Tree]) f236 (by norm_num)
  have h238 : aV al s w cover c (.n 238) = 1 + cc 0 := by
    rw [add (d := 238) (x := 237) (y := 236) (by simp [w2Tree]), cst (d := 237) (e := word 1 0) (by simp [w2Tree]),
      word_one, h236]
  have t0 : ∀ j < 2, (aTree (aCols w)).getD j 0 = (eqLevels cc 0).getD j 0 := fun j hj => by
    have := aTree_lvl (t := 0) (aCols w) (by norm_num) hj
    rwa [show 2 ^ (0 + 1) - 2 + j = j by norm_num] at this
  refine ⟨fun x hx d off he => ?_, fun x hx d off he => ?_⟩
  · subst he
    simp only [w2Tree, trL, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_flatMap,
      List.mem_range] at hx
    rcases hx with (h | h | h | h | h | h) | ⟨t, ht, (h | h | h) | ⟨i, hi, hx⟩⟩ <;>
      try (simp at h; done)
    · simp only [Atom.load.injEq] at h
      obtain ⟨rfl, -, rfl⟩ := h
      rw [h238, t0 0 (by norm_num), eqLevels, List.getD_cons_zero]
    · simp only [Atom.load.injEq] at h
      obtain ⟨rfl, -, rfl⟩ := h
      rw [h236, t0 1 (by norm_num), eqLevels, List.getD_cons_succ, List.getD_cons_zero]
    · simp only [trE, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with h | h | h | h | h <;>
        try (simp only [reduceCtorEq] at h; done)
      · simp only [Atom.load.injEq] at h
        obtain ⟨rfl, -, rfl⟩ := h
        rw [hprev t ht i hi, aTree_lvl (aCols w) (by omega) hi]
      · simp only [Atom.load.injEq] at h
        obtain ⟨rfl, -, rfl⟩ := h
        have hi' : i < 2 ^ (t + 1 + 1) := by rw [pow_succ]; omega
        rw [mul (d := trB (t + 1) + 4 + 3 * i) (x := trB (t + 1) + 3 + 3 * i) (y := trB (t + 1) + 2)
          (mem_trE ht hi (by simp [trE])) (by omega) (by omega), hprev t ht i hi, hone t ht,
          aTree_lvl (aCols w) (by omega) hi', eqLevels_lo cc t hi]
      · simp only [Atom.load.injEq] at h
        obtain ⟨rfl, -, rfl⟩ := h
        have hi' : 2 ^ (t + 1) + i < 2 ^ (t + 1 + 1) := by rw [pow_succ]; omega
        have hcol' : aV al s w cover c (.n (trB (t + 1))) = cc (t + 1) :=
          hcol (mem_trL ht (by simp)) (fcol t ht) (by omega)
        rw [mul (d := trB (t + 1) + 5 + 3 * i) (x := trB (t + 1) + 3 + 3 * i) (y := trB (t + 1))
          (mem_trE ht hi (by simp [trE])) (by omega) (by omega), hprev t ht i hi, hcol', Nat.add_assoc,
          aTree_lvl (aCols w) (by omega) hi', eqLevels_hi cc t hi]
  · subst he
    simp only [w2Tree, trL, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_flatMap,
      List.mem_range] at hx
    rcases hx with (h | h | h | h | h | h) | ⟨t, ht, (h | h | h) | ⟨i, hi, hx⟩⟩ <;>
      try (simp at h; done)
    · simp only [Atom.load.injEq] at h
      obtain ⟨rfl, -, rfl⟩ := h
      exact h236
    · simp only [Atom.load.injEq] at h
      obtain ⟨rfl, -, rfl⟩ := h
      exact hcol (mem_trL ht (by simp)) (fcol t ht) (by omega)
    · simp only [trE, List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with h | h | h | h | h <;> simp [Atom.load.injEq] at h

end

end
end LeanVM.Guest.Complete.Agg
