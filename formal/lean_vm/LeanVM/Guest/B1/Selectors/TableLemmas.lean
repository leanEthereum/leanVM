/-
  LeanVM.Guest.B1.Selectors.TableLemmas

  The entries of the selector tables: `eqTable`'s entry `u` is the eq weight of `u`'s bits,
  `gTable`'s the product of the shares at `u`'s bits, and `eqLevels` holds the table over the
  first `w` coordinates from `2^w - 2` on.
-/

module

public import LeanVM.Guest.B1.Selectors.BlockSelector

/-!
# The selector tables' entries

* `eqTable_getD`: for `u < 2^n`, entry `u` of the eq table over `n` coordinates is
  `Π_{t < n} (bit t of u ? zs_t : zs1_t)`;
* `gTable_getD`: entry `u` of the `g`-power table is `Π_{t < n} (bit t of u ? gs_t : 1)`;
* `eqLevels_getD`: the eq levels hold the table over the first `w ≥ 1` coordinates from
  `2^w - 2` on.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The factor of coordinate `t` at index `u`: `zs_t` at a set bit, `zs1_t` at a clear one. -/
def bitPick (u t : ℕ) (a b : E) : E := if u.testBit t then a else b

theorem tb_exists_snoc {l : List E} {n : ℕ} (h : l.length = n + 1) :
    ∃ l' x, l = l' ++ [x] ∧ l'.length = n := by
  have hne : l ≠ [] := fun e => by simp [e] at h
  refine ⟨l.dropLast, l.getLast hne, (List.dropLast_append_getLast hne).symm, ?_⟩
  rw [List.length_dropLast, h]; rfl

theorem tb_getD_append_left {l l' : List E} {n : ℕ} (h : n < l.length) :
    (l ++ l').getD n 0 = l.getD n 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]

theorem tb_getD_append_right {l l' : List E} {n : ℕ} (h : l.length ≤ n) :
    (l ++ l').getD n 0 = l'.getD (n - l.length) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h, ← List.getD_eq_getElem?_getD]

theorem tb_getD_map {f : E → E} {l : List E} {n : ℕ} (h : n < l.length) :
    (l.map f).getD n 0 = f (l.getD n 0) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h, List.getElem_map]

theorem tb_getD_snoc_last {l : List E} {x : E} : (l ++ [x]).getD l.length 0 = x := by
  rw [tb_getD_append_right le_rfl, Nat.sub_self]; rfl

theorem eqTable_snoc {zs zs1 : List E} (h : zs.length = zs1.length) (z z1 : E) :
    eqTable (zs ++ [z]) (zs1 ++ [z1]) =
      (eqTable zs zs1).map (· * z1) ++ (eqTable zs zs1).map (· * z) := by
  rw [eqTable, List.zip_append h, List.foldl_append]
  rfl

theorem gTable_snoc (gs : List E) (g : E) :
    gTable (gs ++ [g]) = gTable gs ++ (gTable gs).map (· * g) := by
  rw [gTable, List.foldl_append]
  rfl

theorem eqTable_length : ∀ {n : ℕ} {zs zs1 : List E}, zs.length = n → zs1.length = n →
    (eqTable zs zs1).length = 2 ^ n
  | 0, zs, zs1, h0, h1 => by
    rw [List.length_eq_zero_iff] at h0 h1; subst h0 h1; rfl
  | n + 1, zs, zs1, h0, h1 => by
    obtain ⟨zs', z, rfl, h0'⟩ := tb_exists_snoc h0
    obtain ⟨zs1', z1, rfl, h1'⟩ := tb_exists_snoc h1
    rw [eqTable_snoc (h0'.trans h1'.symm), List.length_append, List.length_map, List.length_map,
      eqTable_length h0' h1', pow_succ]
    ring

theorem gTable_length : ∀ {n : ℕ} {gs : List E}, gs.length = n → (gTable gs).length = 2 ^ n
  | 0, gs, h0 => by rw [List.length_eq_zero_iff] at h0; subst h0; rfl
  | n + 1, gs, h0 => by
    obtain ⟨gs', g, rfl, h0'⟩ := tb_exists_snoc h0
    rw [gTable_snoc, List.length_append, List.length_map, gTable_length h0', pow_succ]
    ring

theorem testBit_two_pow_add {n u t : ℕ} (_hu : u < 2 ^ n) (ht : t < n) :
    (2 ^ n + u).testBit t = u.testBit t := by
  rw [Nat.testBit_two_pow_add_gt ht]

theorem testBit_lt_two_pow {n u : ℕ} (hu : u < 2 ^ n) : u.testBit n = false :=
  Nat.testBit_lt_two_pow hu

theorem testBit_two_pow_add_self {n u : ℕ} (hu : u < 2 ^ n) : (2 ^ n + u).testBit n = true := by
  rw [Nat.testBit_two_pow_add_eq, testBit_lt_two_pow hu]; rfl

/-- **An eq table's entry**: for `u < 2^n`, `Π_{t < n} (bit t of u ? zs_t : zs1_t)`. -/
theorem eqTable_getD : ∀ {n : ℕ} {zs zs1 : List E}, zs.length = n → zs1.length = n →
    ∀ {u : ℕ}, u < 2 ^ n → (eqTable zs zs1).getD u 0 =
      ∏ t ∈ Finset.range n, bitPick u t (zs.getD t 0) (zs1.getD t 0)
  | 0, zs, zs1, h0, h1, u, hu => by
    rw [List.length_eq_zero_iff] at h0 h1
    subst h0 h1
    obtain rfl : u = 0 := by simpa using hu
    rfl
  | n + 1, zs, zs1, h0, h1, u, hu => by
    obtain ⟨zs', z, rfl, h0'⟩ := tb_exists_snoc h0
    obtain ⟨zs1', z1, rfl, h1'⟩ := tb_exists_snoc h1
    have hl : (eqTable zs' zs1').length = 2 ^ n := eqTable_length h0' h1'
    rw [eqTable_snoc (h0'.trans h1'.symm), Finset.prod_range_succ]
    have hget : ∀ t ∈ Finset.range n, ((zs' ++ [z]).getD t 0 = zs'.getD t 0) ∧
        ((zs1' ++ [z1]).getD t 0 = zs1'.getD t 0) := fun t ht => by
      have ht' := Finset.mem_range.mp ht
      exact ⟨tb_getD_append_left (by omega), tb_getD_append_left (by omega)⟩
    have hlast : (zs' ++ [z]).getD n 0 = z ∧ (zs1' ++ [z1]).getD n 0 = z1 := by
      refine ⟨?_, ?_⟩
      · rw [← h0']; exact tb_getD_snoc_last
      · rw [← h1']; exact tb_getD_snoc_last
    by_cases hlo : u < 2 ^ n
    · rw [tb_getD_append_left (by rw [List.length_map, hl]; exact hlo),
        tb_getD_map (by rw [hl]; exact hlo), eqTable_getD h0' h1' hlo]
      have hb : bitPick u n ((zs' ++ [z]).getD n 0) ((zs1' ++ [z1]).getD n 0) = z1 := by
        simp only [bitPick, testBit_lt_two_pow hlo, Bool.false_eq_true, ↓reduceIte, hlast.2]
      rw [hb]
      exact congrArg (· * z1) (Finset.prod_congr rfl (fun t ht => by
        rw [(hget t ht).1, (hget t ht).2]))
    · obtain ⟨v, rfl⟩ : ∃ v, u = 2 ^ n + v := ⟨u - 2 ^ n, by omega⟩
      have hv : v < 2 ^ n := by rw [pow_succ] at hu; omega
      rw [tb_getD_append_right (by rw [List.length_map, hl]; omega), List.length_map, hl,
        Nat.add_sub_cancel_left, tb_getD_map (by rw [hl]; exact hv), eqTable_getD h0' h1' hv]
      have hb : bitPick (2 ^ n + v) n ((zs' ++ [z]).getD n 0) ((zs1' ++ [z1]).getD n 0) = z := by
        simp only [bitPick, testBit_two_pow_add_self hv, ↓reduceIte, hlast.1]
      rw [hb]
      exact congrArg (· * z) (Finset.prod_congr rfl (fun t ht => by
        rw [(hget t ht).1, (hget t ht).2]
        simp only [bitPick, testBit_two_pow_add hv (Finset.mem_range.mp ht)]))

/-- **A `g`-power table's entry**: for `u < 2^n`, `Π_{t < n} (bit t of u ? gs_t : 1)`. -/
theorem gTable_getD : ∀ {n : ℕ} {gs : List E}, gs.length = n → ∀ {u : ℕ}, u < 2 ^ n →
    (gTable gs).getD u 0 = ∏ t ∈ Finset.range n, bitPick u t (gs.getD t 0) 1
  | 0, gs, h0, u, hu => by
    rw [List.length_eq_zero_iff] at h0
    subst h0
    obtain rfl : u = 0 := by simpa using hu
    rfl
  | n + 1, gs, h0, u, hu => by
    obtain ⟨gs', g, rfl, h0'⟩ := tb_exists_snoc h0
    have hl : (gTable gs').length = 2 ^ n := gTable_length h0'
    rw [gTable_snoc, Finset.prod_range_succ]
    have hget : ∀ t ∈ Finset.range n, (gs' ++ [g]).getD t 0 = gs'.getD t 0 := fun t ht =>
      tb_getD_append_left (by have := Finset.mem_range.mp ht; omega)
    have hlast : (gs' ++ [g]).getD n 0 = g := by rw [← h0']; exact tb_getD_snoc_last
    by_cases hlo : u < 2 ^ n
    · rw [tb_getD_append_left (by rw [hl]; exact hlo), gTable_getD h0' hlo]
      have hb : bitPick u n ((gs' ++ [g]).getD n 0) 1 = 1 := by
        simp only [bitPick, testBit_lt_two_pow hlo, Bool.false_eq_true, ↓reduceIte]
      rw [hb, mul_one]
      exact Finset.prod_congr rfl (fun t ht => by rw [hget t ht])
    · obtain ⟨v, rfl⟩ : ∃ v, u = 2 ^ n + v := ⟨u - 2 ^ n, by omega⟩
      have hv : v < 2 ^ n := by rw [pow_succ] at hu; omega
      rw [tb_getD_append_right (by rw [hl]; omega), hl, Nat.add_sub_cancel_left,
        tb_getD_map (by rw [hl]; exact hv), gTable_getD h0' hv]
      have hb : bitPick (2 ^ n + v) n ((gs' ++ [g]).getD n 0) 1 = g := by
        simp only [bitPick, testBit_two_pow_add_self hv, ↓reduceIte, hlast]
      rw [hb]
      exact congrArg (· * g) (Finset.prod_congr rfl (fun t ht => by
        rw [hget t ht]; simp only [bitPick, testBit_two_pow_add hv (Finset.mem_range.mp ht)]))

/-- Levels of lengths `2^(t+1)`, end to end: level `s` from `2^(s+1) - 2` on. -/
theorem flatMap_levels_getD (L : ℕ → List E) :
    ∀ {m : ℕ}, (∀ t < m, (L t).length = 2 ^ (t + 1)) → ∀ {s u : ℕ}, s < m → u < 2 ^ (s + 1) →
      ((List.range m).flatMap L).getD (2 ^ (s + 1) - 2 + u) 0 = (L s).getD u 0 := by
  have htot : ∀ m, (∀ t < m, (L t).length = 2 ^ (t + 1)) →
      ((List.range m).flatMap L).length = 2 ^ (m + 1) - 2 := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hL
      rw [List.range_succ, List.flatMap_append, List.length_append, ih (fun t ht => hL t (by omega)),
        List.flatMap_singleton, hL m (by omega), pow_succ 2 (m + 1)]
      have : 2 ≤ 2 ^ (m + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  intro m
  induction m with
  | zero => intro _ s u hs; omega
  | succ m ih =>
    intro hL s u hs hu
    have hL' : ∀ t < m, (L t).length = 2 ^ (t + 1) := fun t ht => hL t (by omega)
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    by_cases hsm : s < m
    · have hlt : 2 ^ (s + 1) - 2 + u < ((List.range m).flatMap L).length := by
        rw [htot m hL']
        have : 2 ^ (s + 1 + 1) ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [pow_succ] at this
        omega
      rw [tb_getD_append_left hlt, ih hL' hsm hu]
    · obtain rfl : s = m := by omega
      rw [tb_getD_append_right (by rw [htot s hL']; omega), htot s hL', Nat.add_sub_cancel_left]

/-- **The eq levels**: from `2^w - 2` on, `w ≥ 1`, the table over the first `w` coordinates. -/
theorem eqLevels_getD {zs zs1 : List E} (h : zs.length = zs1.length) {w u : ℕ} (hw1 : 1 ≤ w)
    (hw : w ≤ zs.length) (hu : u < 2 ^ w) :
    (eqLevels zs zs1).getD (2 ^ w - 2 + u) 0 =
      ∏ t ∈ Finset.range w, bitPick u t (zs.getD t 0) (zs1.getD t 0) := by
  obtain ⟨s, rfl⟩ : ∃ s, w = s + 1 := ⟨w - 1, by omega⟩
  rw [eqLevels, flatMap_levels_getD _ (fun t ht => ?_) (by omega) hu]
  · rw [eqTable_getD (n := s + 1) (by simp; omega) (by simp; omega) hu]
    refine Finset.prod_congr rfl fun t ht => ?_
    have ht' := Finset.mem_range.mp ht
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt ht',
      List.getElem?_take_of_lt ht', ← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
  · exact eqTable_length (by simp [List.length_take]; omega) (by simp [List.length_take]; omega)

end
end LeanVM.Guest.B1.Tables
