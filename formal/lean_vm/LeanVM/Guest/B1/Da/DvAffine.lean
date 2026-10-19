/-
  LeanVM.Guest.B1.Da.DvAffine

  `da_verify`'s words, affinely in its row count: a constant per matrix and a slope per row.
-/

module

public import LeanVM.Guest.B1.Da.VerifyAt

/-!
# `da_verify`'s words, affinely

`dv_tot_affine`: `dvTot fs r ≤ dvWA fs + dvWB fs * r` for every row count `r`. The padded count
`N = nPad r` is at most `2r + 1`, the gap at most `r + 1`, and a tree's level loops are at most
`2N` frames of the largest level loop (`dvLvM`), so each column costs its row loop's and
`da_verify_cell`'s frames per row and a constant.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Guest.Core

@[expose] public section

variable (fs : String → ℕ)

/-- The largest level loop's frame, and the largest tree's. -/
def dvLvM : ℕ := max (fs "") ((lvNames.flatten.map fs).foldr max 0)
def dvDlM : ℕ := max (fs "") ((dlNames.map fs).foldr max 0)
/-- The larger vector cell's frame. -/
def dvVxM : ℕ := max (fs (vxName true)) (fs (vxName false))

/-- A column's constant and slope, by store. -/
def dvColA (s : Bool) : ℕ :=
  fs (colName s) + 4 + fs "da_vector_dispatch" + dvVxM fs + fs (rowName s) + 2 * fs (gapName s) +
    dvDlM fs + 2 * dvLvM fs
def dvColB (s : Bool) : ℕ := 8 + fs (rowName s) + fs "da_verify_cell" + fs (gapName s) + 4 * dvLvM fs

/-- **`da_verify`'s constant per matrix.** -/
def dvWA : ℕ :=
  fs "da_verify" + 902 + fs "da_row_shape" + fs "__loop88" + fs "__loop89" + fs "__loop92" + fs "__loop93" +
    dlTot fs 7 + 2 * fs "__loop94" + dvDlM fs + 2 * dvLvM fs +
    (65 * fs (colLoopName true) + 64 * dvColA fs true) + (65 * fs (colLoopName false) + 64 * dvColA fs false)

/-- **`da_verify`'s slope per row.** -/
def dvWB : ℕ :=
  395 + fs "__loop88" + fs "__loop89" + fs "__loop92" + fs "__loop93" + fs "__loop94" + 4 * dvLvM fs +
    64 * dvColB fs true + 64 * dvColB fs false

theorem dv_foldr_max : ∀ {l : List ℕ} {x : ℕ}, x ∈ l → x ≤ l.foldr max 0
  | [], _, h => absurd h (by simp)
  | y :: l, x, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (dv_foldr_max h) (le_max_right _ _)

theorem dv_lvName_le (k l : ℕ) : fs (lvName k l) ≤ dvLvM fs := by
  unfold lvName dvLvM
  by_cases hk : k < lvNames.length
  · by_cases hl : l < (lvNames.getD k []).length
    · rw [List.getD_eq_getElem _ _ hl]
      refine le_trans (dv_foldr_max (List.mem_map.mpr ⟨_, List.mem_flatten.mpr ⟨_, ?_, List.getElem_mem hl⟩, rfl⟩))
        (le_max_right _ _)
      rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem _
    · rw [List.getD_eq_default (lvNames.getD k []) "" (by omega)]; exact le_max_left _ _
  · rw [List.getD_eq_default lvNames [] (by omega)]; simp only [List.getD_nil]; exact le_max_left _ _

theorem dv_dlName_le (k : ℕ) : fs (dlNames.getD k "") ≤ dvDlM fs := by
  unfold dvDlM
  by_cases hk : k < dlNames.length
  · rw [List.getD_eq_getElem _ _ hk]
    exact le_trans (dv_foldr_max (List.mem_map.mpr ⟨_, List.getElem_mem hk, rfl⟩)) (le_max_right _ _)
  · rw [List.getD_eq_default dlNames "" (by omega)]; exact le_max_left _ _

theorem dv_sum_affine (c : ℕ) (f : ℕ → ℕ) : ∀ L : List ℕ,
    (L.map fun l => c * (f l + 1)).sum = c * ((L.map f).sum + L.length)
  | [] => rfl
  | x :: L => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, dv_sum_affine c f L]
    ring

theorem dv_geom : ∀ k : ℕ, ((List.range k).map fun l => 2 ^ (k - l - 1)).sum + 1 = 2 ^ k
  | 0 => rfl
  | k + 1 => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons]
    have ih := dv_geom k
    have e : ((List.range k).map ((fun l => 2 ^ (k + 1 - l - 1)) ∘ Nat.succ)) =
        (List.range k).map fun l => 2 ^ (k - l - 1) := by
      refine List.map_congr_left fun l _ => ?_
      simp only [Function.comp_apply]
      congr 1; omega
    rw [e, show k + 1 - 0 - 1 = k by omega, pow_succ]
    omega

theorem dv_dlTot_le (k : ℕ) : dlTot fs k ≤ dvDlM fs + dvLvM fs * (2 ^ k - 1 + k) := by
  unfold dlTot
  have h1 := dv_dlName_le fs k
  have h2 : ((List.range k).map fun l => lvTot fs (lvName k l) (2 ^ (k - l - 1)) 0).sum ≤
      ((List.range k).map fun l => dvLvM fs * (2 ^ (k - l - 1) + 1)).sum := by
    refine List.sum_le_sum fun l _ => ?_
    unfold lvTot
    have := dv_lvName_le fs k l
    rw [Nat.sub_zero, Nat.mul_add, Nat.mul_one, Nat.mul_comm]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ this) this
  have h3 : ((List.range k).map fun l => dvLvM fs * (2 ^ (k - l - 1) + 1)).sum =
      dvLvM fs * (((List.range k).map fun l => 2 ^ (k - l - 1)).sum + k) := by
    rw [dv_sum_affine, List.length_range]
  have h4 := dv_geom k
  rw [h3] at h2
  have h5 : ((List.range k).map fun l => 2 ^ (k - l - 1)).sum = 2 ^ k - 1 := by omega
  rw [h5] at h2
  omega

theorem dv_nPad_le (r : ℕ) : LeanDa.nPad r ≤ 2 * r + 1 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rfl
  · have := ((logPad_iff (lp := LeanDa.logPad r) hr).mp rfl).2
    unfold LeanDa.nPad; omega

theorem dv_logPad_le (r : ℕ) : LeanDa.logPad r ≤ LeanDa.nPad r := by
  unfold LeanDa.nPad
  exact le_of_lt (Nat.lt_two_pow_self)

/-- A tree's words at the padded count. -/
theorem dv_dlTot_pad (r : ℕ) : dlTot fs (LeanDa.logPad r) ≤ dvDlM fs + dvLvM fs * (4 * r + 2) := by
  have h := dv_dlTot_le fs (LeanDa.logPad r)
  have h1 := dv_nPad_le r
  have h2 := dv_logPad_le r
  have hN : 2 ^ LeanDa.logPad r = LeanDa.nPad r := rfl
  rw [hN] at h
  exact le_trans h (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _)

theorem dv_colTot_le (s : Bool) (b r : ℕ) :
    colTot fs s b r (LeanDa.nPad r) (LeanDa.logPad r) ≤ dvColA fs s + dvColB fs s * r := by
  have hN := dv_nPad_le r
  have hdl := dv_dlTot_pad fs r
  have hvx : fs (vxName (decide (b = 127))) ≤ dvVxM fs := by
    unfold dvVxM; cases decide (b = 127)
    · exact le_max_right _ _
    · exact le_max_left _ _
  have hgap : (if LeanDa.nPad r - r = 0 then fs (gapName s) else gapTot fs s (LeanDa.nPad r - r) 0) ≤
      (r + 2) * fs (gapName s) := by
    split_ifs
    · nlinarith
    · unfold gapTot; rw [Nat.sub_zero]
      have : LeanDa.nPad r - r ≤ r + 1 := by omega
      nlinarith
  unfold colTot rowTot dvColA dvColB
  rw [Nat.sub_zero]
  have e1 : 4 * LeanDa.nPad r ≤ 4 + 8 * r := by omega
  have e2 : dvLvM fs * (4 * r + 2) = 2 * dvLvM fs + 4 * dvLvM fs * r := by ring
  have e3 : (r + 2) * fs (gapName s) = 2 * fs (gapName s) + fs (gapName s) * r := by ring
  have e4 : (8 + fs (rowName s) + fs "da_verify_cell" + fs (gapName s) + 4 * dvLvM fs) * r =
      8 * r + r * (fs (rowName s) + fs "da_verify_cell") + fs (gapName s) * r + 4 * dvLvM fs * r := by ring
  omega

theorem dv_clTot_le (s : Bool) (r : ℕ) :
    ∀ d j, j + d = clHi s → clTot fs s r (LeanDa.nPad r) (LeanDa.logPad r) j ≤
      (d + 1) * fs (colLoopName s) + d * (dvColA fs s + dvColB fs s * r)
  | d, j, h => by
    unfold clTot
    rw [show clHi s - j = d by omega]
    have : ((List.range d).map fun i => fs (colLoopName s) + colTot fs s (j + i) r (LeanDa.nPad r)
        (LeanDa.logPad r)).sum ≤ ((List.range d).map fun _ => fs (colLoopName s) +
          (dvColA fs s + dvColB fs s * r)).sum :=
      List.sum_le_sum fun i _ => Nat.add_le_add_left (dv_colTot_le fs s _ r) _
    rw [List.map_const', List.sum_replicate, List.length_range, smul_eq_mul] at this
    nlinarith

/-- **`da_verify`'s words are affine in its row count.** -/
theorem dv_tot_affine (r : ℕ) : dvTot fs r ≤ dvWA fs + dvWB fs * r := by
  have hN := dv_nPad_le r
  have hdl := dv_dlTot_pad fs r
  have c1 := dv_clTot_le fs true r 64 0 rfl
  have c2 := dv_clTot_le fs false r 64 64 rfl
  have h94 : (if LeanDa.nPad r - r = 0 then fs "__loop94" else (LeanDa.nPad r - r) * fs "__loop94" +
      fs "__loop94") ≤ (r + 2) * fs "__loop94" := by
    split_ifs
    · nlinarith
    · have : LeanDa.nPad r - r ≤ r + 1 := by omega
      nlinarith
  unfold dvTot dvKids dvSizes dvWA dvWB
  simp only [List.sum_cons, List.sum_nil, List.foldr, Nat.sub_zero]
  have e1 : (dvWA fs - dvWA fs) = 0 := Nat.sub_self _
  clear e1
  have e2 : dvLvM fs * (4 * r + 2) = 2 * dvLvM fs + 4 * (dvLvM fs * r) := by ring
  have e3 : (r + 2) * fs "__loop94" = 2 * fs "__loop94" + fs "__loop94" * r := by ring
  have e4 : (64 + 1) * fs (colLoopName true) + 64 * (dvColA fs true + dvColB fs true * r) =
      65 * fs (colLoopName true) + 64 * dvColA fs true + 64 * dvColB fs true * r := by ring
  have e5 : (64 + 1) * fs (colLoopName false) + 64 * (dvColA fs false + dvColB fs false * r) =
      65 * fs (colLoopName false) + 64 * dvColA fs false + 64 * dvColB fs false * r := by ring
  have e6 : (395 + fs "__loop88" + fs "__loop89" + fs "__loop92" + fs "__loop93" + fs "__loop94" +
      4 * dvLvM fs + 64 * dvColB fs true + 64 * dvColB fs false) * r =
      395 * r + r * fs "__loop88" + r * fs "__loop89" + r * fs "__loop92" + r * fs "__loop93" +
        fs "__loop94" * r + 4 * (dvLvM fs * r) + 64 * (dvColB fs true * r) + 64 * (dvColB fs false * r) := by ring
  omega

end
end LeanVM.Guest.B1.Digest
