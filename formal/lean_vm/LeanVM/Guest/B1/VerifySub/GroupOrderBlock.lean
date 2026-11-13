/-
  LeanVM.Guest.B1.VerifySub.GroupOrderBlock

  `Hints.blockGroupOrder` is `verify_tables`' honest group order (`vtGOrdW`): each side's blocks sorted by their offsets, by group, are its groups in `stackOffsets`' order (`vtOrd`), the pull side's as the push side's.
-/

module

public import LeanVM.Guest.B1.VerifySub.GroupOrderCol
public import LeanVM.Guest.B1.Tables.Vt.SpecLayout
public import LeanVM.Guest.B1.Tables.Vt.Sels
public import LeanVM.Guest.B1.Tables.VtC.SSort

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Guest.Value LeanVM.Protocol.Verifier LeanVM.Guest.B1.Tables

@[expose] public section

theorem pushKeys (rows : List ℕ) : [0, 1, 2] ++ (vtPushBlocks rows).map Hints.blockKey = keysP := by
  have e : (vtPushBlocks rows).map Hints.blockKey = (vtPushBlocks []).map Hints.blockKey := by
    simp only [vtPushBlocks, List.map_flatten, List.map_ofFn, Function.comp_def, List.map_map, Hints.blockKey]
  rw [e]
  decide +kernel

theorem pullKeys (rows : List ℕ) : [0, 1, 2] ++ (vtPullBlocks rows).map Hints.blockKey = keysP := by
  have e : (vtPullBlocks rows).map Hints.blockKey = (vtPullBlocks []).map Hints.blockKey := by
    simp only [vtPullBlocks, List.map_flatten, List.map_ofFn, Function.comp_def, List.map_map, Hints.blockKey]
  rw [e]
  decide +kernel

theorem countKeys (rows : List ℕ) : (vtCountBlocks rows).map Hints.blockKey = keysC := by
  have e : (vtCountBlocks rows).map Hints.blockKey = (vtCountBlocks []).map Hints.blockKey := by
    simp only [vtCountBlocks, List.map_flatten, List.map_ofFn, Function.comp_def, List.map_map, Hints.blockKey]
  rw [e]
  simp only [vtCountBlocks, vt_countColumns]
  decide +kernel

/-- A side's groups' run heads, its blocks sorted by offset. -/
theorem runHeads_blockOrder (κs : List ℕ) {m : ℕ} (st kg : ℕ → ℕ) (c : ℕ) (grp : ℕ → ℕ) (hst0 : st 0 = 0)
    (hstm : st m = κs.length) (hmono : ∀ j < m, st j < st (j + 1))
    (hκ : ∀ j < m, ∀ x, st j ≤ x → x < st (j + 1) → κs.getD x 0 = kg j)
    (hgrp : ∀ j < m, ∀ x, st j ≤ x → x < st (j + 1) → grp x = c + j) :
    Hints.runHeads ((Hints.blockOrder κs).map grp) = ((List.range m).mergeSort (stackLe kg)).map (c + ·) :=
  runHeads_sortOff κs st kg c grp (fun i => (stackOffsets κs).1.getD i 0) hst0 hstm hmono hκ hgrp fun _ _ => rfl

theorem vtSizesP_length (lm : ℕ) (τ : ℕ → ℕ) : (vtSizesP lm τ).length = 54 := by
  simp [vtSizesP, vtPushPadData_length]

theorem vtSizesC_length (τ : ℕ → ℕ) : (vtSizesC τ).length = 45 := by
  simp [vtSizesC, vtCountPadData_length]

theorem bgs_le {j : ℕ} (hj : j < 9) : bgs (j + 1) ≤ 54 :=
  st_le_of bgs bgs_lt (show j + 1 ≤ 9 by omega) le_rfl

theorem bgsC_le {j : ℕ} (hj : j < 6) : bgsC (j + 1) ≤ 45 :=
  st_le_of bgsC bgsC_lt (show j + 1 ≤ 6 by omega) le_rfl

theorem kapP_grp (lm : ℕ) (τ : ℕ → ℕ) : ∀ j < 9, ∀ x, bgs j ≤ x → x < bgs (j + 1) →
    (vtSizesP lm τ).getD x 0 = vtKg lm τ (vtG0 0 + j) := by
  intro j hj x h1 h2
  have hx : x < 54 := lt_of_lt_of_le h2 (bgs_le hj)
  obtain ⟨e1, e2⟩ := srcP_eq j hj x hx h1 h2
  rw [← vt_kapP lm τ hx, show vtG0 0 + j = j by simp [vtG0], vtKg, vtKap, vtKap, e1, e2]
  rfl

theorem kapC_grp (lm : ℕ) (τ : ℕ → ℕ) : ∀ j < 6, ∀ x, bgsC j ≤ x → x < bgsC (j + 1) →
    (vtSizesC τ).getD x 0 = vtKg lm τ (vtG0 2 + j) := by
  intro j hj x h1 h2
  have hx : x < 45 := lt_of_lt_of_le h2 (bgsC_le hj)
  obtain ⟨e1, e2⟩ := srcC_eq j hj x hx h1 h2
  rw [← vt_kapC lm τ hx, show vtG0 2 + j = 18 + j by simp [vtG0], vtKg, vtKap, vtKap, e1, e2]
  rfl

theorem map_range_getD_ord (l : List ℕ) (g : ℕ → E) : (List.range l.length).map (fun i => g (l.getD i 0)) = l.map g :=
  List.ext_getElem (by simp) fun i h1 h2 => by
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem _ _ (by simpa using h1)]

theorem vtOrd_lt {lm : ℕ} {τ : ℕ → ℕ} {s : ℕ} : ∀ j ∈ vtOrd lm τ s, j < vtGm s := fun _ hj =>
  List.mem_range.mp (vtOrd_perm.subset hj)

/-- `vtGOrdW` by sides. -/
theorem vtGOrdW_eq (lm : ℕ) (τ : ℕ → ℕ) :
    vtGOrdW lm τ = (vtOrd lm τ 0).map (gen ^ ·) ++ (vtOrd lm τ 0).map (fun j => gen ^ (9 + j)) ++
      (vtOrd lm τ 2).map (fun j => gen ^ (18 + j)) := by
  have l0 : (vtOrd lm τ 0).length = 9 := vtOrd_length
  have l2 : (vtOrd lm τ 2).length = 6 := vtOrd_length
  rw [vtGOrdW, show 24 = 9 + (9 + 6) from rfl, List.range_add, List.range_add, List.map_append,
    List.map_map, List.map_append, List.map_map, ← List.append_assoc]
  refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) ?_ ?_) ?_
  · conv_rhs => rw [← map_range_getD_ord, l0]
    refine List.map_congr_left fun i hi => ?_
    have := List.mem_range.mp hi
    simp only [this, ↓reduceIte, vtPi]
  · conv_rhs => rw [← map_range_getD_ord, l0]
    refine List.map_congr_left fun i hi => ?_
    have := List.mem_range.mp hi
    simp only [Function.comp_apply, show ¬ 9 + i < 9 by omega, show 9 + i < 18 by omega, ↓reduceIte, vtPi,
      Nat.add_sub_cancel_left]
  · conv_rhs => rw [← map_range_getD_ord, l2]
    refine List.map_congr_left fun i hi => ?_
    have := List.mem_range.mp hi
    simp only [Function.comp_apply, show ¬ 9 + (9 + i) < 9 by omega, show ¬ 9 + (9 + i) < 18 by omega, ↓reduceIte,
      vtPi, show 9 + (9 + i) - 18 = i by omega]

/-- **`blockGroupOrder` is `verify_tables`' honest group order.** -/
theorem blockGroupOrder_eq {bc : List K} (hbc : bc.length = 2 ^ 23) (lm : ℕ) {rows : List ℕ}
    (hr : rows.length = 6) : Hints.blockGroupOrder (layoutOf bc lm rows) = vtGOrdW lm (vtHt rows) := by
  obtain ⟨hpu, hpl, hco⟩ := vt_layout_blocks bc lm hr
  have sP : [0, lm, 19] ++ (vtPushBlocks rows).map (·.logRows) = vtSizesP lm (vtHt rows) := vt_sizes_push lm
  have sQ : [0, lm, 19] ++ (vtPullBlocks rows).map (·.logRows) = vtSizesP lm (vtHt rows) := vt_sizes_pull lm
  have sC : (vtCountBlocks rows).map (·.logRows) = vtSizesC (vtHt rows) := vt_sizes_count
  obtain ⟨k0, k9⟩ := runHeads_keysP
  have hP := runHeads_blockOrder (vtSizesP lm (vtHt rows)) (m := 9) bgs
    (fun j => vtKg lm (vtHt rows) (vtG0 0 + j)) 0 ((Hints.runGroups 0 none keysP).getD · 0) bgs_zero
    (by rw [vtSizesP_length]; rfl) bgs_lt (kapP_grp lm _)
    fun j hj x h1 h2 => (groupsP_eq j hj x (lt_of_lt_of_le h2 (bgs_le hj)) h1 h2).1
  have hQ := runHeads_blockOrder (vtSizesP lm (vtHt rows)) (m := 9) bgs
    (fun j => vtKg lm (vtHt rows) (vtG0 0 + j)) 9 ((Hints.runGroups 9 none keysP).getD · 0) bgs_zero
    (by rw [vtSizesP_length]; rfl) bgs_lt (kapP_grp lm _)
    fun j hj x h1 h2 => (groupsP_eq j hj x (lt_of_lt_of_le h2 (bgs_le hj)) h1 h2).2
  have hC := runHeads_blockOrder (vtSizesC (vtHt rows)) (m := 6) bgsC
    (fun j => vtKg lm (vtHt rows) (vtG0 2 + j)) 18 ((Hints.runGroups 18 none keysC).getD · 0) bgsC_zero
    (by rw [vtSizesC_length]; rfl) bgsC_lt (kapC_grp lm _)
    fun j hj x h1 h2 => groupsC_eq j hj x (lt_of_lt_of_le h2 (bgsC_le hj)) h1 h2
  have o0 : (List.range 9).mergeSort (stackLe fun j => vtKg lm (vtHt rows) (vtG0 0 + j)) = vtOrd lm (vtHt rows) 0 :=
    rfl
  have o2 : (List.range 6).mergeSort (stackLe fun j => vtKg lm (vtHt rows) (vtG0 2 + j)) =
    vtOrd lm (vtHt rows) 2 := rfl
  rw [o0] at hP hQ
  rw [o2] at hC
  dsimp only [Hints.blockGroupOrder]
  rw [vt_layout_logMemory, vt_layout_logBytecode bc lm rows hbc, hpu, hpl, hco, sP, sQ, sC, pushKeys, pullKeys,
    countKeys]
  simp only [List.foldl_cons, List.foldl_nil, List.nil_append, k0, Nat.zero_add]
  rw [k9, hP, hQ, hC, vtGOrdW_eq, List.map_map, List.map_map, List.map_map]
  have hc : ∀ (s c : ℕ), c + vtGm s ≤ 24 → (vtOrd lm (vtHt rows) s).map (Hints.count ∘ (c + ·)) =
      (vtOrd lm (vtHt rows) s).map (fun j => gen ^ (c + j)) := fun s c hcs =>
    List.map_congr_left fun j hj => by
      have := vtOrd_lt j hj
      show Hints.count (c + j) = gen ^ (c + j)
      exact count_eq_gen (by omega)
  rw [hc 0 0 (by simp [vtGm]), hc 0 9 (by simp [vtGm]), hc 2 18 (by simp [vtGm])]
  simp only [Nat.zero_add]

/-- **`colGroupOrder` is `certify_placement`'s honest group order**, on `layoutOf`. -/
theorem colGroupOrder_layoutOf {bc : List K} (hbc : bc.length = 2 ^ 23) (lm : ℕ) {rows : List ℕ}
    (hr : rows.length = 6) :
    Hints.colGroupOrder (layoutOf bc lm rows) = (cpGOrd lm (tableHeightsOf rows)).map (gen ^ ·) := by
  refine colGroupOrder_eq (vt_tableHeightsOf_length hr) ?_
  show (placementsOf (columnKappas lm (Nat.log2 bc.length - busBits) (tableHeightsOf rows))).1 = _
  rw [hbc, Nat.log2_two_pow]
  rfl

end
end LeanVM.Guest.B1.VerifySub
