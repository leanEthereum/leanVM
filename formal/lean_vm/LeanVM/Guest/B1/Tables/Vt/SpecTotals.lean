/-
  LeanVM.Guest.B1.Tables.Vt.SpecTotals

  The specification's bus result on the layout of the announced sizes: each side's total (the
  tree value, the framework blocks, the unused leaves, the padding rows) and each table's form
  on each side, in terms of the selectors and the guest's sums.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.SpecBus
public import LeanVM.Protocol.EndToEnd.Complete.BusTables

/-!
# The bus result's totals and forms

On `layoutOf bc lm rows` (a bytecode of `2^23` words, six row counts), with the selectors of the
push side's blocks `a₀, a₁, a₂` (framework) and `S c` (table blocks, by the guest's copy cell `c`)
and the count side's `S c`:

* `vt_total0`, `vt_total1`, `vt_total2`: the sides' totals;
* `vt_forms0`, `vt_forms1`, `vt_forms2`: table `t`'s form on each side, at any row, is the guest's
  `vtSideVal` of the table's selectors and baked terms.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (refSide refSide_eq refSideC sideSizes sideSels blockSel
  blockVal padSum accFold accFold_spec accumulateSide_fst accumulateSide_snd)

@[expose] public section

section
variable (bc : List K) (lm : ℕ) (rows : List ℕ)

theorem vt_pushBlocks_length (rows : List ℕ) : (vtPushBlocks rows).length = 51 := by
  have := congrArg List.length (vt_push_owners rows); simpa [vtPushPadData_length] using this

theorem vt_pullBlocks_length (rows : List ℕ) : (vtPullBlocks rows).length = 51 := by
  have := congrArg List.length (vt_pull_owners rows); simpa [vtPushPadData_length] using this

theorem vt_countBlocks_length (rows : List ℕ) : (vtCountBlocks rows).length = 45 := by
  have := congrArg List.length (vt_count_owners rows); simpa [vtCountPadData_length] using this

/-- The table blocks' selectors, through the guest's copy cells. -/
theorem vt_tSels {fw : List ℕ} {blocks : List BusBlock} {p : List E} {k : ℕ} {sizes : List ℕ}
    (hsz : sideSizes fw blocks = sizes) {data : List (ℕ × ℕ × ℕ × List (ℕ × ℕ))}
    (hl : blocks.length = data.length) (S : ℕ → E)
    (hS : ∀ i < data.length, S (data.getD i default).2.2.1 = blockSel sizes p.length (k + i) p) :
    sideSels fw blocks p k blocks.length = data.map fun x ↦ S x.2.2.1 := by
  apply List.ext_getElem (by simp [sideSels, hl])
  intro i h1 h2
  simp only [sideSels, List.getElem_map, List.getElem_range, hsz]
  have hi : i < data.length := by simpa using h2
  rw [← hS i hi, List.getD_eq_getElem _ _ hi]

variable {bc lm rows}

theorem vt_foldl_add (l : List E) (c : E) : l.foldl (· + ·) c = c + l.sum := by
  induction l generalizing c with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.sum_cons]; ring

/-- **The push side's total.** -/
theorem vt_total0 (hbc : bc.length = 2 ^ 23) (weights : List E) (β : E) (p memory : List E)
    (bv tv : E) (a0 a1 a2 : E) (S pw : ℕ → E)
    (h0 : blockSel (vtSizesP lm (vtHt rows)) p.length 0 p = a0)
    (h1 : blockSel (vtSizesP lm (vtHt rows)) p.length 1 p = a1)
    (h2 : blockSel (vtSizesP lm (vtHt rows)) p.length 2 p = a2)
    (hS : ∀ i < 51, S (vtPushPadData.getD i default).2.2.1 =
      blockSel (vtSizesP lm (vtHt rows)) p.length (3 + i) p)
    (hpw : ∀ t < 6, paddingWeight (p.take (vtHt rows t)) (vtRw rows t) = pw t)
    (hr : rows.length = 6) :
    (vtAcc0 (layoutOf bc lm rows) weights β p memory bv tv).2 =
      tv + (a0 * (β + (vtFpPush (layoutOf bc lm rows) weights p memory bv).getD 0 0) +
        a1 * (β + (vtFpPush (layoutOf bc lm rows) weights p memory bv).getD 1 0) +
        a2 * (β + (vtFpPush (layoutOf bc lm rows) weights p memory bv).getD 2 0)) +
      (a0 + a1 + a2 + (vtPushPadData.map fun x ↦ S x.2.2.1).sum + 1) +
      vtPadSum S pw (weights.getD · 0) (β + 1) vtPushPadData := by
  have hL := (vt_layout_blocks bc lm hr).1
  rw [vtAcc0, hL, vt_layout_logBytecode bc lm rows hbc, vt_layout_logMemory,
    accumulateSide_snd]
  have hts := vt_tSels (fw := [0, lm, 19]) (blocks := vtPushBlocks rows) (p := p)
    (data := vtPushPadData) (k := 3) (vt_sizes_push lm)
    (by rw [vt_pushBlocks_length, vtPushPadData_length]) S (by rw [vtPushPadData_length]; exact hS)
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
  rw [hts, vt_padSum_push rows p β _ S pw hpw]
  have hfw : sideSels [0, lm, 19] (vtPushBlocks rows) p 0 3 = [a0, a1, a2] := by
    simp only [sideSels, vt_sizes_push]
    simp [List.range_succ, h0, h1, h2]
  rw [hfw, vtFpPush, fingerprints]
  simp only [dot, sumE, List.map_cons, List.map_nil, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.foldl_cons, List.foldl_nil, List.cons_append, List.nil_append, List.getD_cons_zero,
    List.getD_cons_succ]
  simp only [vt_foldl_add]
  ring

/-- **The pull side's total.** -/
theorem vt_total1 (hbc : bc.length = 2 ^ 23) (weights : List E) (β : E) (p memory : List E)
    (mf bf bv tv0 tv : E) (a0 a1 a2 : E) (S pw : ℕ → E)
    (h0 : blockSel (vtSizesP lm (vtHt rows)) p.length 0 p = a0)
    (h1 : blockSel (vtSizesP lm (vtHt rows)) p.length 1 p = a1)
    (h2 : blockSel (vtSizesP lm (vtHt rows)) p.length 2 p = a2)
    (hS : ∀ i < 51, S (vtPushPadData.getD i default).2.2.1 =
      blockSel (vtSizesP lm (vtHt rows)) p.length (3 + i) p)
    (hpw : ∀ t < 6, paddingWeight (p.take (vtHt rows t)) (vtRw rows t) = pw t)
    (hr : rows.length = 6) :
    (vtAcc1 (layoutOf bc lm rows) weights β p memory mf bf bv tv0 tv).2 =
      tv + (a0 * (β + (vtFpPull (layoutOf bc lm rows) weights p memory mf bf bv).getD 0 0) +
        a1 * (β + (vtFpPull (layoutOf bc lm rows) weights p memory mf bf bv).getD 1 0) +
        a2 * (β + (vtFpPull (layoutOf bc lm rows) weights p memory mf bf bv).getD 2 0)) +
      (a0 + a1 + a2 + (vtPushPadData.map fun x ↦ S x.2.2.1).sum + 1) +
      vtPadSum S pw (weights.getD · 0) (β + 1) vtPushPadData := by
  have hL := (vt_layout_blocks bc lm hr).2.1
  rw [vtAcc1, hL, vt_layout_logBytecode bc lm rows hbc, vt_layout_logMemory,
    accumulateSide_snd]
  have hts := vt_tSels (fw := [0, lm, 19]) (blocks := vtPullBlocks rows) (p := p)
    (data := vtPushPadData) (k := 3) (vt_sizes_pull lm)
    (by rw [vt_pullBlocks_length, vtPushPadData_length]) S (by rw [vtPushPadData_length]; exact hS)
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
  rw [hts, vt_padSum_pull rows p β _ S pw hpw]
  have hfw : sideSels [0, lm, 19] (vtPullBlocks rows) p 0 3 = [a0, a1, a2] := by
    simp only [sideSels, vt_sizes_pull]
    simp [List.range_succ, h0, h1, h2]
  rw [hfw, vtFpPull, fingerprints]
  simp only [dot, sumE, List.map_cons, List.map_nil, List.zipWith_cons_cons, List.zipWith_nil_left,
    List.foldl_cons, List.foldl_nil, List.cons_append, List.nil_append, List.getD_cons_zero,
    List.getD_cons_succ]
  simp only [vt_foldl_add]
  ring

/-- **The count side's total.** -/
theorem vt_total2 (weights : List E) (β : E) (p memory : List E)
    (mf bf bv tv0 tv1 tv : E) (S pw W : ℕ → E)
    (hS : ∀ i < 45, S (vtCountPadData.getD i default).2.2.1 =
      blockSel (vtSizesC (vtHt rows)) p.length i p)
    (hpw : ∀ t < 6, paddingWeight (p.take (vtHt rows t)) (vtRw rows t) = pw t)
    (hr : rows.length = 6) :
    (vtAcc2 (layoutOf bc lm rows) weights β p memory mf bf bv tv0 tv1 tv).2 =
      tv + ((vtCountPadData.map fun x ↦ S x.2.2.1).sum + 1) +
      vtPadSum S pw W 1 vtCountPadData := by
  have hL := (vt_layout_blocks bc lm hr).2.2
  rw [vtAcc2, hL, accumulateSide_snd]
  have hts := vt_tSels (fw := []) (blocks := vtCountBlocks rows) (p := p)
    (data := vtCountPadData) (k := 0) vt_sizes_count
    (by rw [vt_countBlocks_length, vtCountPadData_length]) S
    (by rw [vtCountPadData_length]; simpa using hS)
  simp only [List.length_nil]
  rw [hts, vt_padSum_count rows p S pw W hpw]
  simp only [sideSels, List.range_zero, List.map_nil, dot, sumE, List.zipWith_nil_left,
    List.foldl_nil, List.nil_append, vt_foldl_add]
  ring

theorem vt_forms0_shape : (tables.map fun _ ↦ ([{}, {}, {}] : List Form)).length = 6 ∧
    ∀ t < 6, ((tables.map fun _ ↦ ([{}, {}, {}] : List Form)).getD t []).length = 3 := by
  refine ⟨rfl, fun t ht ↦ ?_⟩
  rw [List.getD_eq_getElem _ _ (by simp [tables]; omega)]
  simp

theorem vt_forms0_eval (t sd : ℕ) (col : ℕ → E) :
    (((tables.map fun _ ↦ ([{}, {}, {}] : List Form)).getD t []).getD sd {}).evaluate col = 0 := by
  have hL : ∀ sd, (([{}, {}, {}] : List Form).getD sd {}) = {} := by
    intro sd; rcases sd with _ | _ | _ | sd <;> rfl
  have hX : (tables.map fun _ ↦ ([{}, {}, {}] : List Form)).getD t [] = [{}, {}, {}] ∨
      (tables.map fun _ ↦ ([{}, {}, {}] : List Form)).getD t [] = [] := by
    rw [List.getD_eq_getElem?_getD]
    cases h : (tables.map fun _ ↦ ([{}, {}, {}] : List Form))[t]? with
    | none => exact Or.inr rfl
    | some a =>
      left
      obtain ⟨b, -, hb⟩ := List.mem_map.mp (List.mem_of_getElem? h)
      simp [← hb]
  rcases hX with h | h <;> rw [h]
  · rw [hL]; rfl
  · rfl

theorem vt_push_count : ∀ t : Fin 6,
    (vtPushPadData.filter fun x ↦ x.2.1 = (t : ℕ)).length = (vtBT 0 t).length ∧
    (vtPushPadData.filter fun x ↦ x.2.1 = (t : ℕ)).length = (vtBT 1 t).length ∧
    (vtCountPadData.filter fun x ↦ x.2.1 = (t : ℕ)).length = (vtCountCols.getD t []).length := by
  decide

/-- **Table `t`'s forms** on the three sides, at any row. -/
theorem vt_forms (hbc : bc.length = 2 ^ 23) (weights : List E) (β : E) (p memory : List E)
    (mf bf bv tv0 tv1 tv2 : E) (S : ℕ → E)
    (hS : ∀ i < 51, S (vtPushPadData.getD i default).2.2.1 =
      blockSel (vtSizesP lm (vtHt rows)) p.length (3 + i) p)
    (hSC : ∀ i < 45, S (vtCountPadData.getD i default).2.2.1 =
      blockSel (vtSizesC (vtHt rows)) p.length i p)
    (hr : rows.length = 6) (t : Fin 6) (col : ℕ → E) :
    (((vtAcc2 (layoutOf bc lm rows) weights β p memory mf bf bv tv0 tv1 tv2).1.getD t []).getD 0
        {}).evaluate col =
      vtSideVal ((vtPushPadData.filter fun x ↦ x.2.1 = (t : ℕ)).map fun x ↦ S x.2.2.1) β
        (weights.getD · 0) col (vtBT 0 t) ∧
    (((vtAcc2 (layoutOf bc lm rows) weights β p memory mf bf bv tv0 tv1 tv2).1.getD t []).getD 1
        {}).evaluate col =
      vtSideVal ((vtPushPadData.filter fun x ↦ x.2.1 = (t : ℕ)).map fun x ↦ S x.2.2.1) β
        (weights.getD · 0) col (vtBT 1 t) ∧
    (((vtAcc2 (layoutOf bc lm rows) weights β p memory mf bf bv tv0 tv1 tv2).1.getD t []).getD 2
        {}).evaluate col =
      vtSideVal ((vtCountPadData.filter fun x ↦ x.2.1 = (t : ℕ)).map fun x ↦ S x.2.2.1) 0
        (fun _ ↦ 1) col (vtBT 2 t) := by
  obtain ⟨hpush, hpull, hcount⟩ := vt_layout_blocks bc lm hr
  have hP := vt_tSels (fw := [0, lm, 19]) (blocks := vtPushBlocks rows) (p := p)
    (data := vtPushPadData) (k := 3) (vt_sizes_push lm)
    (by rw [vt_pushBlocks_length, vtPushPadData_length]) S (by rw [vtPushPadData_length]; exact hS)
  have hQ := vt_tSels (fw := [0, lm, 19]) (blocks := vtPullBlocks rows) (p := p)
    (data := vtPushPadData) (k := 3) (vt_sizes_pull lm)
    (by rw [vt_pullBlocks_length, vtPushPadData_length]) S (by rw [vtPushPadData_length]; exact hS)
  have hC := vt_tSels (fw := []) (blocks := vtCountBlocks rows) (p := p)
    (data := vtCountPadData) (k := 0) vt_sizes_count
    (by rw [vt_countBlocks_length, vtCountPadData_length]) S
    (by rw [vtCountPadData_length]; simpa using hSC)
  simp only [vtAcc2, vtAcc1, vtAcc0, hpush, hpull, hcount, vt_layout_logBytecode bc lm rows hbc,
    vt_layout_logMemory, accumulateSide_fst, List.length_cons, List.length_nil, Nat.reduceAdd,
    hP, hQ, hC]
  have own := vt_blocks_owner_lt rows
  obtain ⟨h6, h3⟩ := vt_forms0_shape
  have oP : ∀ x ∈ (vtPushPadData.map fun x ↦ S x.2.2.1).zip (vtPushBlocks rows), x.2.owner < 6 :=
    fun x hx ↦ own.1 _ (List.of_mem_zip hx).2
  have oQ : ∀ x ∈ (vtPushPadData.map fun x ↦ S x.2.2.1).zip (vtPullBlocks rows), x.2.owner < 6 :=
    fun x hx ↦ own.2.1 _ (List.of_mem_zip hx).2
  have oC : ∀ x ∈ (vtCountPadData.map fun x ↦ S x.2.2.1).zip (vtCountBlocks rows), x.2.owner < 6 :=
    fun x hx ↦ own.2.2 _ (List.of_mem_zip hx).2
  obtain ⟨l1, r1, o1, e1⟩ := accFold_spec 0 (by norm_num) weights β _ _ h6 h3 oP
  obtain ⟨l2, r2, o2, e2⟩ := accFold_spec 1 (by norm_num) weights β _ _ l1 r1 oQ
  obtain ⟨-, -, o3, e3⟩ := accFold_spec 2 (by norm_num) [1] 0 _ _ l2 r2 oC
  obtain ⟨c0, c1, c2⟩ := vt_push_count t
  refine ⟨?_, ?_, ?_⟩
  · rw [o3 t 0 (by norm_num), o2 t 0 (by norm_num), e1 t col, vt_forms0_eval, zero_add,
      vt_zip_filter _ _ _ _ _ (vt_push_owners rows), vt_push_filter, refSide_eq, List.map_map]
    simp only [Function.comp_def]
    rw [vt_tie_sum _ _ _ _ _ _ _ _ _ (vt_tie_push t), List.length_map, c0, List.take_length]
  · rw [o3 t 1 (by norm_num), e2 t col, o1 t 1 (by norm_num), vt_forms0_eval, zero_add,
      vt_zip_filter _ _ _ _ _ (vt_pull_owners rows), vt_pull_filter, refSide_eq, List.map_map]
    simp only [Function.comp_def]
    rw [vt_tie_sum _ _ _ _ _ _ _ _ _ (vt_tie_pull t), List.length_map, c1, List.take_length]
  · rw [e3 t col, o2 t 2 (by norm_num), o1 t 2 (by norm_num), vt_forms0_eval, zero_add,
      vt_zip_filter _ _ _ _ _ (vt_count_owners rows), vt_count_filter,
      vt_count_sum _ _ _ _ _ _ (by rw [List.length_map, c2]), vt_bt_count]

end

end
end LeanVM.Guest.B1.Tables
