module

public import NativeVm.Code.Phase3.LayoutOffs

/-!
# Phase 3's placements: one side

`sideC_spec`: a side's code writes its placements (`SideAt`) into `placeR side` and leaves the
total size of its placements in `rsi`. `sideTail_spec` is its table part, from the framework sizes
written.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript

/-! ## A side's sizes -/

theorem sideBlocks_at {layout : LayoutW} {H R : Array Nat}
    (hb : Model.busBlocks H R = (layout.push, layout.pull, layout.count)) {side : Nat}
    (hs : side < 3) {k : Nat} (hk : k < (sideBlocks layout side).size) :
    (sideBlocks layout side)[k].logRows = H.getD ((sideOwners side).getD k 0) 0 ∧
      (sideBlocks layout side)[k].rows = R.getD ((sideOwners side).getD k 0) 0 := by
  have e := congrArg (fun l ↦ l[k]?) (sideBlocks_rows hb hs)
  have hk' : k < (sideOwners side).length := by
    rw [sideOwners_length, ← sideBlocks_size hb hs]; exact hk
  simp only [List.getElem?_map, Array.getElem?_toList, Array.getElem?_eq_getElem hk,
    List.getElem?_eq_getElem hk', Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
  rw [List.getD_eq_getElem _ _ hk']
  exact e

theorem sizes_fw {fr : Array Nat} {B : Array BusBlockW} {j : Nat} (hj : j < fr.size) :
    (sizesOf fr B).getD j 0 = fr.getD j 0 := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_append_left hj]

theorem sizes_blk {fr : Array Nat} {B : Array BusBlockW} {k : Nat} (hk : k < B.size) :
    (sizesOf fr B).getD (fr.size + k) 0 = B[k].logRows := by
  simp [Array.getD_eq_getD_getElem?, hk]

theorem sizes_size (fr : Array Nat) (B : Array BusBlockW) :
    (sizesOf fr B).size = fr.size + B.size := by simp

/-! ## The region -/

theorem placeR_off (side : Nat) : (placeR side).off = 52670 + 256 + 512 * side := by
  simp [placeR, sreg, scratchR_off]; omega

theorem placeR_size (side : Nat) : (placeR side).size = 256 := rfl

theorem ok3_placeR {side : Nat} (hs : side < 3) : Ok3 (placeR side) := ok3_sreg (by omega)

theorem layoutR_size : layoutR.size = 490 := by
  rw [show layoutR.size = layoutWords from rfl, layoutWords, columnCount_val]

/-- Words of a region changed only at the words `A`, inside it. -/
theorem Only.wroteR {env : Env} {r : Region} {A : Nat → Prop} {m m' : UInt64 → Option UInt64}
    (h : Only A env.work m m') (hA : ∀ w, A w → r.off ≤ w ∧ w < r.off + r.size) :
    ∀ a, (∀ q ∈ [r], ¬ q.In env.work a) → m' a = m a :=
  fun a ha ↦ h a fun w hw e ↦ ha r (by simp) ⟨w - r.off, by have := hA w hw; omega,
    by rw [e]; congr 1; have := hA w hw; omega⟩

theorem sideShape_lt {side : Nat} : ∀ x ∈ sideShape side, x.1 < 6 := by
  unfold sideShape
  split <;> decide

theorem sideNb_le (side : Nat) : sideNb side ≤ 51 := by unfold sideNb; split <;> omega

theorem sideFw_le (side : Nat) : sideFw side ≤ 3 := by unfold sideFw; split <;> omega

/-- The placements of `busLayout`, by index. -/
theorem busLayout_get (fr : Array Nat) (bs : Array BusBlockW) :
    ∀ i (h : i < ((Model.busLayout fr bs).framework ++ (Model.busLayout fr bs).tables).size),
      ((Model.busLayout fr bs).framework ++ (Model.busLayout fr bs).tables)[i] =
        ⟨(sizesOf fr bs).getD i 0, offF (sizesOf fr bs) i⟩ := by
  rw [(busLayout_all fr bs).2.2]
  intro i h
  simp

theorem busLayout_size (fr : Array Nat) (bs : Array BusBlockW) :
    ((Model.busLayout fr bs).framework ++ (Model.busLayout fr bs).tables).size =
      (sizesOf fr bs).size := by
  rw [(busLayout_all fr bs).2.2]; simp

variable {env : Env} {inp : Input} {s : QState} {E : QState → Prop}

/-- **A side's table part**: the blocks' sizes and rows, then every placement's offset. -/
theorem sideTail_spec {layout : LayoutW} {rate side : Nat} (hs : side < 3)
    (h15 : s.reg .r15 = env.work) (hi : Inputs env inp s.mem)
    (hl : LayoutAt s.mem (layoutR.at env.work) inp.bytecode layout rate)
    (hfw : ∀ j < sideFw side, s.mem (wd env.work ((placeR side).off + 2 * j)) =
      some ((sideFr layout side).getD j 0).toUInt64) :
    WP (blk [fillC (placeR side).off (2 * sideFw side) (sideShape side),
        offsC (placeR side).off (sideFw side + sideNb side)]) s
      (fun s' ↦ s'.reg .r15 = env.work ∧
        SideAt s'.mem ((placeR side).at env.work) (sideLayout layout side) (sideBlocks layout side) ∧
        s'.reg .rsi = (totF (sizesOf (sideFr layout side) (sideBlocks layout side))).toUInt64 ∧
        totF (sizesOf (sideFr layout side) (sideBlocks layout side)) < 2 ^ 37 ∧
        Wrote env [placeR side] s s') E := by
  obtain ⟨rows, hrs, hrw, hbb⟩ := hl.rows
  have hpo := placeR_off side
  have hlo := layoutR_off
  have hnb := sideNb_le side
  have hfwl := sideFw_le side
  have hBs := sideBlocks_size hbb hs
  have hfs := sideFr_size layout side
  have hdom : ∀ w < 256, (s.mem (wd env.work ((placeR side).off + w))).isSome :=
    fun w hw ↦ hi.ok3_some (ok3_placeR hs) hw
  have hh : ∀ t < 6, s.mem (wd env.work (layoutR.off + 4 + t)) =
      some (layout.tableLogHeights.getD t 0).toUInt64 := fun t ht ↦ by
    have := (hl.heights t ht).2
    rwa [Region.at, wd_wd, ← Nat.add_assoc] at this
  have hr : ∀ t < 6, s.mem (wd env.work (layoutR.off + 10 + t)) = some (rows.getD t 0).toUInt64 :=
    fun t ht ↦ by
      have := ((hrw t ht).1).2
      rwa [Region.at, wd_wd, ← Nat.add_assoc] at this
  have hO : (ownersOf (sideShape side)).length = sideNb side := sideOwners_length side
  -- the sizes
  set S := sizesOf (sideFr layout side) (sideBlocks layout side) with hS
  have hSs : S.size = sideFw side + sideNb side := by rw [hS, sizes_size, hfs, hBs]
  have hSb : ∀ j < S.size, S.getD j 0 ≤ 30 := fun j hj ↦ by
    by_cases hj' : j < sideFw side
    · rw [hS, sizes_fw (by omega)]
      unfold sideFr frameworkLogRows
      have := hl.logMemoryBound
      have := hl.logBytecodeBound
      unfold sideFw at hj'
      split
      · simp
      · rename_i h2; simp only [h2, ↓reduceIte] at hj'
        interval_cases j <;> simp <;> omega
    · have hk : j - sideFw side < (sideBlocks layout side).size := by omega
      rw [hS, show j = (sideFr layout side).size + (j - sideFw side) by omega, sizes_blk hk,
        (sideBlocks_at hbb hs hk).1]
      have ht := sideOwners_lt side ((sideOwners side).getD (j - sideFw side) 0)
        (by rw [List.getD_eq_getElem _ _ (by rw [sideOwners_length]; omega)]; exact List.getElem_mem _)
      exact hl.heightsBound _ ht
  have hpo' : (placeR side).off + 256 < 2 ^ 61 := by omega
  have hpl : layoutR.off + 16 ≤ (placeR side).off := by omega
  refine wp_then (fillC_spec (H := fun t ↦ layout.tableLogHeights.getD t 0)
    (R := fun t ↦ rows.getD t 0) (sideShape side) hpo' hpl (by omega) sideShape_lt h15 hh hr hdom)
    fun s₁ ⟨a15, af, aw, ao, ad⟩ ↦ ?_
  -- the sizes' words
  have hsz : ∀ j < S.size, s₁.mem (wd env.work ((placeR side).off + 2 * j)) =
      some (S.getD j 0).toUInt64 := fun j hj ↦ by
    by_cases hj' : j < sideFw side
    · rw [ao.word (by omega) fun w ⟨j', hj'', hw⟩ ↦ ⟨by omega, by omega⟩, hfw j hj',
        hS, sizes_fw (by omega)]
    · have hk : j - sideFw side < (sideBlocks layout side).size := by omega
      have := (aw (j - sideFw side) (by omega)).1
      rw [show (placeR side).off + 2 * sideFw side + 2 * (j - sideFw side) =
        (placeR side).off + 2 * j by omega] at this
      have hSj : S.getD j 0 = (sideBlocks layout side)[j - sideFw side].logRows := by
        have := sizes_blk (fr := sideFr layout side) hk
        rwa [hfs, show sideFw side + (j - sideFw side) = j by omega] at this
      rw [this, hSj, (sideBlocks_at hbb hs hk).1]
      rfl
  have hdom₁ : ∀ w < 256, (s₁.mem (wd env.work ((placeR side).off + w))).isSome :=
    fun w hw ↦ by rw [ad]; exact hdom w hw
  apply WP.blk_cons
  refine WP.mono (offsC_spec (sz := fun j ↦ S.getD j 0) hpo' (by omega) a15
    (fun j hj ↦ hsz j (by omega)) (fun j hj ↦ hSb j (by omega)) hdom₁)
    (fun s₂ ⟨b15, bsi, bw, bo, bd, bf⟩ ↦ WP.blk_nil ?_) fun _ h ↦ h
  have htS := tSum_lt (sz := fun j ↦ S.getD j 0) (n := S.size) (by omega)
    (fun j hj ↦ hSb j hj) S.size le_rfl
  rw [hSs] at htS
  refine ⟨b15, ⟨?_, by omega, fun i hi ↦ ?_, fun k hk ↦ ?_⟩, ?_, by rw [totF_eq, hSs]; exact htS, ?_⟩
  · rw [sideLayout_eq, busLayout_size, ← hS]; omega
  · have hP := busLayout_get _ _ i (by rw [← sideLayout_eq]; exact hi)
    have hi' : i < S.size := by
      have := busLayout_size (sideFr layout side) (sideBlocks layout side)
      rw [← sideLayout_eq, ← hS] at this; omega
    have e : (sideLayout layout side).framework ++ (sideLayout layout side).tables =
        (Model.busLayout (sideFr layout side) (sideBlocks layout side)).framework ++
          (Model.busLayout (sideFr layout side) (sideBlocks layout side)).tables := by
      rw [sideLayout_eq]
    have hc := cSum_le (fun j ↦ S.getD j 0) (keyS (fun j ↦ S.getD j 0) i) (sideFw side + sideNb side)
    simp only [getElem_congr_coll e, hP, ← hS]
    refine ⟨⟨by have := hSb i hi'; omega, ?_⟩, ⟨by rw [offF_eq S (by omega) hi', hSs]; omega, ?_⟩⟩
    · rw [Region.at, wd_wd, bo.word (by omega) fun w ⟨i', hi'', hw⟩ ↦ ⟨by omega, by omega⟩]
      exact hsz i hi'
    · rw [Region.at, wd_wd, ← Nat.add_assoc, bw i (by omega), offF_eq S (by omega) hi', hSs]
  · have hk' : k < sideNb side := by omega
    have hot := sideOwners_lt side ((sideOwners side).getD k 0)
      (by rw [List.getD_eq_getElem _ _ (by rw [sideOwners_length]; omega)]; exact List.getElem_mem _)
    have hrb := (hrw _ hot).2
    refine ⟨by rw [(sideBlocks_at hbb hs hk).2]; omega, ?_⟩
    · rw [Region.at, wd_wd, bo.word (by omega) fun w ⟨i', hi'', hw⟩ ↦ ⟨by omega, by omega⟩,
        ← Nat.add_assoc, (aw k (by omega)).2, (sideBlocks_at hbb hs hk).2]
      rfl
  · rw [bsi, totF_eq, hSs]
  · refine ⟨?_, (ao.trans bo (C := fun w ↦ (placeR side).off ≤ w ∧ w < (placeR side).off + 256)
      (fun w ⟨j, hj, hw⟩ ↦ by omega) (fun w ⟨j, hj, hw⟩ ↦ by omega)).wroteR
      (fun w hw ↦ hw), fun a ↦ (bd a).trans (ad a)⟩
    rw [bf .rdi (by decide), af .rdi (by decide)]

theorem apart_layout_place (side : Nat) : layoutR.Apart (placeR side) := by
  unfold Region.Apart Region.stop
  rw [layoutR_off, layoutR_size, placeR_off, placeR_size]; omega

theorem ok3_place_all {side : Nat} (hs : side < 3) : ∀ r ∈ [placeR side], Ok3 r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; exact ok3_placeR hs

/-- **A side's placements.** -/
theorem sideC_spec {layout : LayoutW} {rate side : Nat} (hs : side < 3)
    (hrdi : s.reg .rdi = env.ctx) (h15 : s.reg .r15 = env.work) (hi : Inputs env inp s.mem)
    (hl : LayoutAt s.mem (layoutR.at env.work) inp.bytecode layout rate) :
    WP (sideC side) s (fun s' ↦ s'.reg .r15 = env.work ∧
        SideAt s'.mem ((placeR side).at env.work) (sideLayout layout side) (sideBlocks layout side) ∧
        s'.reg .rsi = (totF (sizesOf (sideFr layout side) (sideBlocks layout side))).toUInt64 ∧
        totF (sizesOf (sideFr layout side) (sideBlocks layout side)) < 2 ^ 37 ∧
        Wrote env [placeR side] s s') E := by
  unfold sideC
  by_cases h2 : side = 2
  · subst h2
    refine WP.blk_cons (WP.skip ?_)
    exact sideTail_spec hs h15 hi hl fun j hj ↦ absurd hj (by unfold sideFw; simp)
  · simp only [h2, ↓reduceIte]
    have hpo := placeR_off side
    have hlo := layoutR_off
    have hdom : ∀ w < 256, (s.mem (wd env.work ((placeR side).off + w))).isSome :=
      fun w hw ↦ hi.ok3_some (ok3_placeR hs) hw
    refine wp_then (frameC_spec (lm := layout.logMemory) (lb := layout.logBytecode) (by omega) (by omega) h15 hl.logMemory.2
      (by have := hl.logBytecode.2; rwa [Region.at, wd_wd] at this) hdom)
      fun s₁ ⟨a15, af, a0, a2, a4, ao, ad⟩ ↦ ?_
    have hw₁ : Wrote env [placeR side] s s₁ :=
      ⟨af .rdi (by decide), ao.wroteR fun w hw ↦ by
        rcases hw with rfl | rfl | rfl <;> rw [placeR_size] <;> omega, ad⟩
    have hi₁ := hi.step3 (ok3_place_all hs) hw₁.step hrdi
    have hl₁ := hl.congr (hw₁.same (q := layoutR) hi (ok3_place_all hs)
      (ok0_of_mem List.mem_cons_self)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
          exact apart_layout_place side))
    refine WP.mono (sideTail_spec hs a15 hi₁ hl₁ fun j hj ↦ ?_)
      (fun s₂ ⟨b15, bs, bsi, bt, bw⟩ ↦ ⟨b15, bs, bsi, bt, hw₁.trans bw⟩) fun _ h ↦ h
    unfold sideFw at hj
    simp only [h2, ↓reduceIte] at hj
    unfold sideFr frameworkLogRows
    simp only [h2, ↓reduceIte]
    interval_cases j
    · simpa using a0
    · simpa using a2
    · simpa using a4

end NativeVm.Code.P3
