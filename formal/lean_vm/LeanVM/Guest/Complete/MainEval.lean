module

public import LeanVM.Guest.B1.VsC.VsEval
public import LeanVM.Guest.B1.Main.Body
import LeanVM.Guest.CoreRef

/-!
# `main`'s forward valuation

`Fwd.chk` rejects a branch, and `main`'s body has two (`main_shape`): the direct DA check
(`.ite (.n 384) mDa mDaZ`, `n_direct_da == g`) and the leaf's deferred claim (`.ite (.n 423) mLeaf
mAgg`, `n_children == 1`). Each straight part passes the checker (`chk_mPre`, …), the arms
numbered one after the other.

`mEv rd w`: the words `Fwd.ev` gives part by part, each branch on its taken arm, the other arm's
values `0` (`padZ`). `mVal_good*`: on `mVal = Val.ofArgs (mEv …)`, every statement of each part,
and of each taken arm, satisfies its defining equations (`GoodS`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Main LeanVM.Guest.B1.VsC

@[expose] public section

/-! ## The checker on each part -/

set_option maxRecDepth 200000 in
theorem chk_mPre : chk 0 mPre = some 385 := by decide +kernel

set_option maxRecDepth 200000 in
theorem chk_mDa : chk 385 mDa = some 396 := by decide +kernel

set_option maxRecDepth 200000 in
theorem chk_mDaZ : chk 396 mDaZ = some 398 := by decide +kernel

set_option maxRecDepth 200000 in
theorem chk_mMid : chk 398 mMid = some 424 := by decide +kernel

set_option maxRecDepth 200000 in
theorem chk_mLeaf : chk 424 mLeaf = some 450 := by decide +kernel

set_option maxRecDepth 200000 in
theorem chk_mAgg : chk 450 mAgg = some 452 := by decide +kernel

/-- The values `main`'s body defines: `.n 0 ..< mN`. -/
def mN : ℕ := 460

set_option maxRecDepth 200000 in
theorem chk_mPost : chk 452 mPost = some mN := by decide +kernel

/-! ## The evaluation -/

section
variable (rd : Reader) (w : ℕ → E)

/-- The words after `mPre`. -/
noncomputable def mL1 : List E := ev rd w [] mPre

/-- The words after the direct DA check. -/
noncomputable def mL2 : List E :=
  if B1.Val.ofArgs (mL1 rd w) (.n 384) = 0 then padZ (ev rd w (mL1 rd w) mDa) 398
  else ev rd w (padZ (mL1 rd w) 396) mDaZ

/-- The words after `mMid`. -/
noncomputable def mL3 : List E := ev rd w (mL2 rd w) mMid

/-- The words after the leaf's branch. -/
noncomputable def mL4 : List E :=
  if B1.Val.ofArgs (mL3 rd w) (.n 423) = 0 then padZ (ev rd w (mL3 rd w) mLeaf) 452
  else ev rd w (padZ (mL3 rd w) 450) mAgg

/-- **`main`'s words, evaluated forward**, each branch on its taken arm. -/
noncomputable def mEv : List E := ev rd w (mL4 rd w) mPost

/-- **`main`'s forward valuation.** -/
noncomputable def mVal : Val := B1.Val.ofArgs (mEv rd w)

end

section
variable {rd : Reader} {w : ℕ → E}

theorem mL1_spec : (mL1 rd w).length = 385 := (ev_spec rd w mPre [] (c' := 385) chk_mPre).1

theorem mL2_spec : (mL2 rd w).length = 398 ∧ ∃ m, mL2 rd w = mL1 rd w ++ m := by
  have h1 := mL1_spec (rd := rd) (w := w)
  unfold mL2
  split_ifs
  · obtain ⟨h1', ⟨m, hm⟩, -⟩ := ev_spec rd w mDa (mL1 rd w) (c' := 396) (by rw [h1]; exact chk_mDa)
    exact ⟨padZ_length (by omega), m ++ _, by rw [padZ, hm, List.append_assoc]⟩
  · have hp : (padZ (mL1 rd w) 396).length = 396 := padZ_length (by omega)
    obtain ⟨h1', ⟨m, hm⟩, -⟩ := ev_spec rd w mDaZ (padZ (mL1 rd w) 396) (c' := 398) (by rw [hp]; exact chk_mDaZ)
    exact ⟨h1', List.replicate (396 - (mL1 rd w).length) 0 ++ m, by rw [hm, padZ, List.append_assoc]⟩

theorem mL3_spec : (mL3 rd w).length = 424 ∧ ∃ m, mL3 rd w = mL2 rd w ++ m := by
  obtain ⟨h1, -⟩ := mL2_spec (rd := rd) (w := w)
  obtain ⟨h1', h2', -⟩ := ev_spec rd w mMid (mL2 rd w) (c' := 424) (by rw [h1]; exact chk_mMid)
  exact ⟨h1', h2'⟩

theorem mL4_spec : (mL4 rd w).length = 452 ∧ ∃ m, mL4 rd w = mL3 rd w ++ m := by
  obtain ⟨h1, -⟩ := mL3_spec (rd := rd) (w := w)
  unfold mL4
  split_ifs
  · obtain ⟨h1', ⟨m, hm⟩, -⟩ := ev_spec rd w mLeaf (mL3 rd w) (c' := 450) (by rw [h1]; exact chk_mLeaf)
    exact ⟨padZ_length (by omega), m ++ _, by rw [padZ, hm, List.append_assoc]⟩
  · have hp : (padZ (mL3 rd w) 450).length = 450 := padZ_length (by omega)
    obtain ⟨h1', ⟨m, hm⟩, -⟩ := ev_spec rd w mAgg (padZ (mL3 rd w) 450) (c' := 452) (by rw [hp]; exact chk_mAgg)
    exact ⟨h1', List.replicate (450 - (mL3 rd w).length) 0 ++ m, by rw [hm, padZ, List.append_assoc]⟩

theorem mEv_spec : (mEv rd w).length = mN ∧ ∃ m, mEv rd w = mL4 rd w ++ m := by
  obtain ⟨h1, -⟩ := mL4_spec (rd := rd) (w := w)
  obtain ⟨h1', h2', -⟩ := ev_spec rd w mPost (mL4 rd w) (c' := mN) (by rw [h1]; exact chk_mPost)
  exact ⟨h1', h2'⟩

theorem mEv_ext3 : ∃ m, mEv rd w = mL3 rd w ++ m := ext_trans (mL4_spec).2 (mEv_spec).2

theorem mEv_ext2 : ∃ m, mEv rd w = mL2 rd w ++ m := ext_trans (mL3_spec).2 mEv_ext3

theorem mEv_ext1 : ∃ m, mEv rd w = mL1 rd w ++ m := ext_trans (mL2_spec).2 mEv_ext2

/-- The direct DA check's selector, read after `mPre`. -/
theorem mVal_384 : mVal rd w (.n 384) = B1.Val.ofArgs (mL1 rd w) (.n 384) := by
  obtain ⟨m, hm⟩ := mEv_ext1 (rd := rd) (w := w)
  rw [mVal, hm, ofArgs_old (by rw [mL1_spec]; norm_num)]

/-- The leaf's selector, read after `mMid`. -/
theorem mVal_423 : mVal rd w (.n 423) = B1.Val.ofArgs (mL3 rd w) (.n 423) := by
  obtain ⟨m, hm⟩ := mEv_ext3 (rd := rd) (w := w)
  rw [mVal, hm, ofArgs_old (by rw [(mL3_spec).1]; norm_num)]

/-! ## The equations -/

theorem mVal_goodPre : ∀ s ∈ mPre, GoodS rd (storesOf 0 mPre) w (mVal rd w) s :=
  seg_good (rd := rd) (w := w) (l := []) chk_mPre (L := mEv rd w) (by simpa [mL1] using mEv_ext1)

theorem mVal_goodDa (h : mVal rd w (.n 384) = 0) : ∀ s ∈ mDa, GoodS rd (storesOf 385 mDa) w (mVal rd w) s := by
  have hl := mL1_spec (rd := rd) (w := w)
  have e2 : mL2 rd w = padZ (ev rd w (mL1 rd w) mDa) 398 := by
    rw [mVal_384] at h
    unfold mL2; split_ifs; rfl
  have := seg_good (rd := rd) (w := w) (l := mL1 rd w) (by rw [hl]; exact chk_mDa) (L := mEv rd w)
    (by
      obtain ⟨m, hm⟩ := mEv_ext2 (rd := rd) (w := w)
      exact ⟨List.replicate (398 - (ev rd w (mL1 rd w) mDa).length) 0 ++ m, by rw [hm, e2, padZ, List.append_assoc]⟩)
  rwa [hl] at this

theorem mVal_goodDaZ (h : mVal rd w (.n 384) ≠ 0) :
    ∀ s ∈ mDaZ, GoodS rd (storesOf 396 mDaZ) w (mVal rd w) s := by
  have hl := mL1_spec (rd := rd) (w := w)
  have hp : (padZ (mL1 rd w) 396).length = 396 := padZ_length (by omega)
  have e2 : mL2 rd w = ev rd w (padZ (mL1 rd w) 396) mDaZ := by
    rw [mVal_384] at h
    unfold mL2; split_ifs with hh
    · exact absurd hh h
    · rfl
  have := seg_good (rd := rd) (w := w) (l := padZ (mL1 rd w) 396) (by rw [hp]; exact chk_mDaZ) (L := mEv rd w)
    (by rw [← e2]; exact mEv_ext2)
  rwa [hp] at this

theorem mVal_goodMid : ∀ s ∈ mMid, GoodS rd (storesOf 398 mMid) w (mVal rd w) s := by
  have hl := (mL2_spec (rd := rd) (w := w)).1
  have := seg_good (rd := rd) (w := w) (l := mL2 rd w) (by rw [hl]; exact chk_mMid) (L := mEv rd w) mEv_ext3
  rwa [hl] at this

theorem mVal_goodLeaf (h : mVal rd w (.n 423) = 0) :
    ∀ s ∈ mLeaf, GoodS rd (storesOf 424 mLeaf) w (mVal rd w) s := by
  have hl := (mL3_spec (rd := rd) (w := w)).1
  have e4 : mL4 rd w = padZ (ev rd w (mL3 rd w) mLeaf) 452 := by
    rw [mVal_423] at h
    unfold mL4; split_ifs; rfl
  have := seg_good (rd := rd) (w := w) (l := mL3 rd w) (by rw [hl]; exact chk_mLeaf) (L := mEv rd w)
    (by
      obtain ⟨m, hm⟩ := (mEv_spec (rd := rd) (w := w)).2
      exact ⟨List.replicate (452 - (ev rd w (mL3 rd w) mLeaf).length) 0 ++ m, by rw [hm, e4, padZ, List.append_assoc]⟩)
  rwa [hl] at this

theorem mVal_goodAgg (h : mVal rd w (.n 423) ≠ 0) :
    ∀ s ∈ mAgg, GoodS rd (storesOf 450 mAgg) w (mVal rd w) s := by
  have hl := (mL3_spec (rd := rd) (w := w)).1
  have hp : (padZ (mL3 rd w) 450).length = 450 := padZ_length (by omega)
  have e4 : mL4 rd w = ev rd w (padZ (mL3 rd w) 450) mAgg := by
    rw [mVal_423] at h
    unfold mL4; split_ifs with hh
    · exact absurd hh h
    · rfl
  have := seg_good (rd := rd) (w := w) (l := padZ (mL3 rd w) 450) (by rw [hp]; exact chk_mAgg) (L := mEv rd w)
    (by rw [← e4]; exact (mEv_spec).2)
  rwa [hp] at this

theorem mVal_goodPost : ∀ s ∈ mPost, GoodS rd (storesOf 452 mPost) w (mVal rd w) s := by
  have hl := (mL4_spec (rd := rd) (w := w)).1
  have := seg_good (rd := rd) (w := w) (l := mL4 rd w) (by rw [hl]; exact chk_mPost) (L := mEv rd w)
    ⟨[], by simp [mEv]⟩
  rwa [hl] at this

end

end
end LeanVM.Guest.Complete
