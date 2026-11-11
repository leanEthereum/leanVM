/-
  LeanVM.Guest.B1.Place.KidLr

  open_stacked's `level_residual` calls placed, from their placed statement.
-/

module

public import LeanVM.Guest.B1.Place.HonestSpec

/-!
# `level_residual`'s calls, placed

`lk_fixed`: a slice of an own buffer (but the window pointers) is the same on every memory holding
the callees' words, so its loads lie there. `os_lr_kid`: level `l`'s `level_residual` call, at its
honest arguments (`osLrArgs`), is complete placed on the callees' words, returning `finH`, from
`LrAtO` and the level's honest data (`LvHelperFacts.res`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {c : OsCfg} {tr : OsTr} {b0 : ℕ}
  {Lin : Layout}

/-- A slice's word `k`. -/
theorem slice_get {xs : List E} {off n k : ℕ} (hk : k < ((xs.drop off).take n).length) :
    ((xs.drop off).take n)[k] = xs.getD (off + k) 0 := by
  simp only [List.length_take, List.length_drop] at hk
  rw [List.getElem_take, List.getElem_drop, List.getD_eq_getElem _ _ (by omega)]

theorem qposC_length : (qposC c tr).length = c.levels.length * ligPosCap := by simp [qposC]
theorem bdC_length : (bdC c tr).length = c.levels.length * ligColsCap := by simp [bdC]

/-- **Level `l`'s `level_residual` call, placed**, at its honest arguments. -/
theorem os_lr_kid (hpt : (tr.point (c.levels.headD default).folds).length ≤ pointCap)
    (htl : tr.Lf.ml ≤ yrLogCap) (hs : OsSizes c) {l : ℕ} (hl : l < c.levels.length)
    (hq : (lvAt c l).posOff + (lvAt c l).queries ≤ c.levels.length * ligPosCap)
    (hH : LvHelperFacts c tr l) {name : String} {Bd : Option ℕ}
    (hlr : LrAtO fs cert κ name (lvAt c l).queries (lvAt c l).logCols Bd) (hB : BoundsAt fs name Bd)
    (hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 (osLk c tr b0 Lin)) :
    CompleteAtO fs cert κ name (osLk c tr b0 Lin) (osLrArgs c tr (osAtOf c b0) l)
      (Returns [finH c tr l]) Bd := by
  obtain ⟨g0, g1, g2, g3, g4, g5, -, g7, g8, g9⟩ := osOwnL_getD_head c tr fun _ _ ↦ 0
  obtain ⟨-, -, -, gB, -, -⟩ := osOwnL_getD_fin c tr fun _ _ ↦ 0
  have hcols := hs.cols l hl
  obtain ⟨lP1, lP2⟩ := lk_slice (κ := κ) (b0 := b0) (Lin := Lin) hpt htl (j := 5)
    (off := (lvAt c l).posOff) (n := (lvAt c l).queries) (by omega) (by omega)
    (by rw [g5, qposC_length]; exact hq)
  obtain ⟨lB1, lB2⟩ := lk_slice (κ := κ) (b0 := b0) (Lin := Lin) hpt htl (j := osIxBD c)
    (off := l * ligColsCap) (n := (lvAt c l).logCols) (by unfold osIxBD; omega)
    (by unfold osIxBD; omega)
    (by rw [gB, bdC_length]; nlinarith)
  have hfix : FixedReads κ [(0, (lvAt c l).queries), (1, (lvAt c l).logCols)]
      (osLrArgs c tr (osAtOf c b0) l) (osLk c tr b0 Lin) := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨_, lP1, fun rd hl' hm ↦ lP2 rd hl' hm⟩
    · exact ⟨_, lB1, fun rd hl' hm ↦ lB2 rd hl' hm⟩
  have hreg := fixedReads_region hfix hex
  rw [show finH c tr l = _ from hH.res]
  refine hlr _ _ _ _ _ _ hreg (fun rd hl' hm ↦ ⟨fun i hi ↦ ?_, fun s hs' ↦ ?_⟩) hB
  · have h := lP2 rd hl' hm i (by rw [lP1]; exact hi)
    rw [slice_get, g5] at h
    exact h
  · have h := lB2 rd hl' hm s (by rw [lB1]; exact hs')
    rw [slice_get, gB] at h
    exact h

end
end LeanVM.Guest.B1
