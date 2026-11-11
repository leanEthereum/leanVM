/-
  LeanVM.Guest.B1.Place.OsCandAll

  f128's `open_stacked` is complete placed at every candidate, from the honest data of its runs.
-/

module

public import LeanVM.Guest.B1.Place.OsCandF0
public import LeanVM.Guest.B1.Place.OsCandF1
public import LeanVM.Guest.B1.Place.OsCandF2
public import LeanVM.Guest.B1.Place.OsCandF3
public import LeanVM.Guest.B1.Place.OsLiftB
public import LeanVM.Guest.B1.Whir.DataAll
public import LeanVM.Guest.B1.Whir.Sound
public import LeanVM.Guest.B1.Place.OsHonestSpec
public import LeanVM.Guest.B1.Place.OsMeanB

/-!
# `open_stacked`, placed, at every candidate

`placeAll_all`: every candidate's decided facts (`Place/OsCandF{0..3}.lean`). `OsHonestSpec`:
every accepting run with no zero challenge, no vanishing combiner and openings agreeing in the
caps has the honest data `OsHonest` at its candidate (the body's completeness, `Whir/C*`).
**`open_stacked_completeAtD_of`**, **`open_stacked_completeAtB_of`**: from it, OsSpec's statements
(`os_completeAtD_lift`, `os_completeAtB_lift` at the candidate's core IR, `OsData`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir

@[expose] public section

/-- **Every candidate's decided placed-lift facts.** -/
theorem placeAll_all (m : ℕ) (h : m < 28) : PlaceAll (osCfg m) := by
  interval_cases m
  · exact placeAll_0
  · exact placeAll_1
  · exact placeAll_2
  · exact placeAll_3
  · exact placeAll_4
  · exact placeAll_5
  · exact placeAll_6
  · exact placeAll_7
  · exact placeAll_8
  · exact placeAll_9
  · exact placeAll_10
  · exact placeAll_11
  · exact placeAll_12
  · exact placeAll_13
  · exact placeAll_14
  · exact placeAll_15
  · exact placeAll_16
  · exact placeAll_17
  · exact placeAll_18
  · exact placeAll_19
  · exact placeAll_20
  · exact placeAll_21
  · exact placeAll_22
  · exact placeAll_23
  · exact placeAll_24
  · exact placeAll_25
  · exact placeAll_26
  · exact placeAll_27

/-- A candidate's core IR, at its levels' rows. -/
theorem osData_at {m : ℕ} (hm : m < 28) :
    (∃ fn, coreProgram.find? ("open_stacked__L" ++ natStr m) = some fn ∧ fn.params = osParams 10 ∧
      fn.body = osBody (osCfg m)) ∧
    (∀ l < (osCfg m).levels.length, FnIs ((osCfg m).sqLoop l) (osParams 6)
      (sqLoopBody (osLvAt (osCfg m) l) ((osCfg m).sqLoop l))) ∧
    ∀ l < (osCfg m).yrLevel, FnIs ((osCfg m).resLoop l) (osParams 7)
      (resLoopBody l (osLvAt (osCfg m) l) ((osCfg m).resLoop l)) := by
  obtain ⟨h1, h2, h3⟩ := osData_all m hm
  have hyr := (placeAll_all m hm).2.1
  refine ⟨h1, fun l hl ↦ ?_, fun l hl ↦ ?_⟩
  · rw [osLvAt, osCfg_levels_getD (by rwa [osCfg_levels_length] at hl)]; exact h2 l hl
  · rw [osLvAt, osCfg_levels_getD (by rw [← osCfg_levels_length]; omega)]; exact h3 l hl

theorem os_args_length (S : KeccakState) (target r0 r1 cur tabs : E) :
    (capOf S ++ [target, r0, r1, cur, tabs]).length = 10 := by
  simp [show (capOf S).length = 5 from rfl]

/-- **`open_stacked` is complete placed at every candidate**, from the honest data. -/
theorem open_stacked_completeAtD_of (hH : OsHonestSpec) : open_stacked_completeAtD_Spec := by
  intro μ r h1 h2 h3 h4 fs cert κ hrf hcons hκ S root target cur tabs xs os w s' roots' hrun hnz
    hcaps Lin hLin
  have hm : candidate μ r < 28 := by unfold candidate; omega
  obtain ⟨H⟩ := hH μ r h1 h2 h3 h4 S root target cur tabs xs os w s' roots' hrun hnz hcaps
  obtain ⟨⟨fn, hf, hp, hb⟩, hsq, hres⟩ := osData_at hm
  rw [openName_eq μ r hm]
  exact os_completeAtD_lift hrf hcons hκ (placeAll_all _ hm) hf hp hb hsq hres
    (os_args_length S _ _ _ _ _) H hLin

/-- **`open_stacked` is complete placed at every candidate, within `osBosAt` words**, from the
honest data (the named callees within their bounds by `os_kid_namedB`). -/
theorem open_stacked_completeAtB_of (hH : OsHonestSpec) : open_stacked_completeAtB_Spec := by
  intro μ r h1 h2 h3 h4 fs cert κ Bnd Kr hrf hcons hκ hT hL S root target cur tabs xs os w s'
    roots' hrun hnz hcaps Lin hLin
  have hm : candidate μ r < 28 := by unfold candidate; omega
  obtain ⟨H⟩ := hH μ r h1 h2 h3 h4 S root target cur tabs xs os w s' roots' hrun hnz hcaps
  obtain ⟨⟨fn, hf, hp, hb⟩, hsq, hres⟩ := osData_at hm
  unfold osBosAt
  rw [openName_eq μ r hm]
  have := os_completeAtB_lift hrf hcons hκ (placeAll_all _ hm) hf hp hb hsq hres
    (os_args_length S _ _ _ _ _) H hLin
    (fun hall hex _ hc ht _ hK ↦ os_kid_namedB hκ hT hall hex hc ht hK) hL
  intro fp
  obtain ⟨n, Lown, rets, Lout, ⟨b, b1, e1, e2⟩, hw, hd, hn, hr⟩ := this fp
  exact ⟨n, Lown, rets, Lout, ⟨b, b1, e1, e2⟩, hw, hd, hn, hr⟩

end
end LeanVM.Guest.B1
