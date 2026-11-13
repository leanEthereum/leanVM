/-
  LeanVM.Guest.B1.VerifySub.MuteChk

  `vsMuteSet` pops nothing: every member's body is mute and calls members only (kernel evaluation).
-/

module

public import LeanVM.Guest.B1.Common.MutePops
public import LeanVM.Guest.B1.VerifySub.MuteSet
public import LeanVM.Guest.CoreData

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- Every member's body pops nothing and calls members only. -/
noncomputable def vsMuteOk : Bool :=
  vsMuteSet.all fun g => match coreProgram.find? g with
    | some fn => Stmt.muteList vsMuteSet.contains fn.body
    | none => true

theorem vsMute_ok : vsMuteOk = true := by decide +kernel

theorem vsMute : MuteIn coreProgram vsMuteSet.contains := by
  intro g hg fn hf
  have h := List.all_eq_true.mp vsMute_ok g (by simpa using hg)
  rw [hf] at h
  exact h

end
end LeanVM.Guest.B1.VerifySub
