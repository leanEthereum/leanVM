/-
  LeanVM.Guest.EndExecCoreGhostD

  `GhostOk` on the deployed guest: the exponent and dimension facts carried down (`expFacts_okW`, `dimFacts_okW`),
  the gap walk's ghost families (`EndExecMonoA`), the cursor-run loops (`link_rounds`' loops and last arms: `stLoops_okA`), the functions'
  own families (`EndExecOwnA`), `anyLink`'s checks (`Gen/AnyLinkOk`) and the loops' check (`progOk_guest`).
-/

module

public import LeanVM.Guest.EndExecExpW
public import LeanVM.Guest.CoreMode.Gen.AnyLinkOk
public import LeanVM.Guest.CoreMode.Fam.ProgOkG
public import LeanVM.Guest.EndExecMonoA
public import LeanVM.Guest.EndExecOwnA
public import LeanVM.Guest.CoreMode.Fn.link_rounds.SoundA
public import LeanVM.Guest.CoreMode.Fn.link_rounds_last.SoundA

namespace LeanVM.Guest.EndExec

open LeanVM.Guest LeanVM.Guest.Core

public section

/-- **The cursor-run loops' cursors**: each function's own (`FnReg.stLoops`), proved in its `SoundA` module:
`link_rounds`' loops and its last arms. -/
theorem stLoops_okA {al : String → Bool} {D : Ref → RefD} : ∀ c ∈ CoreMode.FnReg.stLoops, StLoopOkA al D c :=
  CoreMode.FnReg.all_append
    (CoreMode.FnReg.all_append CoreMode.Own.link_rounds.stLoops_okA CoreMode.Own.link_rounds_last.stLoops_okA)
    CoreMode.FnReg.all_nil

/-- **What each function's own soundness owes the core route**, on the deployed guest. -/
theorem ghostOk_guest {al : String → Bool} {D : Ref → RefD} : GhostOk al D :=
  ⟨expFacts_okW, dimFacts_okW, mlLoops_okA, cmLoops_okA, stLoops_okA, fams_okA, anyLink_ok, progOk_guest⟩

end

end LeanVM.Guest.EndExec
