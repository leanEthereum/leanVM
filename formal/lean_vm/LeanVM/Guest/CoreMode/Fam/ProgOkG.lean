/-
  LeanVM.Guest.CoreMode.Fam.ProgOkG

  The deployed guest's loops pass their termination check (`Gen/LoopCheck`), so the program is
  `Res.ProgOk`; every frame has a word.
-/

module

public import LeanVM.Guest.CoreMode.Fam.ResTA
public import LeanVM.Guest.CoreMode.Gen.LoopCheck

namespace LeanVM.Guest.Res

public section

theorem fs_pos (f : String) : 1 ≤ B2C.fs f := le_trans (by norm_num) (B2C.two_le_fs f)

end

end LeanVM.Guest.Res

namespace LeanVM.Guest.EndExec

public section

/-- **The deployed guest's loops' check** (`Res.termAll`). -/
theorem progOk_guest : Res.ProgOk coreProgram := progOk_of_termAll Res.termAll

end

end LeanVM.Guest.EndExec
