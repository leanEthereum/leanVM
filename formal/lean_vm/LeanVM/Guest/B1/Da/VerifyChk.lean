/-
  LeanVM.Guest.B1.Da.VerifyChk

  `da_verify`'s body and its loops, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.VerifyDefs

namespace LeanVM.Guest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem dv_ok : dvOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l17_ok : l17Ok (coreProgram.getD 387 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l18_ok : l18Ok (coreProgram.getD 388 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l19_ok : l19Ok (coreProgram.getD 389 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l20_ok : l20Ok (coreProgram.getD 390 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem dv_loops_idx : coreProgram.indexOf? "__loop21" = some 387 ∧
    coreProgram.indexOf? "__loop22" = some 388 ∧ coreProgram.indexOf? "__loop23" = some 389 ∧
    coreProgram.indexOf? "__loop24" = some 390 := by
  decide +kernel

end
end LeanVM.Guest.B1.Da
