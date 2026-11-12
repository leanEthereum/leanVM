/-
  LeanVM.Guest.B1.Da.VerifyChk

  `da_verify`'s body and its loops, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.VerifyDefs
public import LeanVM.Guest.B1.Common.Find

namespace LeanVM.Guest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem dv_ok : dvOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l17_ok : l17Ok (coreProgram.getD 403 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l18_ok : l18Ok (coreProgram.getD 404 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l19_ok : l19Ok (coreProgram.getD 405 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l20_ok : l20Ok (coreProgram.getD 406 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem dv_loops_idx : coreProgram.indexOf? "__loop21" = some 403 ∧
    coreProgram.indexOf? "__loop22" = some 404 ∧ coreProgram.indexOf? "__loop23" = some 405 ∧
    coreProgram.indexOf? "__loop24" = some 406 :=
  ⟨coreProgram_indexOf?_at (j := 403) rfl, coreProgram_indexOf?_at (j := 404) rfl,
    coreProgram_indexOf?_at (j := 405) rfl, coreProgram_indexOf?_at (j := 406) rfl⟩

end
end LeanVM.Guest.B1.Da
