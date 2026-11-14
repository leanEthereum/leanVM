/-
  LeanVM.Guest.B1.Da.VerifyChk

  `da_verify`'s body and its loops, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.VerifyDefs
public import LeanVM.Guest.B1.Common.Find
public import LeanVM.Guest.Data.NameStrings

namespace LeanVM.Guest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem dv_ok : dvOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l17_ok : l17Ok (coreProgram.getD idx% «da_verify_loop0» default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l18_ok : l18Ok (coreProgram.getD idx% «da_verify_loop1» default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l19_ok : l19Ok (coreProgram.getD idx% «da_verify_loop2» default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l20_ok : l20Ok (coreProgram.getD idx% «da_verify_loop3» default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem dv_loops_idx : coreProgram.indexOf? name% «da_verify_loop0» = some idx% «da_verify_loop0» ∧
    coreProgram.indexOf? name% «da_verify_loop1» = some idx% «da_verify_loop1» ∧
        coreProgram.indexOf? name% «da_verify_loop2» = some idx% «da_verify_loop2» ∧
    coreProgram.indexOf? name% «da_verify_loop3» = some idx% «da_verify_loop3» :=
  ⟨coreProgram_indexOf?_at (j := idx% «da_verify_loop0») rfl,
      coreProgram_indexOf?_at (j := idx% «da_verify_loop1») rfl,
    coreProgram_indexOf?_at (j := idx% «da_verify_loop2») rfl,
        coreProgram_indexOf?_at (j := idx% «da_verify_loop3») rfl⟩

end
end LeanVM.Guest.B1.Da
