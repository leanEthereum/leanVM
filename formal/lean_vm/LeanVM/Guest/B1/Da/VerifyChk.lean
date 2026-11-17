/-
  LeanVM.Guest.B1.Da.VerifyChk

  `da_verify`'s body, its loops and `da_pad`'s, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.VerifyDefs
public import LeanVM.Guest.B1.Common.Find
public import LeanVM.Guest.Data.NameStrings

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core LeanVM.Guest.B1.Digest

@[expose] public section

set_option maxRecDepth 100000 in
theorem dv_ok : dvOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ws_ok : wsOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem b_ok : bOk (coreProgram.getD idx% «da_verify_loop0» default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem padL_ok : padLOk (coreProgram.getD idx% «da_pad_loop0» default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem dpad_ok : dpadOk fn% «da_pad» = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem dv_loops_idx : coreProgram.indexOf? name% «da_verify_loop0» = some idx% «da_verify_loop0» ∧
    coreProgram.indexOf? name% «da_pad_loop0» = some idx% «da_pad_loop0» :=
  ⟨coreProgram_indexOf?_at (j := idx% «da_verify_loop0») rfl,
    coreProgram_indexOf?_at (j := idx% «da_pad_loop0») rfl⟩

theorem find_da_weights : coreProgram.find? name% «da_weights» = some fn% «da_weights» :=
  coreProgram_find?_at (j := idx% «da_weights») rfl

theorem find_da_pad : coreProgram.find? name% «da_pad» = some fn% «da_pad» :=
  coreProgram_find?_at (j := idx% «da_pad») rfl

end
end LeanVM.Guest.B1.Da
