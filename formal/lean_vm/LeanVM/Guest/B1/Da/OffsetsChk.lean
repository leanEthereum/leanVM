/-
  LeanVM.Guest.B1.Da.OffsetsChk

  `da_column_offsets`' body and its seven loops, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.Offsets

namespace LeanVM.Guest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem off_ok : offOk fn% «da_column_offsets» = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem offLoop_ok : ∀ b < 7, offLoopOk (coreProgram.getD (idx% «da_column_offsets_loop0» + b) default) b = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem offLoop_idx : ∀ b < 7, coreProgram.indexOf? (offLoopName b) = some (idx% «da_column_offsets_loop0» + b) :=
  coreProgram_indexOf?_run (by decide +kernel)

end
end LeanVM.Guest.B1.Da
