/-
  LeanVM.Guest.B1.Da.OffsetsChk

  `da_column_offsets`' body and its seven loops, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.Offsets

namespace LeanVM.Guest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem off_ok : offOk Data.core32 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem offLoop_ok : ∀ b < 7, offLoopOk (coreProgram.getD (423 + b) default) b = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem offLoop_idx : ∀ b < 7, coreProgram.indexOf? (offLoopName b) = some (423 + b) :=
  coreProgram_indexOf?_run (by decide +kernel)

end
end LeanVM.Guest.B1.Da
