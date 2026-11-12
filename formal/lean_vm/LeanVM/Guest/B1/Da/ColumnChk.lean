/-
  LeanVM.Guest.B1.Da.ColumnChk

  `da_verify_column`'s body and `__loop25`'s, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.ColumnDefs

namespace LeanVM.Guest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem col_ok : colOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l21_ok : l21Ok (coreProgram.getD 419 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l21_idx : coreProgram.indexOf? "__loop25" = some 419 := by decide +kernel

end
end LeanVM.Guest.B1.Da
