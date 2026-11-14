/-
  LeanVM.Guest.B1.Da.ColumnChk

  `da_verify_column`'s body and `da_verify_column_loop0`'s, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.ColumnDefs
public import LeanVM.Guest.Data.NameStrings

namespace LeanVM.Guest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem col_ok : colOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l21_ok : l21Ok (coreProgram.getD idx% «da_verify_column_loop0» default) = true :=
  by decide +kernel

set_option maxRecDepth 100000 in
theorem l21_idx : coreProgram.indexOf? name% «da_verify_column_loop0» = some
    idx% «da_verify_column_loop0» :=
  coreProgram_indexOf?_at (j := idx% «da_verify_column_loop0») rfl

end
end LeanVM.Guest.B1.Da
