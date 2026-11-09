/-
  LeanVM.Guest.B1.Da.CellChk

  `da_verify_cell`'s body, checked by kernel evaluation.
-/

module

public import LeanVM.Guest.B1.Da.Cell

namespace LeanVM.Guest.B1.Da

@[expose] public section

set_option maxRecDepth 100000 in
theorem cell_ok : cellOk Data.core30 = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
