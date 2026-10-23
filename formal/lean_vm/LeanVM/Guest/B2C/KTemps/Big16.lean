module

public import LeanVM.Guest.B2C.KTempsBase
public import LeanVM.Guest.B2C.Temps1617

namespace LeanVM.Guest.B2C

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

set_option maxRecDepth 100000 in
theorem tmpsOk_16 : TmpsOk 16 := by
  unfold TmpsOk
  show tmpCellsB 17 ((Stmt.tmpsList Data.core16.body).map V.idx) = true
  rw [tmps16]
  decide +kernel

end
end LeanVM.Guest.B2C
