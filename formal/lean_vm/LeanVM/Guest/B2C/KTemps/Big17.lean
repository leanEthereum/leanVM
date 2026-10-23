module

public import LeanVM.Guest.B2C.KTempsBase
public import LeanVM.Guest.B2C.Temps1617

namespace LeanVM.Guest.B2C

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

set_option maxRecDepth 100000 in
theorem tmpsOk_17 : TmpsOk 17 := by
  unfold TmpsOk
  show tmpCellsB 18 ((Stmt.tmpsList Data.core17.body).map V.idx) = true
  rw [tmps17]
  decide +kernel

end
end LeanVM.Guest.B2C
