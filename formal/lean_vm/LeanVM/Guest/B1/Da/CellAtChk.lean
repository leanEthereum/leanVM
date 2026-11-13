/-
  LeanVM.Guest.B1.Da.CellAtChk

  `da_verify_cell`'s block, for its placement (by kernel evaluation): flat, calling nothing, no buffer, its loads the
  `256` weights through its argument.
-/

module

public import LeanVM.Guest.B1.Da.Cell
public import LeanVM.Guest.B1.Da.VecCChk
public import LeanVM.Guest.B1.Tables.FlatAt

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- `da_verify_cell`'s block. -/
noncomputable def cellPre : List Stmt := (Fn.body fn% «da_verify_cell»).dropLast

/-- **Its shape**: the block then `ret`, flat, no dispatch nor `ite`, no `frameAddr`, `HeapBuf` nor call, loading the
weights `0 … 255` through `.n 0`. -/
noncomputable def cellPOk : Bool :=
  stmtsEqb (Fn.body fn% «da_verify_cell») (cellPre ++ [.ret [.n 1740, .n 1741, .n 1742]]) &&
  cellPre.all Core.Stmt.flat && cellPre.all noDispatch && cellPre.all notIteB &&
  decide (cellPre.filterMap Main.Stmt.addrS = []) && decide (cellPre.filterMap Main.Stmt.allocSz = []) &&
  decide (cellPre.filterMap Main.Stmt.callS = []) &&
  decide (cellPre.filterMap Stmt.loadS = (List.range 256).map fun i => (V.n 0, i))

set_option maxRecDepth 100000 in
theorem cellp_ok : cellPOk = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
