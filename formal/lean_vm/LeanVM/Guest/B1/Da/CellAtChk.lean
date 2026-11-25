/-
  LeanVM.Guest.B1.Da.CellAtChk

  `da_verify_cell`'s block, for its placement (by kernel evaluation): flat, calling nothing, no buffer, its loads the
  `128` weights through its argument.
-/

module

public import LeanVM.Guest.B1.Da.Padding
public import LeanVM.Guest.B1.Da.VecCChk
public import LeanVM.Guest.B1.Tables.FlatAt
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_verify_cell»
import LeanVM.Guest.StmtsAppend

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- `da_verify_cell`'s block. -/
noncomputable def cellPre : List Stmt := (Fn.body fn% «da_verify_cell»).dropLast

/-- **Its shape**: the block then `ret`, flat, no dispatch nor `ite`, no `frameAddr`, `HeapBuf` nor call, loading the
weights `0 … 127` through `.n 0`. -/
noncomputable def cellPOk : Bool :=
  stmtsEqb (Fn.body fn% «da_verify_cell») (cellPre ⧺ [.ret [.n (val% «da_verify_cell» "s6#0"), .n (val% «da_verify_cell» "s6#0[1]"), .n (val% «da_verify_cell» "s6#0[2]")]]) &&
  cellPre.all Core.Stmt.flat && cellPre.all noDispatch && cellPre.all notIteB &&
  decide (cellPre.filterMap Main.Stmt.addrS = []) && decide (cellPre.filterMap Main.Stmt.allocSz = []) &&
  decide (cellPre.filterMap Main.Stmt.callS = []) &&
  decide (cellPre.filterMap Stmt.loadS = (List.range 128).map fun i => (V.n (val% «da_verify_cell» "lvals"), i))

theorem cellp_ok : cellPOk = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
