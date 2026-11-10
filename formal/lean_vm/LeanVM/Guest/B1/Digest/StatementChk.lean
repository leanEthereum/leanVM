/-
  LeanVM.Guest.B1.Digest.StatementChk

  `statement_digest`'s template, evaluated: its values defined in order, no store, its side
  conditions in its loads (by kernel evaluation).
-/

module

public import LeanVM.Guest.B1.Digest.Statement
public import LeanVM.Guest.B1.Fwd.Canon

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- `statement_digest`'s body, as its template. -/
def sdBody : List Stmt := sdAtoms.map Stmt.atom ++ [.ret [.n 115, .n 116]]

set_option maxRecDepth 100000 in
theorem sd_chk : chk 9 sdBody = some 117 := by decide +kernel

set_option maxRecDepth 100000 in
theorem sd_stores : storesOf 9 sdBody = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem sd_needs : sdAtoms.filter needsSide = sdLoads := by decide +kernel

end
end LeanVM.Guest.B1.Digest
