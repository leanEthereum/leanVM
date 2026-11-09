/-
  LeanVM.Guest.B1.Digest.StatementChk

  `statement_digest`'s template, evaluated: its values defined in order, no store, its `KECCAK`
  inputs canonical from the header and pair cells, its side conditions in the header and pairs
  (by kernel evaluation).
-/

module

public import LeanVM.Guest.B1.Digest.Statement
public import LeanVM.Guest.B1.Fwd.Canon

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- `statement_digest`'s body, as its template. -/
def sdBody : List Stmt := sdAtoms.map Stmt.atom ++ [.ret [.n 454, .n 455]]

/-- The values known canonical: the header cells, the pairs' cells, the constants. -/
def sdA : List ℕ :=
  [9, 10, 11, 12, 13, 14, 15, 16] ++ (List.range 12).flatMap (fun p => [17 + 27 * p + 8,
    17 + 27 * p + 17, 17 + 27 * p + 26]) ++ [341, 342, 343, 344, 345, 450]

set_option maxRecDepth 100000 in
theorem sd_chk : chk 9 sdBody = some 456 := by decide +kernel

set_option maxRecDepth 100000 in
theorem sd_stores : storesOf 9 sdBody = [] := by decide +kernel

set_option maxRecDepth 100000 in
theorem sd_canon : canonChk sdA sdAtoms = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem sd_needs : sdAtoms.filter needsSide =
    (List.range 12).flatMap (fun p => (pairAtoms (.n 8) (2 * p) (17 + 27 * p)).filter needsSide) := by
  decide +kernel

end
end LeanVM.Guest.B1.Digest
