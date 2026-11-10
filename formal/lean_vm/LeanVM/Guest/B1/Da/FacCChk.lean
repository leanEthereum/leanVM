/-
  LeanVM.Guest.B1.Da.FacCChk

  `da_factors`, evaluated (by kernel evaluation): its values defined in order, its stores the
  nodes' factors, its one `HeapBuf`, no `frameAddr`.
-/

module

public import LeanVM.Guest.B1.Da.Factors
public import LeanVM.Guest.B1.Fwd.Canon
public import LeanVM.Guest.B1.Tables.FlatAt

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

/-- The nodes' stores: node `2^d + y`'s factor into `factors[2^d + y]`. -/
def facStores (D : ℕ) : List Atom :=
  (List.range D).flatMap fun d => (List.range (2 ^ d)).map fun y =>
    .load (.n (facB d + 4 + 4 * y)) (.n 1) (2 ^ d + y)

/-- **`da_factors`, evaluated**: defined in order from its argument, its stores the nodes',
canonical without inputs, one `HeapBuf` of `256` words, no `frameAddr`. -/
def facCOk (fn : Fn) (top D : ℕ) : Bool :=
  (chk 1 fn.body).isSome && atomsEqb (storesOf 1 fn.body) (facStores D) &&
  canonChk [] (facT top D) &&
  decide (((facT top D).map Stmt.atom).filterMap Stmt.addrS = []) &&
  decide (((facT top D).map Stmt.atom).filterMap Stmt.allocSz = [(.n 1, .inl 256)])

set_option maxRecDepth 100000 in
theorem fac14_cok : facCOk Data.core433 14 7 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem fac7_cok : facCOk Data.core435 7 8 = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
