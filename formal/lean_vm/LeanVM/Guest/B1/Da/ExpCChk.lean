/-
  LeanVM.Guest.B1.Da.ExpCChk

  `da_expand`, evaluated (by kernel evaluation): its computing atoms define their values in order
  below the run's pointer, with no store; no `HeapBuf`; one `frameAddr`, of its `256`-word run.
-/

module

public import LeanVM.Guest.B1.Da.Expand
public import LeanVM.Guest.B1.Fwd.Canon
public import LeanVM.Guest.B1.Tables.FlatAt

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

/-- **`da_expand`, evaluated**: its computing atoms defined in order from its four arguments up
to the run's pointer `.n (expB D)`, without a store, only their loads
needing a side condition, their values below it; no `HeapBuf`; its one `frameAddr` the run's. -/
def expCOk (top D W : ℕ) : Bool :=
  decide (chk 4 ((expBodyA top D).map Stmt.atom) = some (expB D)) &&
  (storesOf 4 ((expBodyA top D).map Stmt.atom)).isEmpty &&
  (expBodyA top D).all (fun a => !needsSide a || (atomLoad? a).isSome) &&
  (expBodyA top D).all (fun a => a.vals.all fun v => decide (v.idx < expB D)) &&
  (expT top D W).all (fun a => !atomAllocB a) &&
  decide ((expT top D W).filterMap atomAddr? = [(.n (expB D), .n (expB D + 1))]) &&
  decide ((expT top D W).filterMap atomRun? = [(.n (expB D + 1), 256)])

set_option maxRecDepth 100000 in
theorem expCell_cok : expCOk 6 7 325 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem expTop_cok : expCOk 13 7 325 = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
