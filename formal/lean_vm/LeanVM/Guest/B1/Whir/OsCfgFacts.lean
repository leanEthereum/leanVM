/-
  LeanVM.Guest.B1.Whir.OsCfgFacts

  The per-configuration facts `open_stacked`'s placed completeness takes of its compiled body.
-/

module

public import LeanVM.Guest.B1.Whir.OsLay

/-!
# A configuration's body facts (TRIAGE #36)

`OsBodyFacts cfg`: the buffer layout (`OsLayoutOk`), the buffers' sizes fit an exponent
(`OsSizesOk`), the body is its statements before the return then the return, those statements
are straight-line, set up no `frameAddr`, and allocate the buffers `osAllocList cfg`, and the tail
challenges' value is not the fold challenges' pointer. Each is decided per configuration.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- The variables `open_stacked`'s body returns. -/
def osRetVs (cfg : OsCfg) : List V :=
  match (osBody cfg).getLast? with
  | some (.ret vs) => vs
  | _ => []

/-- **A configuration's body facts.** -/
structure OsBodyFacts (cfg : OsCfg) : Prop where
  layout : OsLayoutOk cfg
  sizes : OsSizesOk cfg
  last : osBody cfg = (osBody cfg).dropLast ++ [.ret (osRetVs cfg)]
  straight : (osBody cfg).dropLast.all Main.Stmt.straight = true
  addrs : (osBody cfg).dropLast.filterMap Main.Stmt.addrS = []
  allocs : (osBody cfg).dropLast.filterMap Main.Stmt.allocSz = osAllocList cfg
  tch : OsRun.tch cfg ≠ osFch

end
end LeanVM.Guest.B1
