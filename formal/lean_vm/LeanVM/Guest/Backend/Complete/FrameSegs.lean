/-
  LeanVM.Guest.Backend.Complete.FrameSegs

  The statements `FrameStmt.lean` takes from the primitives: a flush in lockstep with the scope
  walk (`FlushSegStmt`) and the chaining of `match`es kept by a statement (`ChainKeep`).
-/

module

public import LeanVM.Guest.Backend.Complete.FrameStmt
public import LeanVM.Guest.Backend.Complete.FrameLocs

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **A flush in lockstep with `flushS`** (`flush_lock`). -/
theorem flushSeg_lock : FlushSegStmt :=
  fun _ _ _ _ up _ _ _ _ hok hfl hlen hcp huse hab h2 hv hb =>
    flush_lock up hok hfl hlen hcp huse hab h2 hv hb

variable {ctx : Ctx} {rest : List Stmt}

theorem chainKeep_atom' {a : Atom} : ChainKeep ctx (.atom a) rest := chainKeep_atom

theorem chainKeep_call' {f : String} {args rets : List V} :
    ChainKeep ctx (.call f args rets) rest := chainKeep_call

theorem chainKeep_callIf' {c : V} {f : String} {args : List V} :
    ChainKeep ctx (.callIf c f args) rest := chainKeep_callIf

theorem chainKeep_dispatch' {x : V} {fs : List String} {args rets : List V} :
    ChainKeep ctx (.dispatch x fs args rets) rest := chainKeep_dispatch

theorem chainKeep_ret' {vs : List V} : ChainKeep ctx (.ret vs) rest := chainKeep_ret

end
end LeanVM.Guest.Backend.Complete
