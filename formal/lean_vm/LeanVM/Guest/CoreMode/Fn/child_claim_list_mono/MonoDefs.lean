/-
  LeanVM.Guest.CoreMode.Fn.child_claim_list_mono.MonoDefs

  The checks behind the gap walk's table reads: `child_claim_list_mono`'s cells and call sites,
  its callees' callers, and the residual a read of the walk leaves.
-/

module

public import LeanVM.Guest.CoreMode.Fam.LinkDefs
public import LeanVM.Guest.B1.Digest.MonoDefs
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«child_claim_list_mono»

/-!
# The gap walk's table reads

`child_claim_list_mono` (index `o`) holds `entries`, `region`, `limit` in cells `2`, `3`, `5`, and
calls its frame loops and its last claims at fixed arguments, each a site of its plumbing
(`monoOriginB`). Its callees are called only by it or, a loop, by itself, and it only by
`child_claim_list_digest` (`monoCallers`, the callers' check `callersG`).

Claim `jj` of a walk reads the four cells from `[ent]·∏_{i ≤ jj} [gap_i]^4 · g^(4 jj)`, the gaps
at `.n (g0 + 10 i)`, `ent` the walk's table pointer: the frame loops' `.n 12` (`g0 = 13`, 136 or
17 claims), the last claims' `rec[14]`, a heap word through `.n 0` (`g0 = 6`, `k` claims).
-/

namespace LeanVM.Guest.Res

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B2C (cellJ fsN)
open LeanVM.Guest.B1.Digest (mlNames)

@[expose] public section

/-- **The gap walk's callees and their callers**: the frame loops and the last claims called by
`child_claim_list_mono`, it by `child_claim_list_digest`. -/
noncomputable def monoCallers : List (String × String) :=
  ([name% «child_claim_list_mono_loop0», name% «child_claim_list_mono_loop1»] ++ mlNames).map
    (·, name% «child_claim_list_mono») ++ [(name% «child_claim_list_mono», name% «child_claim_list_digest»)]

/-- A call site of `child_claim_list_mono`'s callees: the frame loops and the last claims at their
arguments, each a site of its plumbing. -/
noncomputable def monoSiteB (o : ℕ) (f : String) (args rets : List V) : Bool :=
  (f != name% «child_claim_list_mono_loop0» || (args == [.n (val% «child_claim_list_mono» "s4#2"), .n (val% «child_claim_list_mono» "bigs"), .n (val% «child_claim_list_mono» "chain"), .n (val% «child_claim_list_mono» "base")] && siteB o args rets)) &&
  (f != name% «child_claim_list_mono_loop1» || (args == [.n (val% «child_claim_list_mono» "s6#2"), .n (val% «child_claim_list_mono» "groups"), .n (val% «child_claim_list_mono» "mid"), .n (val% «child_claim_list_mono» "base")] && siteB o args rets)) &&
  (!mlNames.contains f || (args == [.n (val% «child_claim_list_mono» "last"), .n (val% «child_claim_list_mono» "region"), .n (val% «child_claim_list_mono» "base"), .n (val% «child_claim_list_mono» "limit_g")] && siteB o args rets))

/-- **`child_claim_list_mono`'s check**: its cells `2`, `3`, `5` and its call sites. -/
noncomputable def monoOriginB : Bool :=
  let o := fn_idx% «child_claim_list_mono»
  (coreOf o).name == name% «child_claim_list_mono» && !(coreOf o).loop &&
  decide ((coreOf o).params = [.n (val% «child_claim_list_mono» "entries_ptr"), .n (val% «child_claim_list_mono» "region"), .n (val% «child_claim_list_mono» "base"), .n (val% «child_claim_list_mono» "limit_g"), .n (val% «child_claim_list_mono» "bigs"), .n (val% «child_claim_list_mono» "groups"), .n (val% «child_claim_list_mono» "rest")]) &&
  cellJ o (.n (val% «child_claim_list_mono» "entries_ptr")) == 2 && cellJ o (.n (val% «child_claim_list_mono» "region")) == 3 && cellJ o (.n (val% «child_claim_list_mono» "limit_g")) == 5 && Nat.blt 5 (fsN o) &&
  sitesB (monoSiteB o) (coreOf o).body

/-- A frame loop's check: no call of itself before its tail. -/
noncomputable def monoLoopB (f : String) : Bool :=
  match coreProgram.find? f with
  | some fn => !(Stmt.blockCallees (loopBody fn)).contains f
  | none => false

/-- The last claims are no loops. -/
noncomputable def monoMlB : Bool :=
  mlNames.all fun f => match coreProgram.find? f with
    | some fn => !fn.loop
    | none => true

end

end LeanVM.Guest.Res
