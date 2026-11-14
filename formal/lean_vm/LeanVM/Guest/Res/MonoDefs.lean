/-
  LeanVM.Guest.Res.MonoDefs

  The checks behind the gap walk's table reads: `child_claim_list_mono`'s cells and call sites,
  its callees' callers, and the residual a read of the walk leaves.
-/

module

public import LeanVM.Guest.Res.LinkDefs
public import LeanVM.Guest.B1.Digest.MonoDefs

/-!
# The gap walk's table reads

`child_claim_list_mono` (index `o`) holds `entries`, `region`, `limit` in cells `2`, `3`, `5`, and
calls its frame loops and its last claims at fixed arguments, each a site of its plumbing
(`monoOriginB`). Its callees are called only by it or, a loop, by itself, and it only by
`child_claim_list_digest` (`monoCallers`, the callers' check `callersG`).

Claim `jj` of a walk reads the four cells from `[ent]·∏_{i ≤ jj} [gap_i]^4 · g^(4 jj)`, the gaps
at `.n (g0 + 10 i)`, `ent` the walk's table pointer: the frame loops' `.n 12` (`g0 = 13`, 136 or
17 claims), the last claims' `rec[14]`, a heap word through `.n 0` (`g0 = 6`, `k` claims)
(`monoFam`). `monoResB j x`: residual `x` of function `j` is such a read inside the caller's table
(`anyTab`), its bases those, in one of the two orders the walk sorts them, inside the frame.
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

/-- **The callers' check of one function** against `(callee, caller)` pairs: a call of a listed
callee is its caller's, or its own, a loop. -/
noncomputable def callersG (R : List (String × String)) (fn : Fn) : Bool :=
  sitesB (fun f _ _ => R.all fun p => p.1 != f || fn.name == p.2 || (fn.name == f && fn.loop)) fn.body

/-- A call site of `child_claim_list_mono`'s callees: the frame loops and the last claims at their
arguments, each a site of its plumbing. -/
noncomputable def monoSiteB (o : ℕ) (f : String) (args rets : List V) : Bool :=
  (f != name% «child_claim_list_mono_loop0» || (args == [.n 32, .n 4, .n 16, .n 2] && siteB o args rets)) &&
  (f != name% «child_claim_list_mono_loop1» || (args == [.n 42, .n 5, .n 39, .n 2] && siteB o args rets)) &&
  (!mlNames.contains f || (args == [.n 49, .n 1, .n 2, .n 3] && siteB o args rets))

/-- **`child_claim_list_mono`'s check**: its cells `2`, `3`, `5` and its call sites. -/
noncomputable def monoOriginB : Bool :=
  let o := fn_idx% «child_claim_list_mono»
  (coreOf o).name == name% «child_claim_list_mono» && !(coreOf o).loop &&
  decide ((coreOf o).params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6]) &&
  cellJ o (.n 0) == 2 && cellJ o (.n 1) == 3 && cellJ o (.n 3) == 5 && Nat.blt 5 (fsN o) &&
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

/-- **The walk of function `j`**: its first gap's value index, its claims' count and its table
pointer's base. -/
noncomputable def monoFam (j : ℕ) : Option (ℕ × ℕ × Mode.Base) :=
  if (coreOf j).name == name% «child_claim_list_mono_loop0» then some (13, 136, .fr (cellJ j (.n 12)))
  else if (coreOf j).name == name% «child_claim_list_mono_loop1» then some (13, 17, .fr (cellJ j (.n 12)))
  else ((List.range 17).find? fun k => mlNames.getD k "" == (coreOf j).name).map
    fun k => (6, k, .hp (cellJ j (.n 0)) 14)

/-- The gaps of claims `0 … jj`, as bases. -/
noncomputable def gapBs (j g0 jj : ℕ) : List (Mode.Base × ℕ) :=
  (List.range (jj + 1)).map fun i => (.fr (cellJ j (.n (g0 + 10 * i))), 4)

/-- A base's cell inside the frame of function `j`. -/
noncomputable def baseIn (j : ℕ) : Mode.Base → Bool
  | .fr c => Nat.ble 2 c && Nat.blt c (fsN j)
  | .hp c _ => Nat.ble 2 c && Nat.blt c (fsN j)

/-- **A read of the walk of function `j` inside its caller's table.** -/
noncomputable def monoResB (j : ℕ) : Mode.Res → Bool
  | .sub a bs => decide (bs = anyTab) && decide (a.q.fp = 0) && decide (a.lo = .num 0) &&
      decide (a.hi = .num 4) && a.S == 1 && a.d == 0 &&
      match monoFam j with
      | some (g0, n, entB) => a.q.k % 4 == 0 && Nat.blt (a.q.k / 4) n &&
          (decide (a.q.bs = (entB, 1) :: gapBs j g0 (a.q.k / 4)) ||
            decide (a.q.bs = gapBs j g0 (a.q.k / 4) ++ [(entB, 1)])) &&
          (gapBs j g0 (a.q.k / 4)).all (fun p => baseIn j p.1) && baseIn j entB
      | none => false
  | _ => false

end

end LeanVM.Guest.Res
