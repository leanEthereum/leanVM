/-
  LeanVM.Guest.CoreMode.Fn.certify_stack.Fam

  `certify_stack`'s own residual family (`CoreMode/FnReg.lean`): its `group_at` through its hinted order.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Renumber

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- `certify_stack`'s `group_at` (`B1.Stack.csBody`'s value `164`). -/
def csAt : ℕ := 164

/-- Rank `r`'s hinted group's value (`B1.Stack.csRanks`' slots: rank `0` at `165`, rank `r ≥ 1` at `165 + 11 + 18 (r - 1)`). -/
def csSlot (r : ℕ) : ℕ := if r = 0 then 165 else 165 + 11 + 18 * (r - 1)

/-- Its ranks' hinted groups, `csSlot r`, `r < 8`. -/
def csRankVals : List ℕ := [165, 176, 194, 212, 230, 248, 266, 284]

/-- **`certify_stack`'s `group_at[0 .. 8)` through its hinted order** (`csPerm`): the cell `[group_at]·g^k`, `k < 8`,
one of `[group_at]·[v]` over its ranks' groups (`EndExec.csPerm_instA`). -/
def csPerm : CRes → Bool
  | .subP c cs => decide (c.bases = [(csAt, 1)]) && decide (c.off < 8) &&
      decide (cs = csRankVals.map fun v ↦ ⟨[(csAt, 1), (v, 1)], 0⟩)
  | _ => false

end

end LeanVM.Guest.CoreMode

namespace LeanVM.Guest.CoreMode.Own.certify_stack

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its family**: its `group_at` through its hinted order (`csPerm`). -/
noncomputable def fams : List (String × (Fn → CRes → Bool)) := [(name% «certify_stack», fun _ r ↦ csPerm r)]

end

end LeanVM.Guest.CoreMode.Own.certify_stack
