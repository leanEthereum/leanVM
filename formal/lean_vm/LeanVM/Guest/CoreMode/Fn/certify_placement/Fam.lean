/-
  LeanVM.Guest.CoreMode.Fn.certify_placement.Fam

  `certify_placement`'s own residual families (`CoreMode/FnReg.lean`): its `group_base` through its hinted order.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public meta import LeanVM.Guest.CoreRef

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- `certify_placement`'s ranks' group values (`B1.Tables.cpRB`). -/
def cpRanks : List ℕ := [138, 149, 167, 185, 203, 221, 239, 257, 275]

/-- **`certify_placement`'s `group_base[0 .. 9)` through its hinted order** (`cpPerm`, the old route's `Res.cpSub` on core
names): the cell `[137]·g^k`, `k < 9`, one of `[137]·[v]` over its ranks' groups (`EndExec.cpPerm_inst`). -/
def cpPerm (fn : Fn) : CRes → Bool
  | .subP c cs => fn.name == name% «certify_placement» && decide (c.bases = [(137, 1)]) && decide (c.off < 9) &&
      decide (cs = cpRanks.map fun v ↦ ⟨[(137, 1), (v, 1)], 0⟩)
  | _ => false

end

end LeanVM.Guest.CoreMode

namespace LeanVM.Guest.CoreMode.Own.certify_placement

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its family**: its `group_base` through its hinted order (`cpPerm`). -/
noncomputable def fams : List (String × (Fn → CRes → Bool)) := [(name% «certify_placement», cpPerm)]

end

end LeanVM.Guest.CoreMode.Own.certify_placement
