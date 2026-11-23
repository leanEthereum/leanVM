/-
  LeanVM.Guest.CoreMode.Fn.certify_placement.Fam

  `certify_placement`'s own residual families (`CoreMode/FnReg.lean`): its `group_base` through its hinted order.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public meta import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«certify_placement»

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- `certify_placement`'s ranks' group values (`B1.Tables.cpRB`). -/
def cpRanks : List ℕ :=
  [val% «certify_placement» "gi@1", val% «certify_placement» "gi@2", val% «certify_placement» "gi@3", val% «certify_placement» "gi@4",
    val% «certify_placement» "gi@5", val% «certify_placement» "gi@6", val% «certify_placement» "gi@7", val% «certify_placement» "gi@8", val% «certify_placement» "gi@9"]

/-- **`certify_placement`'s `group_base[0 .. 9)` through its hinted order** (`cpPerm`): the
cell `[group_base]·g^k`, `k < 9`, one of `[group_base]·[v]` over its ranks' groups (`EndExec.cpPerm_inst`). -/
def cpPerm (fn : Fn) : CRes → Bool
  | .subP c cs => fn.name == name% «certify_placement» && decide (c.bases = [(val% «certify_placement» "group_base", 1)]) &&
      decide (c.off < 9) && decide (cs = cpRanks.map fun v ↦ ⟨[(val% «certify_placement» "group_base", 1), (v, 1)], 0⟩)
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
