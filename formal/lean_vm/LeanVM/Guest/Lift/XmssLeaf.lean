/-
  LeanVM.Guest.Lift.XmssLeaf

  The leanXMSS check inline in `main_loop2` (its statements `9` to `321`) is a leaf block whose only
  loads are the claim's four words at the pointer `.n 65`, by the kernel over the core data.
-/

module

public import LeanVM.Guest.Data.Names
public import LeanVM.Guest.Memory.LiftPure
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«main_loop2»

/-!
# The check's loads, on the data

`segLoad`: a load from `.n 65` at an offset below `4`, and no other load. `loop2Seg_leafOk`: the
statements `9` to `321` of `main_loop2`'s body (`fn% «main_loop2»`) are atoms, branches and arms,
placing nothing, their loads `segLoad`'s. A module of its own: it imports only the data and the
check (`Sig.XmssSegData` names these statements `xSeg`; `Lift.Sig` concludes on the template).
-/

namespace LeanVM.Guest.Lift

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- A load of the claim's pointer `.n 65` at an offset below 4; no other load. -/
def segLoad : Atom → Bool
  | .load _ p off => decide (p = .n (val% «main_loop2» "s3#2")) && decide (off < 4)
  | _ => true

set_option maxRecDepth 100000 in
/-- **The check's statements of `main_loop2` load only the claim**, by the kernel. -/
theorem loop2Seg_leafOk : Stmt.leafOkList segLoad (((fn% «main_loop2»).body.drop (pos% «main_loop2» "pp")).take (span% «main_loop2» "pp" "s5#0")) =
    true := by
  decide +kernel

/-- `main_loop2`'s body has `329` statements. -/
theorem main_loop2_length : (fn% «main_loop2»).body.length = 329 := by
  decide +kernel

end
end LeanVM.Guest.Lift
