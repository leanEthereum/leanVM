/-
  LeanVM.Guest.B1.Da.VecCChk

  `da_vector`'s block, its shape (by kernel evaluation): flat, no dispatch or branch, two
  `HeapBuf`s of `14` words, its four calls, its loads (stores) into `zs` and `above_top`.
-/

module

public import LeanVM.Guest.B1.Da.VecFnChk
public import LeanVM.Guest.B1.Terminal.KidsDep
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_vector»

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1.Digest

@[expose] public section

/-- Not a dispatch. -/
def noDispatch : Stmt → Bool
  | .dispatch .. => false
  | _ => true

/-- `da_vector`'s calls. -/
def vecCalls : List (Option V × String × List V × List V) :=
  [(none, "da_factors__L13_L7_L0", [.n (val% «da_vector» "zs")], [.n (val% «da_vector» "top_factors")]),
    (none, "da_expand__L13_L7", [.n (val% «da_vector» "top_leaves~1"), .n (val% «da_vector» "top_factors"), .n (val% «da_vector» "zs"), .n (val% «da_vector» "above_top")], [.n (val% «da_vector» "top_leaves")]),
    (none, "da_factors__L6_L7_L128", [.n (val% «da_vector» "zs")], [.n (val% «da_vector» "cell_factors")]), (none, "da_column_offsets", [.n (val% «da_vector» "zs")], [.n (val% «da_vector» "offsets")])]

/-- `da_vector`'s loads: `zs[j]`, then `above_top[7 + i]`. -/
def vecLoads : List (V × ℕ) :=
  (List.range 14).map (fun j => (.n (val% «da_vector» "zs"), j)) ++ (List.range 7).map fun i => (.n (val% «da_vector» "above_top"), 7 + i)

/-- **`da_vector`'s block, its shape.** -/
noncomputable def vecCOk : Bool :=
  vecP.all Core.Stmt.flat && vecP.all noDispatch && vecP.all B1.notIteB &&
  decide (vecP.filterMap Stmt.addrS = []) &&
  decide (vecP.filterMap Stmt.allocSz = [(.n (val% «da_vector» "zs"), .inl 14), (.n (val% «da_vector» "above_top"), .inl 14)]) &&
  decide (vecP.filterMap Main.Stmt.callS = vecCalls) && decide (vecP.filterMap Stmt.loadS = vecLoads)

set_option maxRecDepth 100000 in
theorem vec_cok : vecCOk = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
