/-
  LeanVM.Guest.B1.Da.VecCChk

  `da_vector`'s block, its shape (by kernel evaluation): flat, no dispatch or branch, two
  `HeapBuf`s of `14` words, its four calls, its loads (stores) into `zs` and `above_top`.
-/

module

public import LeanVM.Guest.B1.Da.VecFnChk
public import LeanVM.Guest.B1.Terminal.KidsDep

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1.Digest

@[expose] public section

/-- Not a dispatch. -/
def noDispatch : Stmt → Bool
  | .dispatch .. => false
  | _ => true

/-- `da_vector`'s calls. -/
def vecCalls : List (Option V × String × List V × List V) :=
  [(none, "da_factors__L13_L7_L0", [.n 1], [.n 24]),
    (none, "da_expand__L13_L7", [.n 25, .n 24, .n 1, .n 16], [.n 26]),
    (none, "da_factors__L6_L7_L128", [.n 1], [.n 27]), (none, "da_column_offsets", [.n 1], [.n 28])]

/-- `da_vector`'s loads: `zs[j]`, then `above_top[7 + i]`. -/
def vecLoads : List (V × ℕ) :=
  (List.range 14).map (fun j => (.n 1, j)) ++ (List.range 7).map fun i => (.n 16, 7 + i)

/-- **`da_vector`'s block, its shape.** -/
noncomputable def vecCOk : Bool :=
  vecP.all Core.Stmt.flat && vecP.all noDispatch && vecP.all B1.notIteB &&
  decide (vecP.filterMap Stmt.addrS = []) &&
  decide (vecP.filterMap Stmt.allocSz = [(.n 1, .inl 14), (.n 16, .inl 14)]) &&
  decide (vecP.filterMap Main.Stmt.callS = vecCalls) && decide (vecP.filterMap Stmt.loadS = vecLoads)

set_option maxRecDepth 100000 in
theorem vec_cok : vecCOk = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
