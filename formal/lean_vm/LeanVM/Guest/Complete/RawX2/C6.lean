/-
  LeanVM.Guest.Complete.RawX2.C6

  `main_loop2`'s chunk `c6`: it places nothing, hints no heap word, loads only its coverage cell and its
  claim, and calls only `main_loop2`, by the kernel.
-/

module

public import LeanVM.Guest.Complete.LoadVar
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Pack.main_loop2.Core23

namespace LeanVM.Guest.Complete

open LeanVM.Guest.Core LeanVM.Guest.Memory

public section

theorem l2_ck_c6 : Stmt.atomsAll (loadVarB l2Loads) Fn.«main_loop2».core.c6 = true ∧
    Stmt.pureList [name% «main_loop2»] Fn.«main_loop2».core.c6 = true := by
  decide +kernel

end
end LeanVM.Guest.Complete
