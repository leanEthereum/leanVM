/-
  LeanVM.Guest.Exact.SpWots.C1

  `sp_wots`'s chunk `c1`: no computed hint and no call, by the kernel.
-/

module

public import LeanVM.Guest.Exact.Atoms
public import LeanVM.Guest.Pack.sp_wots.Core4

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core

public section

theorem sp_wots_c1 : Stmt.atomsAll (fun a => !isComputed a) Fn.«sp_wots».core.c1 = true ∧
    Stmt.blockCallees Fn.«sp_wots».core.c1 = [] := by
  decide +kernel

end
end LeanVM.Guest.Memory
