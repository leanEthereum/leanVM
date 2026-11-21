/-
  LeanVM.Guest.Exact.SpWots.C0c

  `sp_wots`'s chunk `c0`, statements 91 on: no computed hint and no call, by the kernel.
-/

module

public import LeanVM.Guest.Exact.Atoms
public import LeanVM.Guest.Pack.sp_wots.Core5

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core

public section

theorem sp_wots_c0c : Stmt.atomsAll (fun a => !isComputed a) (Fn.«sp_wots».core.c0.drop 91) = true ∧
    Stmt.blockCallees (Fn.«sp_wots».core.c0.drop 91) = [] := by
  decide +kernel

end
end LeanVM.Guest.Memory
