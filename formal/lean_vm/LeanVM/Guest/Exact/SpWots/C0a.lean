/-
  LeanVM.Guest.Exact.SpWots.C0a

  `sp_wots`'s chunk `c0`, statements 0 to 50: no computed hint and no call, by the kernel.
-/

module

public import LeanVM.Guest.Exact.Atoms
public import LeanVM.Guest.Pack.sp_wots.Core5

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core

public section

theorem sp_wots_c0a : Stmt.atomsAll (fun a => !isComputed a) (Fn.«sp_wots».core.c0.take 51) = true ∧
    Stmt.blockCallees (Fn.«sp_wots».core.c0.take 51) = [] := by
  decide +kernel

end
end LeanVM.Guest.Memory
