/-
  LeanVM.Guest.Exact.SpWots.C0b

  `sp_wots`'s chunk `c0`, statements 51 to 90: no computed hint and no call, by the kernel.
-/

module

public import LeanVM.Guest.Exact.Atoms
public import LeanVM.Guest.Pack.sp_wots.Core5

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core

public section

theorem sp_wots_c0b : Stmt.atomsAll (fun a => !isComputed a) ((Fn.«sp_wots».core.c0.drop 51).take 40) = true ∧
    Stmt.blockCallees ((Fn.«sp_wots».core.c0.drop 51).take 40) = [] := by
  decide +kernel

end
end LeanVM.Guest.Memory
