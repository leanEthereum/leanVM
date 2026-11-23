/-
  LeanVM.Guest.Exact.MainLoop2.C2

  `main_loop2`'s chunk `c2`: no computed hint, and no callee but `main_loop2` itself, by the kernel.
-/

module

public import LeanVM.Guest.Exact.Atoms
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Pack.main_loop2.Core23

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core

public section

theorem main_loop2_c2 : Stmt.atomsAll (fun a => !isComputed a) Fn.«main_loop2».core.c2 = true ∧
    (Stmt.blockCallees Fn.«main_loop2».core.c2).all (· == name% «main_loop2») = true := by
  decide +kernel

end
end LeanVM.Guest.Memory
