/-
  LeanVM.Guest.Exact.MainLoop2.C3

  `main_loop2`'s chunk `c3`: no computed hint, and no callee but `main_loop2` itself, by the kernel.
-/

module

public import LeanVM.Guest.Exact.Atoms
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Pack.main_loop2.Core23

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core

public section

theorem main_loop2_c3 : Stmt.atomsAll (fun a => !isComputed a) Fn.«main_loop2».core.c3 = true ∧
    (Stmt.blockCallees Fn.«main_loop2».core.c3).all (· == name% «main_loop2») = true := by
  decide +kernel

end
end LeanVM.Guest.Memory
