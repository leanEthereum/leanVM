/-
  LeanVM.Guest.Exact.MainLoop2.C1b

  `main_loop2`'s chunk `c1`, after its first three statements: no computed hint, and no callee but `main_loop2` itself, by the kernel.
-/

module

public import LeanVM.Guest.Exact.Atoms
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Pack.main_loop2.Core23

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core

public section

theorem main_loop2_c1b : Stmt.atomsAll (fun a => !isComputed a) (Fn.«main_loop2».core.c1.drop 3) = true ∧
    (Stmt.blockCallees (Fn.«main_loop2».core.c1.drop 3)).all (· == name% «main_loop2») = true := by
  decide +kernel

end
end LeanVM.Guest.Memory
