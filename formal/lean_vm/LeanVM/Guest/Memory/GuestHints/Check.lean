/-
  LeanVM.Guest.Memory.GuestHints.Check

  The guest's heap hint check by function, decided by the kernel on ranges of the core IR
  (`GuestHints/Part*`).
-/

module

public import LeanVM.Guest.Memory.HintsCheck
public import LeanVM.Guest.Memory.Family
public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings

/-!
# The guest's heap hint check

`hintsX`: the three loop helpers whose heap hints write through a pointer their caller computes,
`main`'s claim tables' duplicate slots and its children's carried claims, into `main`'s buffers.
`chkH j fn`: unless `fn` is one of them, it has no heap hint (`quickR`) or its heap hints rest on
its path (`hintsOkL`); it does not call `main`, and unless it is `main`, none of them but itself
(`calleeOk`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

/-- The loop helpers writing into `main`'s buffers through a computed pointer. -/
def hintsX : List String := [name% «main_loop0», name% «main_loop1», name% «main_loop4»]

/-- What `chkH` asks of a callee of `fn`. -/
def calleeOk (fn : Fn) (g : String) : Bool :=
  g != "main" && (fn.name == "main" || g == fn.name || !hintsX.contains g)

/-- **The check of function `j`.** -/
noncomputable def chkH (_ : ℕ) (fn : Fn) : Bool :=
  if hintsX.contains fn.name then calleesR (calleeOk fn) fn.body
  else quickR (calleeOk fn) fn.body || (hintsOkL [] fn.body && calleesR (calleeOk fn) fn.body)

end
end LeanVM.Guest.Memory
