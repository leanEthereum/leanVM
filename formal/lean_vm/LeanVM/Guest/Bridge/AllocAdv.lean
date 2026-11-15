/-
  LeanVM.Guest.Bridge.AllocAdv

  The advised buffers' hints: every `allocAdvice` is a buffer hint before its function's first jump,
  decided by the kernel over every compiled function.
-/

module

public import LeanVM.Guest.Bridge.ProgAlDefs
public import LeanVM.Guest.Bridge.AllocDefs
public import LeanVM.Guest.Bridge.ProgAlData

/-!
# The advised buffers' hints

`advChk F`: each `allocAdvice` of a function is a buffer hint (`isBuf`) at an offset before its
code's first jump (`nextJump code 0`), so every path through the function runs all of them, before
any call. `advChk_all`: every compiled function passes it.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- An advised buffer's hint, popping its size. -/
def isAdv : Prover.Exec.Hint → Bool
  | .allocAdvice .. => true
  | _ => false

/-- **Each `allocAdvice` is a buffer hint before the code's first jump.** -/
noncomputable def advChk (F : FnAl) : Bool :=
  (allocHints F.d).all fun q ↦ !isAdv q.2 || (decide (q.1 < nextJump F.code 0) && isBuf F.X q.2)

end

public section

theorem advChk_all : ∀ j < nFns, advChk (fnAl j) = true := by decide +kernel

end

end LeanVM.Guest.Bridge
