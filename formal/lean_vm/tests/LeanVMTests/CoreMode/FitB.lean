import LeanVM.Guest.CoreMode.Core

/-!
# A callee's mode signature against its heap signature, rejected

`fitB G h na nr` (a call's callee on the function route) accepts a mode signature `G` of a callee of heap
signature `h` only when every mode precondition over the arguments is one of `h`'s, the header cells are
entry cells, and every heap guarantee is one `G` promises. Each case the kernel must reject sits beside the
matching accepted one, so the check is not vacuous.
-/

namespace LeanVM.Guest.CoreMode.Test

open LeanVM.Guest LeanVM.Guest.Core

/-- A callee's mode signature: its header and first argument written at entry, nothing else. -/
def gNone : Mode.Sig :=
  { pc := 0, entry := [0, 1, 2], self := none, pre := [], preR := [], term := [], ret := [], post := [],
    postR := [], postL := [], preP := [], postP := [], postLP := [], retV := [], postT := [], postC := [] }

/-- The cell `p·g^0` over the first argument's word, as a mode product and as a heap cell. -/
def m0 : Mode.Mono := ⟨0, 0, [(.fr 2, 1)]⟩

def c0 : CCell := ⟨[(0, 1)], 0⟩

example : fitB gNone {} 1 0 = true := by decide +kernel

-- The header cells must be entry cells.
example : fitB { gNone with entry := [1, 2] } {} 1 0 = false := by decide +kernel

-- A mode precondition over the argument: accepted when the heap signature has it, rejected when not.
example : fitB { gNone with pre := [m0] } { pre := [c0] } 1 0 = true := by decide +kernel

example : fitB { gNone with pre := [m0] } {} 1 0 = false := by decide +kernel

-- A heap guarantee: accepted when the mode signature promises it, rejected when not.
example : fitB { gNone with post := [m0] } { post := [c0] } 1 0 = true := by decide +kernel

example : fitB gNone { post := [c0] } 1 0 = false := by decide +kernel

-- A heap signature with ghost slots needs a pointer base per ghost.
example : fitB gNone { ghosts := 1 } 1 0 = false := by decide +kernel

end LeanVM.Guest.CoreMode.Test
