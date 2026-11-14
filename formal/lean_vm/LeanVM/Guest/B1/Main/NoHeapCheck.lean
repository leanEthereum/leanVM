/-
  LeanVM.Guest.B1.Main.NoHeapCheck

  No witness hint of the program is on the `heap_sizes` stream, by the kernel.
-/

module

public import LeanVM.Guest.Pops
public import LeanVM.Guest.Hints
public import LeanVM.Guest.B2C.ShareSound

/-!
# No witness hint on `heap_sizes`

`atomNoHeap`: an atom is no witness hint on `heap_sizes`; `coreProgram_noHeap`: every atom of every function passes it.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- An atom that is no witness hint on `heap_sizes`. -/
def atomNoHeap : Atom → Bool
  | .hint (.witness s _) => s != Hints.heapSizeStream
  | _ => true

/-- **No atom of the program is a witness hint on `heap_sizes`.** -/
theorem coreProgram_noHeap : coreProgram.all (fun fn => (B2C.lAtoms fn.body).all atomNoHeap) = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Main
