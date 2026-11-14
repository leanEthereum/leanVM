/-
  LeanVM.Guest.EndExecCDeref

  `DerefPow` from the reference step alone.
-/

module

public import LeanVM.Guest.EndExecX

/-!
# A `DEREF`'s address on the reference

The reference step at a `DEREF` with offset `o` reads the word at `p · g^o`, `p` its pointer cell's
first limb, so `p · g^o = g^i` for some `i < 2^κ ≤ 2^28` (`refOk_of_pow`'s `DEREF` case): that is
`DerefPow`, for every hint track invariant (`derefPow_all`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Guest
open LeanVM.Prover.Exec

public section

/-- **A `DEREF`'s pointer times `g^o` is a power below `maxCells`** at every state of the tracks. -/
theorem derefPow_all (Y : Ref → St → Prop) : DerefPow Y :=
  fun r hr _ hC _ _ _ _ _ hon hop ↦
    refOk_of_pow (logMemorySize_le_28 (e := r.exec) hr.size) hC hon.2.1 hon.2.2 hop trivial

end

end LeanVM.Guest.EndExec
