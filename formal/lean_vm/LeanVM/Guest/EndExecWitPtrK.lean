/-
  LeanVM.Guest.EndExecWitPtrK

  `WitPtrK`, the heap witness pointers no spine pins in `K`, from the carried facts.
-/

module

public import LeanVM.Guest.EndExecW
public import LeanVM.Guest.Complete.WitCellsG

/-!
# The heap witness pointers no spine pins

`Complete.WitPtrK` at b2c's layout for every `al` and `D` (`witPtrK_carryA`), by `EndExec.witPtrK_carry`:
each such pointer is in `K` by the carried values (`Res.carryG`'s `witAtomC`), written from offset `0`.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Guest LeanVM.Guest.Memory LeanVM.Guest.EndExec

public section

/-- **`WitPtrK` from the carried facts.** -/
theorem witPtrK_carryA {al : String → Bool} {D : Ref → RefD} : WitPtrK ⟨B2C.fs, al, B2C.H, B2C.C, B2C.cert⟩ D :=
  fun _ hR _ _ hI _ _ _ _ ht _ hf _ _ _ _ ha hpk ↦ witPtrK_carry hR hI ht hf ha hpk

end

end LeanVM.Guest.Complete
