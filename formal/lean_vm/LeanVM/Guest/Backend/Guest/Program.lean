/-
  LeanVM.Guest.Backend.Guest.Program

  The guest as the back end's input: `coreProgram`'s functions with their traces.
-/

module

public import LeanVM.Guest.Backend.Guest.Traced
public import LeanVM.Guest.CoreData

/-!
# The guest's traced program

`guestTraced` is `coreProgram`'s function `j` with entry `j` of `GuestData.guestInfo`
(`Guest/Traced.lean`, written by `lake exe guest-traced`): the allocation trace of its expansion,
every value renamed as `coreProgram` names it, its return cells and its `loopSource`. Its core
program is `coreProgram` by construction (`guestTraced_core`). It is apart from `Guest/World.lean`
so that the kernel's checks of the guest's compilation (`Guest/Piece/`) import no proof.
-/

namespace LeanVM.Guest.Backend

open LeanVM.Guest LeanVM.Guest.Core GuestData

@[expose] public section

/-- **The back end's input for the guest**: `coreProgram`'s functions, each with its trace, its
return cells and its `loopSource`. -/
noncomputable def guestTraced : List TracedFn :=
  (coreProgram.zip guestInfo).map fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩

/-- **The back end's input for the guest has `coreProgram`'s functions.** -/
theorem guestTraced_core : guestTraced.map (·.core) = coreProgram := by
  rw [guestTraced, List.map_map]
  exact List.map_fst_zip (by rw [coreProgram_length, guestInfo_length])

end
end LeanVM.Guest.Backend
