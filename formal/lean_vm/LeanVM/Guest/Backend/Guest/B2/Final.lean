/-
  LeanVM.Guest.Backend.Guest.B2.Final

  `B2SoundL` from the back end's compilation of the guest, with no hypothesis.
-/

module

public import LeanVM.Guest.Backend.Guest.Compiled
public import LeanVM.Guest.Backend.Guest.B2.Bridge
public import LeanVM.Guest.Backend.Guest.B2.LocsAll

/-!
# B2, the back end's

`b2SoundL_compiled`: `End.B2SoundL` from `b2SoundL_backend` with `GuestCompiles guestFns
guestSlots` (`guest_compiles`, the kernel-checked pieces) and `LocsAgree` (`locsOk_all`, the
kernel-checked agreement of every function's places with its certificate's cells, through
`guestWorld_locs`). It has no hypothesis.
-/

namespace LeanVM.Guest.Backend.B2

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core GuestPiece

@[expose] public section

/-- The places of function `j`'s values are `placedLocs (j - 1)`. -/
theorem gLocs_eq {i : ℕ} (hi : i < coreProgram.length) :
    gLocs (coreOf (i + 1)).name = placedLocs i := by
  have hi' : i < guestTraced.length := by rw [guestTraced_length]; exact hi
  have h := guestWorld_locs (L := (fun _ => 0 : MemoryImage 0)) (U := fun _ _ => True) hi'
  rw [List.getD_eq_getElem _ _ hi', guestTraced_getElem hi', world_locs] at h
  exact h

/-- **Every function's places agree with its certificate's cells.** -/
theorem locsAgree_compiled : LocsAgree :=
  locsAgree_of fun i hi => by
    rw [gLocs_eq hi]
    exact List.all_eq_true.mp locsOk_all i
      (List.mem_range'_1.mpr ⟨Nat.zero_le _, by rw [coreProgram_length] at hi; exact hi⟩)

/-- **B2 from the back end, compiled**: `End.B2SoundL`, proved from the back end's compilation of
the guest and the certificates' data, no certificate check. -/
theorem b2SoundL_compiled : End.B2SoundL :=
  b2SoundL_backend guest_compiles locsAgree_compiled

end
end LeanVM.Guest.Backend.B2

/-- info: 'LeanVM.Guest.Backend.B2.b2SoundL_compiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.B2.b2SoundL_compiled
