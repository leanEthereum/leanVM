/-
  LeanVM.Guest.Backend.Guest.B2.Final

  `B2SoundL` from the back end's compilation of the guest, given only the piece and the agreement
  check of `__loop2`, not yet cut.
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
`guestWorld_locs`). What remains is `__loop2`'s piece (`BigPieces`) and agreement check
(`BigLocs`).
-/

namespace LeanVM.Guest.Backend.B2

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core GuestPiece

@[expose] public section

/-- The places of function `j`'s values are `placedLocs (j - 1)`. -/
theorem gLocs_eq (hbig : BigPieces) {i : ℕ} (hi : i < coreProgram.length) :
    gLocs (coreOf (i + 1)).name = placedLocs i := by
  have hi' : i < guestTraced.length := by rw [guestTraced_length]; exact hi
  have h := guestWorld_locs (L := (fun _ => 0 : MemoryImage 0)) (U := fun _ _ => True) hbig hi'
  rw [List.getD_eq_getElem _ _ hi', guestTraced_getElem hi', world_locs] at h
  exact h

/-- **Every function's places agree with its certificate's cells**, given `BigPieces` and
`BigLocs`. -/
theorem locsAgree_compiled (hbig : BigPieces) (hlocs : BigLocs) : LocsAgree :=
  locsAgree_of fun i hi => by
    rw [gLocs_eq hbig hi]
    exact List.all_eq_true.mp (locsOk_all hlocs) i
      (List.mem_range'_1.mpr ⟨Nat.zero_le _, by rw [coreProgram_length] at hi; exact hi⟩)

/-- **B2 from the back end, compiled**: `End.B2SoundL`, given the piece and the agreement check of
`__loop2`. -/
theorem b2SoundL_compiled (hbig : BigPieces) (hlocs : BigLocs) : End.B2SoundL :=
  b2SoundL_backend (guest_compiles hbig) (locsAgree_compiled hbig hlocs)

end
end LeanVM.Guest.Backend.B2

/-- info: 'LeanVM.Guest.Backend.B2.b2SoundL_compiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.B2.b2SoundL_compiled
