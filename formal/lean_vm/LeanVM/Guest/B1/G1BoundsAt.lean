/-
  LeanVM.Guest.B1.G1BoundsAt

  Group 1's pure callees' words at frame sizes agreeing with `fsOf` but at `main`, from the static
  checker.
-/

module

public import LeanVM.Guest.B1.OsCalleesPlaced
public import LeanVM.Guest.Memory.GuestBoundsAt
public import LeanVM.Guest.Memory.GuestSize

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Guest.Memory

@[expose] public section

/-- **Group 1's pure callees' words at frame sizes agreeing with `fsOf` but at `main`**, constants
but the loops', which grow with their end's exponent. -/
noncomputable def g1BoundsOf (fs' : String → ℕ) (h : FsAgree fs') : G1Bounds fs' where
  foldB := fun _ => 68
  fold := opening_fold_totalLe_at h
  canonicalB := fun _ => fs' "assert_canonical"
  canonical := assert_canonical_totalLe fs'
  loop6B := fun x => logG x * 32
  loop6 := loop6_totalLeOn_at h
  loop9B := fun x => logG x * 78
  loop9 := loop9_totalLeOn_at h
  finalMsg4B := fun _ => 72
  finalMsg4 := opening_final_message_L4_totalLe_at h
  finalMsg8B := fun _ => 124
  finalMsg8 := opening_final_message_L8_totalLe_at h
  finalMsg16B := fun _ => 228
  finalMsg16 := opening_final_message_L16_totalLe_at h
  finalMsg32B := fun _ => 436
  finalMsg32 := opening_final_message_L32_totalLe_at h
  rowWeights4B := fun _ => 57
  rowWeights4 := opening_row_weights_L4_L0_totalLe_at h
  rowWeights6B := fun _ => 205
  rowWeights6 := opening_row_weights_L6_L1_totalLe_at h
  foldFinal2B := fun _ => 92
  foldFinal2 := fold_final_msg_L2_totalLe_at h
  foldFinal3B := fun _ => 137
  foldFinal3 := fold_final_msg_L3_totalLe_at h
  foldFinal4B := fun _ => 194
  foldFinal4 := fold_final_msg_L4_totalLe_at h
  foldFinal5B := fun _ => 275
  foldFinal5 := fold_final_msg_L5_totalLe_at h

/-- `g1BoundsOf` at `fsOf`. -/
noncomputable def g1BoundsFsOf : G1Bounds fsOf := g1BoundsOf fsOf fun _ _ _ _ => rfl

/-- `fsOf "assert_canonical"` is `10`. -/
theorem fsOf_assert_canonical : fsOf "assert_canonical" = 10 := by
  rw [← (show (coreProgram[1]'(by rw [coreProgram_length]; decide)).name = "assert_canonical" by decide +kernel),
    fsOf_getElem]
  rfl

end
end LeanVM.Guest.B1
