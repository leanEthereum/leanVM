/-
  LeanVM.Guest.Complete.FsSmall

  Every frame size is below `2^16`.
-/

module

public import LeanVM.Guest.B2C.Defs
import LeanVM.Guest.B2C.Cells

/-!
# The frames are small

`fs_lt16`: every frame size `B2C.fs` is below `2^16`, the compiled frames and `main`'s by the kernel
(`B2C.fs_lt` bounds them by `2^30`). A callee's end past its cursor is then bounded by its loops'
iterations.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Guest.Memory

@[expose] public section

/-- Every compiled frame below `2^16`, by the kernel. -/
theorem fsAt_lt16 (j : ℕ) : fsAt j < 2 ^ 16 := by
  have hall : Data.frameSizes.all (fun x ↦ decide (x < 2 ^ 16)) = true := by decide +kernel
  unfold fsAt
  rw [List.getD_eq_getElem?_getD]
  cases hj : Data.frameSizes[j]? with
  | none => simp
  | some x => simpa using of_decide_eq_true (List.all_eq_true.mp hall x (List.mem_of_getElem? hj))

theorem mainFrame_lt16 : B2C.mainFrame < 2 ^ 16 := by unfold B2C.mainFrame; decide +kernel

theorem fsN_lt16 (j : ℕ) : B2C.fsN j < 2 ^ 16 := by
  unfold B2C.fsN
  cases Nat.beq j 1
  · exact max_lt (by norm_num) (fsAt_lt16 j)
  · exact mainFrame_lt16

/-- **Every frame below `2^16`.** -/
theorem fs_lt16 (f : String) : B2C.fs f < 2 ^ 16 := by
  unfold B2C.fs
  split
  · exact mainFrame_lt16
  · exact max_lt (by norm_num) (fsAt_lt16 _)
  · unfold B2C.tailFs
    split
    · exact lt_of_le_of_lt (min_le_left _ _) (fsN_lt16 _)
    · norm_num

end
end LeanVM.Guest.Complete
