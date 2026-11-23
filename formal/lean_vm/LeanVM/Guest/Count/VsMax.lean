/-
  LeanVM.Guest.Count.VsMax

  `verify_bus_gkr`'s and `verify_tables`' largest bounds at `vsWords` (their count modules' `vbgMaxV`,
  `vtMaxV`), `verify_keccak`'s and the terminal's bounds, written out by the kernel (`kernel_lit`) through the
  search tree's lookups (`Count.Fast`), so that no number here changes with the guest.
-/

module

public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Count.VsWords
public import LeanVM.Guest.Count.Fast
public import LeanVM.Guest.B1.KeccakGkr.VkCW
public import LeanVM.Guest.B1.VerifySub.BoundsB
public import LeanVM.Guest.KernelLit

namespace LeanVM.Guest.Count

@[expose] public section

theorem vbgMax_eq : B1.Tables.vbgMax B2C.fs vsWords.vbg = vbgMaxV := vbgWordsMax_eq

theorem vtMax_eq : B1.Tables.vtMax B2C.fs vsWords.vt = vtMaxV := vtWordsMax_eq

/-- `verify_keccak`'s bound. -/
kernel_lit vkBoundV : ℕ := B1.VerifySub.vkBound

theorem vkBound_eq : B1.VerifySub.vkBound = vkBoundV := vkBoundV_eq

/-- The terminal's bound, at the search tree's lookups. -/
kernel_lit termBoundV : ℕ :=
  B1.VerifySub.termBound fsFast vsWords.Beqc vsWords.K15 vsWords.Bcs vsWords.Brs

theorem termBound_eq : B1.VerifySub.termBound B2C.fs vsWords.Beqc vsWords.K15 vsWords.Bcs vsWords.Brs =
    termBoundV := by
  rw [← termBoundV_eq, fsFast_eq]

end
end LeanVM.Guest.Count
