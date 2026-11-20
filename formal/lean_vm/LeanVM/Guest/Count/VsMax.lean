/-
  LeanVM.Guest.Count.VsMax

  `verify_bus_gkr`'s and `verify_tables`' largest bounds over their depths and heights,
  `verify_keccak`'s and the terminal's bounds, written out by the kernel (`kernel_lit`) through the
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

/-- `verify_bus_gkr`'s largest bound, at the search tree's lookups. -/
kernel_lit vbgMaxV : ℕ := B1.VerifySub.vbgMax fsFast
  (B1.VerifySub.glsKL fsFast fun p o => wSKFast (B1.Tables.glLoopName p o) - fsFast (B1.Tables.glLoopName p o))
  (wSKFast (name% verify_bus_gkr_loop0) - fsFast (name% verify_bus_gkr_loop0))

theorem vbgMax_eq : B1.VerifySub.vbgMax B2C.fs vsWords.KL vsWords.K8 = vbgMaxV := by
  rw [← vbgMaxV_eq, fsFast_eq, wSKFast_eq]; rfl

/-- `verify_tables`' largest bound, at the search tree's lookups. -/
kernel_lit vtMaxV : ℕ := B1.VerifySub.vtMax fsFast wSBFast
  (fsFast "shared_selector_tables" + (fsFast (name% shared_selector_tables_loop0) +
    15 * (wSKFast (name% shared_selector_tables_loop0) - fsFast (name% shared_selector_tables_loop0))) +
    max (max (wSBFast "sel_partial_nibble__L0") (wSBFast "sel_partial_nibble__L1"))
      (max (wSBFast "sel_partial_nibble__L2") (wSBFast "sel_partial_nibble__L3")))
  (wSKFast (name% verify_tables_loop0) - fsFast (name% verify_tables_loop0))

theorem vtMax_eq : B1.VerifySub.vtMax B2C.fs vsWords.Kf vsWords.Ksh vsWords.K10 = vtMaxV := by
  rw [← vtMaxV_eq, fsFast_eq, wSBFast_eq, wSKFast_eq]; dsimp only [vsWords, kSp]

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
