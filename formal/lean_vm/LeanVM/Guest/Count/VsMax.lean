/-
  LeanVM.Guest.Count.VsMax

  `verify_bus_gkr`'s and `verify_tables`' largest bounds over their depths and heights,
  `verify_keccak`'s and the terminal's bounds, by the kernel, through the search tree's lookups
  (`Count.Fast`).
-/

module

public import LeanVM.Guest.Count.VsWords
public import LeanVM.Guest.Count.Fast
public import LeanVM.Guest.B1.KeccakGkr.VkCW

namespace LeanVM.Guest.Count

@[expose] public section

set_option maxRecDepth 100000 in
theorem vbgMax_eq : B1.VerifySub.vbgMax B2C.fs vsWords.K29 vsWords.R vsWords.K8 = 50050 := by
  unfold B1.VerifySub.vbgMax
  dsimp only [vsWords, kGr]
  rw [← fsFast_eq, ← wSBFast_eq, ← wSKFast_eq]
  decide +kernel

set_option maxRecDepth 100000 in
theorem vtMax_eq : B1.VerifySub.vtMax B2C.fs vsWords.Kf vsWords.Ksh vsWords.K10 = 38467 := by
  unfold B1.VerifySub.vtMax
  dsimp only [vsWords]
  rw [← fsFast_eq, ← wSBFast_eq, ← wSKFast_eq]
  decide +kernel

set_option maxRecDepth 100000 in
theorem vkBound_eq : B1.VerifySub.vkBound = 65770 := by
  show B2C.fs "verify_keccak" + 440 + 61728 = 65770
  rw [← fsFast_eq]; decide +kernel

set_option maxRecDepth 100000 in
theorem termBound_eq : B1.VerifySub.termBound B2C.fs vsWords.Beqc vsWords.K15 vsWords.Bcs vsWords.Brs = 30208 := by
  show B2C.fs "check_opening_terminal" + 146 + 3 * 184 + (32 * 19 + B2C.fs "__loop14") +
    (B2C.fs "selector_tables" + 512) + 101 * 157 + (B2C.fs "ring_switch_weight" + 2240 + 8142) = 30208
  rw [← fsFast_eq]; decide +kernel

end
end LeanVM.Guest.Count
