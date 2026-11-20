/-
  LeanVM.Guest.Count.VsMax

  `verify_bus_gkr`'s and `verify_tables`' largest bounds over their depths and heights,
  `verify_keccak`'s and the terminal's bounds, by the kernel, through the search tree's lookups
  (`Count.Fast`).
-/

module

public import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Count.VsWords
public import LeanVM.Guest.Count.Fast
public import LeanVM.Guest.B1.KeccakGkr.VkCW
public import LeanVM.Guest.B1.VerifySub.BoundsB

namespace LeanVM.Guest.Count

@[expose] public section

set_option maxRecDepth 100000 in
theorem vbgMax_eq : B1.VerifySub.vbgMax Deployed.fs vsWords.K29 vsWords.R vsWords.K8 = 29669 := by
  unfold B1.VerifySub.vbgMax
  dsimp only [vsWords, kGr]
  rw [← fsFast_eq, ← wSBFast_eq, ← wSKFast_eq]
  decide +kernel

set_option maxRecDepth 100000 in
theorem vtMax_eq : B1.VerifySub.vtMax Deployed.fs vsWords.Kf vsWords.Ksh vsWords.K10 = 31245 := by
  unfold B1.VerifySub.vtMax
  dsimp only [vsWords]
  rw [← fsFast_eq, ← wSBFast_eq, ← wSKFast_eq]
  decide +kernel

set_option maxRecDepth 100000 in
theorem vkBound_eq : B1.VerifySub.vkBound = 55936 := by
  show Deployed.fs "verify_keccak" + 440 + 52647 = 55936
  rw [← fsFast_eq]; decide +kernel

set_option maxRecDepth 100000 in
theorem termBound_eq : B1.VerifySub.termBound Deployed.fs vsWords.Beqc vsWords.K15 vsWords.Bcs vsWords.Brs = 28991 := by
  show Deployed.fs "check_opening_terminal" + 177 + 4 * 184 + (32 * 19 + Deployed.fs (name% check_opening_terminal_loop0)) +
    (Deployed.fs "selector_tables" + 512) + 94 * 157 + (Deployed.fs "ring_switch_weight" + 2240 + 8142) = 28991
  rw [← fsFast_eq]; decide +kernel

end
end LeanVM.Guest.Count
