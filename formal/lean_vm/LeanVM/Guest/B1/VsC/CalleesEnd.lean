/-
  LeanVM.Guest.B1.VsC.CalleesEnd

  `verify_sub`'s callees but `open_stacked` complete placed with their ends bounded.
-/

module

public import LeanVM.Guest.B1.VsC.RoundsSpecA1
public import LeanVM.Guest.B1.VsC.CertifyA
public import LeanVM.Guest.B1.VsC.CstA
public import LeanVM.Guest.B1.VsC.VkPM
public import LeanVM.Guest.Complete.FsSmall

/-!
# `verify_sub`'s callees, their ends bounded

`vsCalleesEndA_complete`: every field of `VsCalleesEndA` (`CalleesB.lean`) on a memory floor
`k ≥ 11`, every frame below `2^16`: the link callees within `2^22` of their cursors
(`vsLinkCalleesAB_of`), `certify_stack` and `ring_switch_target` within `2^20` (`cs_completeAB`,
`rst_completeAB`), `check_stack_terminal` and `verify_keccak` within `2^24` (`cst_completeAB`,
`verifyKeccakCompleteAB`). `vsCalleesEndA_b2c`: at the compiled frames, every one below `2^16`
(`fs_lt16`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

/-- **`verify_sub`'s callees but `open_stacked` complete placed, their ends bounded**, every frame
below `2^16`. -/
theorem vsCalleesEndA_complete {k : ℕ} (hk : 11 ≤ k) (hfs : FsSmall fs) : VsCalleesEndA fs al cert k :=
  ⟨vsLinkCalleesAB_of k (linkGrindLeft_complete hk) hfs, cs_completeAB hk hfs, cst_completeAB hk hfs,
    rst_completeAB k hfs, VerifySub.verifyKeccakCompleteAB hk hfs⟩

/-- **`verify_sub`'s callees but `open_stacked` complete placed at the compiled frames, their ends
bounded.** -/
theorem vsCalleesEndA_b2c {k : ℕ} (hk : 11 ≤ k) : VsCalleesEndA B2C.fs al B2C.cert k :=
  vsCalleesEndA_complete hk LeanVM.Guest.Complete.fs_lt16

end
end LeanVM.Guest.B1.VsC
