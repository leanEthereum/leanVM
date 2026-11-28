/-
  LeanVM.Guest.B1.VsC.RoundsSpecA1

  `link_rounds__L{8,9,10}_L1` complete placed: the link callees `verify_sub` enters.
-/

module

public import LeanVM.Guest.B1.VsC.RoundsSpecA
public import LeanVM.Guest.B1.VsC.RoundsLoopA1
public import LeanVM.Guest.B1.VsC.CalleesA
import LeanVM.Guest.CoreRef

/-!
# `link_rounds` at one bit of grind, placed

The fields of `LinkGrindLeft` at every `k ≥ 11` (the grinds' range checks read the memory's first
`2^11` words): the loop helpers by `lrLoopA1`, the last arms with rounds by `lrLastA_placed1`, each
specialization's body checked by the kernel (`lrLChecks1`, `lrlChecks1A`). Then
`linkGrindLeft_complete` and `vsLinkCalleesA_complete`: the `link` field of `VsCalleesCompleteA`;
`vsCalleesCompleteA_of_rest`: the structure from its other five fields.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.B1.Link LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Protocol.Verifier

@[expose] public section

variable {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ}

set_option maxRecDepth 100000 in
theorem lrLChecks1_L8 : lrLChecks1 8 "__loop0_link_rounds__L8_L1" = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **`link_rounds__L8_L1`'s loop helper completes placed.** -/
theorem lrLoopA_L8_L1 {k : ℕ} (hk : 11 ≤ k) : LrLoopA fs al cert k 8 1 "__loop0_link_rounds__L8_L1" :=
  lrLoopA1 hk (by norm_num) (by norm_num) (by norm_num)
    (coreProgram_find?_at (j := idx% «link_rounds__L8_L1_loop0») rfl) (by decide +kernel) rfl
    lrLoop_L8_L1_body lrLChecks1_L8

set_option maxRecDepth 100000 in
theorem lrl_L8_L1_L1_checksA : lrlChecks1A 8 1 (lrLastBody 8 1 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **`link_rounds_last__L8_L1_L1` completes placed.** -/
theorem lrLastA_L8_L1_L1 {k : ℕ} (hk : 11 ≤ k) :
    LrLastA fs al cert k 8 1 "link_rounds_last__L8_L1_L1" 1 :=
  lrLastA_placed1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (coreProgram_find?_at (j := idx% «link_rounds_last__L8_L1_L1») rfl) (by decide +kernel) rfl
    lrl_L8_L1_L1_body lrl_L8_L1_L1_checksA

set_option maxRecDepth 100000 in
theorem lrl_L8_L1_L2_checksA : lrlChecks1A 8 2 (lrLastBody 8 1 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **`link_rounds_last__L8_L1_L2` completes placed.** -/
theorem lrLastA_L8_L1_L2 {k : ℕ} (hk : 11 ≤ k) :
    LrLastA fs al cert k 8 1 "link_rounds_last__L8_L1_L2" 2 :=
  lrLastA_placed1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (coreProgram_find?_at (j := idx% «link_rounds_last__L8_L1_L2») rfl) (by decide +kernel) rfl
    lrl_L8_L1_L2_body lrl_L8_L1_L2_checksA

set_option maxRecDepth 100000 in
theorem lrl_L8_L1_L3_checksA : lrlChecks1A 8 3 (lrLastBody 8 1 3) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **`link_rounds_last__L8_L1_L3` completes placed.** -/
theorem lrLastA_L8_L1_L3 {k : ℕ} (hk : 11 ≤ k) :
    LrLastA fs al cert k 8 1 "link_rounds_last__L8_L1_L3" 3 :=
  lrLastA_placed1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (coreProgram_find?_at (j := idx% «link_rounds_last__L8_L1_L3») rfl) (by decide +kernel) rfl
    lrl_L8_L1_L3_body lrl_L8_L1_L3_checksA

set_option maxRecDepth 100000 in
theorem lrLChecks1_L9 : lrLChecks1 9 "__loop0_link_rounds__L9_L1" = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **`link_rounds__L9_L1`'s loop helper completes placed.** -/
theorem lrLoopA_L9_L1 {k : ℕ} (hk : 11 ≤ k) : LrLoopA fs al cert k 9 1 "__loop0_link_rounds__L9_L1" :=
  lrLoopA1 hk (by norm_num) (by norm_num) (by norm_num)
    (coreProgram_find?_at (j := idx% «link_rounds__L9_L1_loop0») rfl) (by decide +kernel) rfl
    lrLoop_L9_L1_body lrLChecks1_L9

set_option maxRecDepth 100000 in
theorem lrl_L9_L1_L1_checksA : lrlChecks1A 9 1 (lrLastBody 9 1 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **`link_rounds_last__L9_L1_L1` completes placed.** -/
theorem lrLastA_L9_L1_L1 {k : ℕ} (hk : 11 ≤ k) :
    LrLastA fs al cert k 9 1 "link_rounds_last__L9_L1_L1" 1 :=
  lrLastA_placed1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (coreProgram_find?_at (j := idx% «link_rounds_last__L9_L1_L1») rfl) (by decide +kernel) rfl
    lrl_L9_L1_L1_body lrl_L9_L1_L1_checksA

set_option maxRecDepth 100000 in
theorem lrl_L9_L1_L2_checksA : lrlChecks1A 9 2 (lrLastBody 9 1 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **`link_rounds_last__L9_L1_L2` completes placed.** -/
theorem lrLastA_L9_L1_L2 {k : ℕ} (hk : 11 ≤ k) :
    LrLastA fs al cert k 9 1 "link_rounds_last__L9_L1_L2" 2 :=
  lrLastA_placed1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (coreProgram_find?_at (j := idx% «link_rounds_last__L9_L1_L2») rfl) (by decide +kernel) rfl
    lrl_L9_L1_L2_body lrl_L9_L1_L2_checksA

set_option maxRecDepth 100000 in
theorem lrl_L9_L1_L3_checksA : lrlChecks1A 9 3 (lrLastBody 9 1 3) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **`link_rounds_last__L9_L1_L3` completes placed.** -/
theorem lrLastA_L9_L1_L3 {k : ℕ} (hk : 11 ≤ k) :
    LrLastA fs al cert k 9 1 "link_rounds_last__L9_L1_L3" 3 :=
  lrLastA_placed1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (coreProgram_find?_at (j := idx% «link_rounds_last__L9_L1_L3») rfl) (by decide +kernel) rfl
    lrl_L9_L1_L3_body lrl_L9_L1_L3_checksA

set_option maxRecDepth 100000 in
theorem lrLChecks1_L10 : lrLChecks1 10 "__loop0_link_rounds__L10_L1" = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **`link_rounds__L10_L1`'s loop helper completes placed.** -/
theorem lrLoopA_L10_L1 {k : ℕ} (hk : 11 ≤ k) : LrLoopA fs al cert k 10 1 "__loop0_link_rounds__L10_L1" :=
  lrLoopA1 hk (by norm_num) (by norm_num) (by norm_num)
    (coreProgram_find?_at (j := idx% «link_rounds__L10_L1_loop0») rfl) (by decide +kernel) rfl
    lrLoop_L10_L1_body lrLChecks1_L10

set_option maxRecDepth 100000 in
theorem lrl_L10_L1_L1_checksA : lrlChecks1A 10 1 (lrLastBody 10 1 1) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **`link_rounds_last__L10_L1_L1` completes placed.** -/
theorem lrLastA_L10_L1_L1 {k : ℕ} (hk : 11 ≤ k) :
    LrLastA fs al cert k 10 1 "link_rounds_last__L10_L1_L1" 1 :=
  lrLastA_placed1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (coreProgram_find?_at (j := idx% «link_rounds_last__L10_L1_L1») rfl) (by decide +kernel) rfl
    lrl_L10_L1_L1_body lrl_L10_L1_L1_checksA

set_option maxRecDepth 100000 in
theorem lrl_L10_L1_L2_checksA : lrlChecks1A 10 2 (lrLastBody 10 1 2) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **`link_rounds_last__L10_L1_L2` completes placed.** -/
theorem lrLastA_L10_L1_L2 {k : ℕ} (hk : 11 ≤ k) :
    LrLastA fs al cert k 10 1 "link_rounds_last__L10_L1_L2" 2 :=
  lrLastA_placed1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (coreProgram_find?_at (j := idx% «link_rounds_last__L10_L1_L2») rfl) (by decide +kernel) rfl
    lrl_L10_L1_L2_body lrl_L10_L1_L2_checksA

set_option maxRecDepth 100000 in
theorem lrl_L10_L1_L3_checksA : lrlChecks1A 10 3 (lrLastBody 10 1 3) = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **`link_rounds_last__L10_L1_L3` completes placed.** -/
theorem lrLastA_L10_L1_L3 {k : ℕ} (hk : 11 ≤ k) :
    LrLastA fs al cert k 10 1 "link_rounds_last__L10_L1_L3" 3 :=
  lrLastA_placed1 hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (coreProgram_find?_at (j := idx% «link_rounds_last__L10_L1_L3») rfl) (by decide +kernel) rfl
    lrl_L10_L1_L3_body lrl_L10_L1_L3_checksA

/-- **What was left of the link callees holds** on every memory floor `k ≥ 11`. -/
theorem linkGrindLeft_complete {k : ℕ} (hk : 11 ≤ k) : LinkGrindLeft fs al cert k :=
  ⟨lrLoopA_L8_L1 hk, lrLastA_L8_L1_L1 hk, lrLastA_L8_L1_L2 hk, lrLastA_L8_L1_L3 hk,
    lrLoopA_L9_L1 hk, lrLastA_L9_L1_L1 hk, lrLastA_L9_L1_L2 hk, lrLastA_L9_L1_L3 hk,
    lrLoopA_L10_L1 hk, lrLastA_L10_L1_L1 hk, lrLastA_L10_L1_L2 hk, lrLastA_L10_L1_L3 hk⟩

/-- **The link callees `verify_sub` enters complete placed** (the `link` field of
`VsCalleesCompleteA`), on every memory floor `k ≥ 11`. -/
theorem vsLinkCalleesA_complete {k : ℕ} (hk : 11 ≤ k) : VsLinkCalleesA fs al cert k :=
  vsLinkCalleesA_of k (linkGrindLeft_complete hk)

/-- **`verify_sub`'s callees complete placed** from the five fields beside the link. -/
theorem vsCalleesCompleteA_of_rest {k : ℕ} (hk : 11 ≤ k) (hcs : CertifyStackCompleteA fs al cert k)
    (hst : CheckStackTerminalCompleteA fs al cert k) (hrs : RingSwitchTargetCompleteA fs al cert k)
    (hvk : VerifyKeccakCompleteA fs al cert k) (hos : ∀ m, m ≤ 14 → OpenStackedCompleteA fs al cert k m) :
    VsCalleesCompleteA fs al cert k :=
  ⟨vsLinkCalleesA_complete hk, hcs, hst, hrs, hvk, hos⟩

end
end LeanVM.Guest.B1.VsC
