/-
  LeanVM.Guest.B1.VsC.CalleesU

  `verify_sub`'s callees but `open_stacked`, their ends bounded with no premise on the cursor.
-/

module

public import LeanVM.Guest.B1.VsC.CalleesEnd

/-!
# `verify_sub`'s callees, their ends bounded unconditionally

`VsCalleesEndA`'s bounds are `EndLe c β e` (`c < 2^60 → e ≤ c + 2^β`), which says nothing near `2^60`.
The producers give `FsSmall fs → e ≤ c + 2^β` at every cursor, so at frames below `2^16` the bound
needs no premise: **`VsCalleesEndU`**, the fields at `EndU β` (`e ≤ c + 2^β`), `2^21` for the link's
callees, `2^20` for `certify_stack` and `ring_switch_target`, `2^24` for `check_stack_terminal` and
`verify_keccak`; **`vsCalleesEndU_complete`** (`11 ≤ k`, `FsSmall fs`), **`vsCalleesEndU_b2c`** at the
compiled frames.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1.Link

@[expose] public section

/-- The end `e` within `2^β` of the cursor `c`. -/
abbrev EndU (β c e : ℕ) : Prop := e ≤ c + 2 ^ β

variable (fs : String → ℕ) (al : String → Bool) (cert : String → V → ℕ) (k : ℕ)

/-- **`verify_sub`'s callees but `open_stacked`, their ends within `2^β` of their cursors.** -/
structure VsCalleesEndU : Prop where
  rounds_L1_L0 : LinkRoundsCompleteAE fs al cert k 1 0 "link_rounds__L1_L0" (EndU 21)
  rounds_L6_L0 : LinkRoundsCompleteAE fs al cert k 6 0 "link_rounds__L6_L0" (EndU 21)
  rounds_L7_L0 : LinkRoundsCompleteAE fs al cert k 7 0 "link_rounds__L7_L0" (EndU 21)
  rounds_L8_L1 : LinkRoundsCompleteAE fs al cert k 8 1 "link_rounds__L8_L1" (EndU 21)
  rounds_L9_L1 : LinkRoundsCompleteAE fs al cert k 9 1 "link_rounds__L9_L1" (EndU 21)
  rounds_L10_L1 : LinkRoundsCompleteAE fs al cert k 10 1 "link_rounds__L10_L1" (EndU 21)
  squeeze_packed : SqueezePackedCompleteAE fs al cert k (EndU 21)
  terminal : ∀ w, 19 ≤ w → w ≤ 24 → LinkTerminalCompleteAE fs al cert k w (ltNames.getD (w - 19) "") (EndU 21)
  certify_stack : CertifyStackCompleteAE fs al cert k (EndU 20)
  check_stack_terminal : CheckStackTerminalCompleteAE fs al cert k (EndU 24)
  ring_switch_target : RingSwitchTargetCompleteAE fs al cert k (EndU 20)
  verify_keccak : VerifyKeccakCompleteAE fs al cert k (EndU 24)

variable {fs al cert k}

/-- **`verify_sub`'s callees but `open_stacked`, their ends bounded unconditionally**, every frame below
`2^16`. -/
theorem vsCalleesEndU_complete (hk : 11 ≤ k) (hfs : FsSmall fs) : VsCalleesEndU fs al cert k :=
  have m : ∀ β c e : ℕ, (FsSmall fs → e ≤ c + 2 ^ β) → EndU β c e := fun _ _ _ h => h hfs
  have h := linkGrindLeft_complete (fs := fs) (al := al) (cert := cert) hk
  ⟨(link_rounds_L1_L0_completeA k).mono (m 21), (link_rounds_L6_L0_completeA k).mono (m 21),
    (link_rounds_L7_L0_completeA k).mono (m 21),
    (link_rounds_L8_L1_completeA_of k h.loop_L8 h.last_L8_L1 h.last_L8_L2 h.last_L8_L3).mono (m 21),
    (link_rounds_L9_L1_completeA_of k h.loop_L9 h.last_L9_L1 h.last_L9_L2 h.last_L9_L3).mono (m 21),
    (link_rounds_L10_L1_completeA_of k h.loop_L10 h.last_L10_L1 h.last_L10_L2 h.last_L10_L3).mono (m 21),
    (squeeze_packed_completeA k).mono (m 21), fun w h1 h2 => (link_terminal_completeA k w h1 h2).mono (m 21),
    (cs_completeAE hk).mono (m 20), (cst_completeAE hk).mono (m 24), (rst_completeAE k).mono (m 20),
    (VerifySub.vkFromLayerAE (VerifySub.KL.keccakLayerCompleteA hk)).mono (m 24)⟩

/-- **`verify_sub`'s callees but `open_stacked` at the compiled frames, their ends bounded
unconditionally.** -/
theorem vsCalleesEndU_b2c {k : ℕ} (hk : 11 ≤ k) : VsCalleesEndU B2C.fs al B2C.cert k :=
  vsCalleesEndU_complete hk LeanVM.Guest.Complete.fs_lt16

end
end LeanVM.Guest.B1.VsC
