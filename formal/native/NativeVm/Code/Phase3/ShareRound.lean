module

public import NativeVm.Code.Phase3.ShareRest

/-!
# The bytecode share: one round

`shRound` refines `shareRoundM` (`shRound_refines`): from `shInv k acc` (after `k` rounds: the
challenges so far at `slotR`, the claim in `tmpR`, `r13 = 4 - k`, `r14` at the next challenge) to
`shInv (k + 1)`.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Field NativeVm.Transcript NativeVm.Code

/-- The rounds' invariant after `k` rounds with the sumcheck's accumulator `acc`, from the start
`s0`, the share `share`. -/
def shInv (env : Env) (inp : Input) (s0 : QState) (share : EW) (k : Nat) (acc : Array EW × EW)
    (t : TState) (s : QState) : Prop :=
  CodeRel env t s ∧ Inputs env inp s.mem ∧ acc.1.size = k ∧
    EWArr s.mem (wd env.work slotR.off) acc.1 ∧ EWAt s.mem (wd env.work shClaimW) acc.2 ∧
    s.reg .r13 = (4 - k).toUInt64 ∧ s.reg .r14 = wd env.work (slotR.off + 2 * k) ∧
    EWAt s.mem (wd env.work shareR.off) share ∧ Step3 env allRegs shW s0 s

/-- Element `k` of the slot. -/
def slotElR (k : Nat) : Region := ⟨slotR.off + 2 * k, 2⟩

/-- The slot's first `k` elements. -/
def slotLowR (k : Nat) : Region := ⟨slotR.off, 2 * k⟩

theorem regs_sub_all (regs : List Reg64) : regs ⊆ allRegs := fun r _ ↦ by
  cases r <;> simp [allRegs]

variable {env : Env} {inp : Input} {s s' : QState}

/-- A part's run as the share's. -/
theorem sh_step {regs : List Reg64} {ws : List Region} (h : Step3 env regs ws s s')
    (hw : ∀ r ∈ ws, ∃ q ∈ shW, Within r q) : Step3 env allRegs shW s s' :=
  step3_within (h.mono (regs_sub_all _) fun _ h ↦ h) hw

/-- **One round.** -/
theorem shRound_refines {s0 : QState} {share : EW} {k : Nat} (hk : k < 4)
    (acc : Array EW × EW) :
    Refines (shInv env inp s0 share k acc) shRound (shareRoundM acc)
      (fun acc' t s ↦ shInv env inp s0 share (k + 1) acc' t s)
      (fun s' ↦ Step3 env allRegs shW s0 s') := by
  rintro t s ⟨hc, hi, hsz, hslot, hcl, h13, h14, hsh, hst⟩
  have hrdi := hc.rdi
  unfold shRound shareRoundM
  refine WP.blk_cons (WP.mono (readTo_spec (r := shConstR) (k := shConstW) (by sh_reg) le_rfl
    (by sh_reg) hc hi) (fun s1 ⟨c, t1, hr1, hc1, he1, hs1⟩ ↦ ?_)
    (fun s1 ⟨hr1, hs1⟩ ↦ ⟨Refines.run_bind_none hr1, hst.trans (sh_step hs1 (by sh_reg))⟩))
  have hi1 : Inputs env inp s1.mem := hi.step3 (by sh_reg) hs1 hrdi
  refine WP.blk_cons (WP.mono (readTo_spec (r := shTailR) (k := shTailW) (by sh_reg) le_rfl
    (by sh_reg) hc1 hi1) (fun s2 ⟨tt, t2, hr2, hc2, he2, hs2⟩ ↦ ?_)
    (fun s2 ⟨hr2, hs2⟩ ↦ ⟨by rw [Refines.run_bind_some hr1, Refines.run_bind_none hr2],
      hst.trans ((sh_step hs1 (by sh_reg)).trans (sh_step hs2 (by sh_reg)))⟩))
  have hi2 : Inputs env inp s2.mem := hi1.step3 (by sh_reg) hs2 hc1.rdi
  refine WP.blk_cons (WP.mono (WP.frame (sampleChallengeM_spec hc2))
    (fun s3 ⟨⟨x, t3, hr3, hc3, h9, h10, hk3⟩, hd3, _⟩ ↦ ?_) (fun _ ⟨h, _⟩ ↦ h.elim))
  have hs3 : Step3 env clobbers [] s2 s3 := Step3.ofKeeps hk3 hd3
  have hi3 : Inputs env inp s3.mem := hi2.step3 (by simp) hs3 hc2.rdi
  have h14' : s3.reg .r14 = wd env.work (slotR.off + 2 * k) := by
    rw [hs3.regs .r14 (by decide), hs2.regs .r14 (by decide), hs1.regs .r14 (by decide), h14]
  have h13' : s3.reg .r13 = (4 - k).toUInt64 := by
    rw [hs3.regs .r13 (by decide), hs2.regs .r13 (by decide), hs1.regs .r13 (by decide), h13]
  refine wp_storePair (r := slotElR k) (a := slotR.off + 2 * k) (by unfold slotElR; sh_reg) le_rfl
    (by simp only [slotElR, Region.stop]; omega) h14' hi3 fun s4 hw4 he4 hreg4 ↦ ?_
  have hs4 : Step3 env allRegs [slotElR k] s3 s4 := hw4.step
  have hok4 : ∀ r ∈ [slotElR k], Ok3 r := by unfold slotElR; sh_reg
  have hi4 : Inputs env inp s4.mem := hi3.step3 hok4 hs4 hc3.rdi
  have hc4 : CodeRel env t3 s4 := hc3.wrote3 hi3 hok4 hw4
  -- the three parts so far, as runs writing `L`
  have hL1 : Step3 env allRegs [shConstR, shTailR, slotElR k] s s1 :=
    hs1.mono (regs_sub_all _) (by simp)
  have hL2 : Step3 env allRegs [shConstR, shTailR, slotElR k] s1 s2 :=
    hs2.mono (regs_sub_all _) (by simp)
  have hL3 : Step3 env allRegs [shConstR, shTailR, slotElR k] s2 s3 :=
    hs3.mono (regs_sub_all _) (by simp)
  have hL4 : Step3 env allRegs [shConstR, shTailR, slotElR k] s3 s4 :=
    hs4.mono (regs_sub_all _) (by simp)
  have hokL : ∀ r ∈ [shConstR, shTailR, slotElR k], Ok3 r := by unfold slotElR; sh_reg
  have hcl4 : EWAt s4.mem (wd env.work shClaimW) acc.2 :=
    ewat_keep (hL1.trans (hL2.trans (hL3.trans hL4))) hi hokL (q := shClaimR) (by sh_reg)
      (by unfold slotElR; sh_reg) le_rfl (by sh_reg) hcl
  have hM2 : Step3 env allRegs [shTailR, slotElR k] s1 s4 :=
    (hs2.mono (regs_sub_all _) (by simp)).trans ((hs3.mono (regs_sub_all _) (by simp)).trans
      (hs4.mono (regs_sub_all _) (by simp)))
  have hc4' : EWAt s4.mem (wd env.work shConstW) c :=
    ewat_keep hM2 hi1 (by unfold slotElR; sh_reg) (q := shConstR) (by sh_reg)
      (by unfold slotElR; sh_reg) le_rfl (by sh_reg) he1
  have hM3 : Step3 env allRegs [slotElR k] s2 s4 :=
    (hs3.mono (regs_sub_all _) (by simp)).trans hs4
  have ht4 : EWAt s4.mem (wd env.work shTailW) tt :=
    ewat_keep hM3 hi2 hok4 (q := shTailR) (by sh_reg)
      (by unfold slotElR; sh_reg) le_rfl (by sh_reg) he2
  refine shRest_spec (k := k) (x := x) (hreg4 ▸ hc3.rdi) hc4.workPtr3 hi4 (by rw [hreg4]; exact h9)
    (by rw [hreg4]; exact h10) (by rw [hreg4]; exact h13') (by rw [hreg4]; exact h14') hk hcl4
    hc4' ht4 fun s5 hw5 _ hcl5 h135 h145 ↦ ?_
  have hok5 : ∀ r ∈ [shClaimR], Ok3 r := by sh_reg
  have hs5 : Step3 env allRegs [shClaimR] s4 s5 := hw5.step
  have hL : Step3 env allRegs [shConstR, shTailR, slotElR k, shClaimR] s s5 :=
    (hL1.trans (hL2.trans (hL3.trans hL4))).mono (fun _ h ↦ h) (by simp) |>.trans
      (hs5.mono (fun _ h ↦ h) (by simp))
  have hokL' : ∀ r ∈ [shConstR, shTailR, slotElR k, shClaimR], Ok3 r := by unfold slotElR; sh_reg
  refine ⟨(acc.1.push x, polyEval #[c, acc.2 + sumE #[tt], tt] x), t3, ?_, hc4.wrote3 hi4 hok5 hw5, hi4.step3 hok5 hs5 hc4.rdi, by simp [hsz], ?_,
    hcl5, h135, h145, ?_, hst.trans (sh_step hL (by unfold slotElR; sh_reg))⟩
  · rw [Refines.run_bind_some hr1, Refines.run_bind_some hr2, Refines.run_bind_some hr3]
    rfl
  · refine ewarr_push ?_ ?_
    · exact ewarr_keep hL hi hokL' (q := slotLowR k) (by unfold slotLowR; sh_reg)
        (by unfold slotLowR slotElR; sh_reg) (by simp [slotLowR])
        (by simp only [slotLowR, Region.stop]; omega) hslot
    · rw [wd_wd, hsz]
      have := ewat_keep hs5 hi4 hok5 (q := slotElR k) (by unfold slotElR; sh_reg)
        (by unfold slotElR; sh_reg) (by simp [slotElR]) (by simp only [slotElR, Region.stop]; omega) he4
      rwa [h9, h10] at this
  · exact ewat_keep hL hi hokL' (q := shareR) (by sh_reg) (by unfold slotElR; sh_reg) le_rfl
      (by sh_reg) hsh

end NativeVm.Code.P3
