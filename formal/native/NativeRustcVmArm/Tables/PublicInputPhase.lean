module

public import NativeRustcVmArm.Code.Vm.LayoutWPlacement.Names
public import NativeRustcVmArm.Code.Vm.MultilinearEvalByOfMultilinearEval.Names
public import NativeRustcVmArm.Code.Vm.PublicInputPhase.Names
public import NativeRustcVmArm.Code.Vm.PushClaim.Names
public import NativeRustcVmArm.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmArm.Tables.PublicInputPhase.Limb0

/-!
# `public_input_phase` meets its contract

`b0` saves the registers in the 608-byte frame and squeezes the challenge (`squeeze_call`); from
there the frame goes on from the squeeze's state (`Fr.rebase`). `b1` zeroes the point and asks the
layout for the memory placement's variable count `v`; `b2` takes the point's size `max v 1` and
rejects `v > 31` (the contract's bound rules it out); then the two limbs (`limb0`, `limb1`).
-/

namespace NativeRustcVmArm.Tables.PublicInputPhase

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.PublicInputPhase
open NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeVm.Model
open NativeRustcVm.Layout (claimsBytes ClaimsWAt claimCap pointCap columnCountW)
open LeanVM.Protocol.Verifier (memory0 memory1)

public section

variable [Host] {k : Nat}

/-- **`public_input_phase` meets its contract.** -/
theorem publicInputPhase_spec (hp : Placed code k)
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hpl : ∀ L, Spec (Labels.label NativeRustcVmArm.Vm.LayoutWPlacement.entryLabel) (LayoutWPlacementPre L)
      (LayoutWPlacementPost L))
    (hmle : Spec (Labels.label NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) MleOfMultilinearEvalPre
      MleOfMultilinearEvalPost)
    (hpush : ∀ cs, Spec (Labels.label NativeRustcVmArm.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs))
    {a : DecArea} {s : TState} {L : LayoutW} {pub : Vector UInt64 4} {cs : Array ColumnClaimW} :
    Spec (Labels.label NativeRustcVmArm.Vm.PublicInputPhase.entryLabel) (PublicInputPhasePre a s L pub cs)
      (PublicInputPhasePost a s L pub cs) := by
  intro m0 hpre
  rw [show Labels.label NativeRustcVmArm.Vm.PublicInputPhase.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.PublicInputPhase.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.PublicInputPhase.entryOffset) NativeRustcVmArm.Vm.PublicInputPhase.entry_at]
  have hpre' := hpre
  obtain ⟨hS, hrc, hts, htok, hco, hcs, hLin, hL, hvc, hPin, hP⟩ := hpre'
  have hN := hS.2.1
  have c : Sumcheck.Ctx m0 m0.regs.X0.toBitVec a publicInputPhaseStack 608 :=
    Bus.Gkr.ctx_of hS hrc hts htok le_N rfl
  have hwf := Bus.wf_env0 hS (F := 608) le_N
  have hm : Match (Bus.env0 m0 608) entryS m0 := Bus.match_entry hS le_N rfl
  -- `b0`: the prologue, `squeeze`.
  refine exec_then (b0_in_code.trans hp.1 (by simp [b0])) run_b0 hwf hm fun st hm1 hpc ↦ ?_
  have hm1' : Match (Bus.env0 m0 608) (Bus.after b0 entryS) st.data := by
    rw [Bus.after_eq run_b0]; exact hm1
  obtain ⟨hsp0, hsl0, hmem0, hk0, h0, h19, h20, h23⟩ := ok_b0
  have hfr0 : Fr m0 608 publicInputPhaseStack slots keep (fun _ ↦ False) st.data :=
    Fr.ofPrologue hN le_N hm1' hwf hsp0 hsl0 slots_le hmem0 hk0
  have hts1 := tstate_fr hfr0 hS htok (fun _ h ↦ h.elim) hts
  have e0 : st.data.regs.X0.toBitVec = m0.regs.X0.toBitVec := hm1'.regs .X0 _ h0
  have hpc' : st.pc = Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel ∧ retOf st.data = Host.addrOf (k + NativeRustcVmArm.Vm.PublicInputPhase.b1Offset) := hpc
  have hfrT : Fr m0 608 publicInputPhaseStack slots keep
      (fun q ↦ InRange m0.regs.X0.toBitVec tstateBytes q) st.data :=
    Bus.Fr.mono hfr0 fun _ h ↦ h.elim
  refine squeeze_call c hsq hfrT (fun q hq ↦ c.not_rc_tstate hq) le_squeeze keep_callee slots_le
    (fun q hq ↦ Bus.Gkr.tstate_not_frame c hq) (fun _ h ↦ h) hpc' e0 hts1
    fun m2 hfr2 hts2 hc0 hc1 hcs2 _ ↦ ?_
  -- From the squeeze's state on.
  have hfrR := Fr.rebase hfr2
  have hk2 : Kept m0.dmem m2.dmem := hfr2.kept
  have hS1 := StackOk.rebase hS hk2
  have hnts : ∀ {x : BitVec 64} {n : Nat}, NoWrap x n →
      Apart x n m0.regs.X0.toBitVec tstateBytes →
      ∀ j < n, ¬InRange m0.regs.X0.toBitVec tstateBytes (x + BitVec.ofNat 64 j) :=
    fun hnw hap j hj ↦ Bus.not_inRange_of_apart hap hnw hts.footprint.1.2 hj
  have hcs2' : ClaimsWAt m2.dmem m0.regs.X3.toBitVec cs :=
    NativeRustcVm.Tables.ClaimsWAt.of_same hcs
      (same_in hfr2 hS hco.2.1 hco.2.2.2.2.1 (hnts hco.2.1 hco.2.2.1))
  have hL2 : NativeRustcVm.Layout.LayoutWAt m2.dmem m0.regs.X1.toBitVec L :=
    NativeRustcVm.Tables.LayoutWAt.of_same hL (same_in hfr2 hS hLin.1.2 hLin.2.1
      (hnts hLin.1.2 (hLin.2.2 ⟨m0.regs.X0.toBitVec, tstateBytes⟩ (by simp))))
  have hP2 : NativeRustcVm.WordsAt m2.dmem m0.regs.X2.toBitVec pub.toList :=
    NativeRustcVm.Tables.WordsAt.of_same hP (same_in hfr2 hS hPin.1.2 hPin.2.1
      (hnts hPin.1.2 (hPin.2.2 ⟨m0.regs.X0.toBitVec, tstateBytes⟩ (by simp)))) (by simp)
  -- `b1`: the point zeroed, `LayoutW::placement`.
  have hwf2 := Bus.wf_frame hS1 le_N hfrR.kept
  have hm2 := Bus.match_frame hS1 le_N rfl hfrR.sp
  refine exec_then (b1_in_code.trans hp.1 (by simp [b1])) run_b1 hwf2 hm2 fun st3 hm3 hpc3 ↦ ?_
  have hm3' : Match (Env.ofMachine m2 [(base (reb m0 m2.dmem) 608, 608)]) (Bus.after b1 sF)
      st3.data := by
    rw [Bus.after_eq run_b1]; exact hm3
  obtain ⟨hsp3, hFW3, hk3, hz3, g0, g1, g19, g20, g21, g22, g23⟩ := ok_b1
  have hfr3 := Bus.Fr.block hfrR hN le_N hm3' hwf2 hsp3 hFW3 hk3 slots_le
  have hzw : Bus.FrameWords st3.data.dmem (base m0 608) zeroWords := by
    intro p hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
    have := Bus.wordAt_write hm3' (r := 0) rfl (by simp at hj; omega)
      (hz3 j (List.mem_range.mp hj))
    exact this
  have x0 : st3.data.regs.X0 = m0.regs.X1 := by
    rw [show st3.data.regs.X0 = st3.data.regs.getXReg .X0 from rfl, Bus.Gkr.reg_of hm3' g0,
      hcs2 .X23 rfl, Bus.Gkr.reg_of hm1' h23]
    rfl
  have x1 : st3.data.regs.X1.toNat = 0 := by
    show (st3.data.regs.getXReg .X1).toBitVec.toNat = 0
    rw [Bus.Gkr.reg_lit hm3' g1]; rfl
  have hpc3' : st3.pc = Labels.label NativeRustcVmArm.Vm.LayoutWPlacement.entryLabel ∧
      retOf st3.data = Host.addrOf (k + NativeRustcVmArm.Vm.PublicInputPhase.b2Offset) := hpc3
  have hL3 : NativeRustcVm.Layout.LayoutWAt st3.data.dmem m0.regs.X1.toBitVec L :=
    NativeRustcVm.Tables.LayoutWAt.of_same hL2 (same_fr hfr3 hS1 hLin.1.2 hLin.2.1)
  refine Fr.leaf hfr3 hN le_place keep_callee slots_le (fun _ h ↦ h.elim) (hpl L)
    (fun m m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun _ h ↦ h.elim, hq.2.2.2⟩) hpc3'
    ⟨by rw [x1]; decide, by rw [x0]; exact hL3,
      by rw [x0]; exact Bus.Fr.readable hfr3 ⟨fun i h ↦ hk2 _ (hLin.1.1 i h), hLin.1.2⟩⟩
    fun m4 hfr4 hq4 hcs4 ↦ ?_
  -- After `placement`: the variable count.
  have hvc' : (L.placement 0).variableCount ≤ 31 := hvc
  have hvL : vcOf L ≤ 31 := hvc
  have hv4 : (m4.regs.getXReg .X0).toBitVec.toNat = vcOf L := by
    show (m4.regs.X0).toNat = _
    rw [hq4.1, x1, toNat_toUInt64 (by omega)]
    rfl
  have hzw4 : Bus.FrameWords m4.dmem (base m0 608) zeroWords :=
    Bus.FrameWords.call (N' := 0) (outs := fun _ ↦ False) hzw hfr3.sp (by have := le_N; omega)
      (fun p hp ↦ by obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp; simp at hj ⊢; omega)
      (fun _ h ↦ h.elim) (NativeRustcVm.SameOutside.mono hq4.2.2.1 fun _ h ↦ h.elim)
  -- `b2`: the point's size, `v ≤ 31`.
  refine Bus.Gkr.Fr.runBlock hS1 le_N rfl hfr4 (b2_in_code.trans hp.1 (by simp [b2])) run_b2
    rfl rfl (by decide) (by decide) fun st5 hfr5 hd5 hm5 hpc5 ↦ ?_
  have hm5' : Match (Env.ofMachine m4 [(base (reb m0 m2.dmem) 608, 608)]) (Bus.after b2 sF)
      st5.data := by
    rw [Bus.after_eq run_b2]; exact hm5
  obtain ⟨-, -, -, f19, f20, f21, f22, f23⟩ := ok_b2
  simp only [PcOk, SBool.eval, Sym.eval, Env.ofMachine_regs, cmp_ult_lit _ _ (by decide : 31 < 2 ^ 64),
    cmp_eq_lit _ _ (by decide : 31 < 2 ^ 64), UInt64.toNat, hv4] at hpc5
  split at hpc5
  next h => simp at h; omega
  have x23 : (st5.data.regs.getXReg .X23).toNat = max (vcOf L) 1 := by
    show (st5.data.regs.getXReg .X23).toBitVec.toNat = _
    rw [hm5'.regs .X23 _ f23]
    simp only [Sym.eval, SBool.eval, Env.ofMachine_regs, cmp_ult_lit _ _ (by decide : 1 < 2 ^ 64),
      cmp_eq_lit _ _ (by decide : 1 < 2 ^ 64), UInt64.toNat, hv4]
    split
    next h => simp at h; omega
    next h => simp at h ⊢; omega
  refine Bus.Gkr.at_pc hpc5 (limb0 hp hmle hpush hpre ?_)
  refine ⟨Fr.rebase (m0 := reb m0 m2.dmem) hfr5, ?_, ?_, ?_, ?_, x23, by rw [hd5]; exact hzw4,
    NativeRustcVm.Tables.ClaimsWAt.of_same hcs2' (same_fr hfr5 hS1 hco.2.1 hco.2.2.2.2.1),
    NativeRustcVm.Tables.WordsAt.of_same hP2 (same_fr hfr5 hS1 hPin.1.2 hPin.2.1) (by simp),
    tstate_fr hfr5 hS1 htok (fun _ h ↦ h.elim) hts2, fun p hp ↦ hfr5.kept p (hk2 p hp),
    (NativeRustcVm.SameOutside.trans hfr2.same hfr5.same).mono fun q hq ↦
      hq.elim (fun h ↦ h.elim Or.inl fun h ↦ Or.inr (Or.inl h)) fun h ↦ h.elim Or.inl False.elim⟩
  · rw [Bus.Gkr.reg_of hm5' f19, hcs4 .X19 rfl, Bus.Gkr.reg_of hm3' g19, hcs2 .X19 rfl,
      Bus.Gkr.reg_of hm1' h19]; rfl
  · rw [Bus.Gkr.reg_of hm5' f20, hcs4 .X20 rfl, Bus.Gkr.reg_of hm3' g20, hcs2 .X20 rfl,
      Bus.Gkr.reg_of hm1' h20]; rfl
  · rw [Bus.Gkr.reg_of hm5' f21, hcs4 .X21 rfl, Bus.Gkr.reg_of hm3' g21]; exact hc0
  · rw [Bus.Gkr.reg_of hm5' f22, hcs4 .X22 rfl, Bus.Gkr.reg_of hm3' g22]; exact hc1

end

end NativeRustcVmArm.Tables.PublicInputPhase
