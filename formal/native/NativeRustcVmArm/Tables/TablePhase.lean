module

public import NativeRustcVmArm.Code.Vm.BitLength.Names
public import NativeRustcVmArm.Code.Vm.Dot.Names
public import NativeRustcVmArm.Code.Vm.Powers.Names
public import NativeRustcVmArm.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.Code.Vm.TablePhase.Names
public import NativeRustcVmArm.Code.Vm.TableSumcheck.Names
public import NativeRustcVmArm.Tables.TablePhase.Tail

/-!
# `table_phase` meets its contract

`b0` saves the registers in the 128-byte frame and calls `bit_length(3)` (`2`); `b1` grinds
`grindingBits 4 = 0` bits; `b2` leaves with `0` on a failed grind; `b3` squeezes `ξ`
(`squeeze_call`); from `b4` on, `tail`.
-/

namespace NativeRustcVmArm.Tables.TablePhase

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TablePhase
open NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Tables
open NativeRustcVmArm.Sumcheck (Ctx At)

public section

variable [Host] {k : Nat}

/-- **`table_phase` meets its contract.** -/
theorem tablePhase_spec (hp : Placed code k)
    (hbl : Spec (Labels.label NativeRustcVmArm.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgrind : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hpow : Spec (Labels.label NativeRustcVmArm.Vm.Powers.entryLabel) PowersPre PowersPost)
    (hdot : Spec (Labels.label NativeRustcVmArm.Vm.Dot.entryLabel) DotPre DotPost)
    (hsum : ∀ a s heights bus, Spec (Labels.label NativeRustcVmArm.Vm.TableSumcheck.entryLabel)
      (TableSumcheckPre a s heights bus) (TableSumcheckPost a s heights bus))
    {a : DecArea} {s : TState} {L : LayoutW} {bus : BusResultW} :
    Spec (Labels.label NativeRustcVmArm.Vm.TablePhase.entryLabel) (TablePhasePre a s L bus) (TablePhasePost a s L bus) := by
  intro m0 hpre
  rw [show Labels.label NativeRustcVmArm.Vm.TablePhase.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.TablePhase.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.TablePhase.entryOffset) NativeRustcVmArm.Vm.TablePhase.entry_at]
  have hpre' := hpre
  obtain ⟨hS, hrc, hT, hts0, htok, heo, hRt, hRe, hLin, hL, hBin, hB⟩ := hpre'
  have hN := hS.2.1
  have c : Ctx m0 m0.regs.X0.toBitVec a tablePhaseStack 128 :=
    Bus.Gkr.ctx_of hS hrc hts0 htok N_ge rfl
  have hor : ∀ q, outs m0 q → ¬InRange rcAddr 192 q := fun q hq ↦
    hq.elim c.not_rc_tstate (Bus.Gkr.out_not_rc c heo)
  have hof : ∀ q, outs m0 q → ¬InRange (base m0 128) 128 q := fun q hq ↦
    hq.elim (Bus.Gkr.tstate_not_frame c) (Bus.Gkr.out_not_frame c heo)
  have hwf := Bus.wf_env0 hS (F := 128) N_ge
  have hm : Match (Bus.env0 m0 128) entryS m0 := Bus.match_entry hS N_ge rfl
  -- `b0`: the prologue, `bit_length(3)`.
  refine exec_then (b0_in_code.trans hp.1 (by simp [b0])) run_b0 hwf hm fun st hm1 hpc ↦ ?_
  have hm1' : Match (Bus.env0 m0 128) (Bus.after b0 entryS) st.data := by
    rw [Bus.after_eq run_b0]; exact hm1
  obtain ⟨hsp0, hsl0, hmem0, hk0, h0, h19, h20, h21, h22⟩ := ok_b0
  have hfr0 : Fr m0 128 tablePhaseStack slots keep (outs m0) st.data :=
    Fr.ofPrologue hN N_ge hm1' hwf hsp0 hsl0 slots_le hmem0 hk0
  have hts1 : TStateAt st.data.dmem m0.regs.X0.toBitVec a s :=
    tstate_keep c (fun q hq ↦ Bus.frame_inRange hN N_ge (Bus.Written.inRange rfl
      (base_noWrap (le_trans N_ge hN)) hmem0 hq)) hts0 (hm1'.kept hwf) (hm1'.sameOutside hwf)
  have hle0 : 128 + bitLengthStack ≤ tablePhaseStack := N_ge
  have hpc' : st.pc = Labels.label NativeRustcVmArm.Vm.BitLength.entryLabel ∧ retOf st.data = Host.addrOf (k + NativeRustcVmArm.Vm.TablePhase.b1Offset) := hpc
  refine Fr.leaf hfr0 hN hle0 keep_callee slots_le hof hbl
    (fun m m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun _ h ↦ .inl h, hq.2.2⟩) hpc' trivial
    fun m2 hfr2 hq2 hcs2 ↦ ?_
  have hx2 : m2.regs.X0.toNat = 2 := by
    rw [hq2.1, show st.data.regs.X0.toNat = 3 by
      show (st.data.regs.getXReg .X0).toBitVec.toNat = 3
      rw [Bus.Gkr.reg_lit hm1' h0]; rfl, bitLength_three]
  -- `b1`: `grind(0)`.
  have hle_g : 128 + grindStack ≤ tablePhaseStack := by unfold tablePhaseStack; omega
  refine Bus.Gkr.Fr.runBlock hS N_ge rfl hfr2 (b1_in_code.trans hp.1 (by simp [b1])) run_b1 rfl rfl
    (by decide) (by decide) fun st3 hfr3 hd3 hm3 hpc3 ↦ ?_
  have hm3' : Match (Env.ofMachine m2 [(base m0 128, 128)]) (Bus.after b1 sF) st3.data := by
    rw [Bus.after_eq run_b1]; exact hm3
  obtain ⟨-, -, hk1, g0, g1⟩ := ok_b1
  have tr2 : ∀ r, calleeSaved r = true → r ∈ mids → st3.data.regs.getXReg r =
      st.data.regs.getXReg r := fun r hc hr ↦ by
    rw [Bus.Gkr.reg_of hm3' (reg_keep hk1 hr), hcs2 r hc]
  have e30 : st3.data.regs.X0 = m0.regs.X0 := by
    rw [show st3.data.regs.X0 = st3.data.regs.getXReg .X0 from rfl, Bus.Gkr.reg_of hm3' g0,
      hcs2 .X21 rfl, Bus.Gkr.reg_of hm1' h21]
    rfl
  have e31 : grindBits st3.data = 0 := by
    unfold grindBits
    show (st3.data.regs.getXReg .X1).toBitVec.toNat % 2 ^ 32 = 0
    rw [hm3'.regs .X1 _ g1]
    simp only [Sym.eval, SBool.eval, Env.ofMachine_regs]
    have : (m2.regs.getXReg .X0).toBitVec = BitVec.ofNat 64 2 := by
      apply BitVec.eq_of_toNat_eq; exact hx2
    have hlt : CmpOp.ult.apply .W32 (m2.regs.getXReg .X0).toBitVec (BitVec.ofNat 64 3) = true := by
      rw [this]; decide
    simp only [hlt, ↓reduceIte]; rfl
  have hat3 := Bus.Gkr.Fr.at_ c hfr3 hor
  have hts3 : TStateAt st3.data.dmem m0.regs.X0.toBitVec a s := by
    rw [hd3]
    exact tstate_keep c (fun q hq ↦ by unfold bitLengthStack at hq; exact
      (Bus.not_inRange_zero _ _ hq).elim) hts1 hq2.2.2.2.2 hq2.2.1
  have hpc3' : st3.pc = Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel ∧ retOf st3.data = Host.addrOf (k + NativeRustcVmArm.Vm.TablePhase.b2Offset) := hpc3
  refine Bus.Gkr.Fr.callSpec hfr3 hN hle_g keep_callee slots_le hof (hgrind a s) hpc3'
    ⟨hfr3.stackOk hS rfl hle_g, c.rcAt hat3 hle_g, by rw [e30]; exact hts3,
      by rw [e30]; exact c.tstateOk hat3 hle_g, by rw [e31]; decide⟩
    (fun m' hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.2.1 fun q h ↦ h.elim
      (fun h ↦ .inr (.inl (by rw [e30] at h; exact h))) .inl, hq.2.2.2⟩)
    fun m4 hfr4 hq4 hcs4 ↦ ?_
  have hgr : (grind (grindBits st3.data)).run s = (grind (grindingBits 4)).run s := by
    rw [e31, grindingBits_four]
  obtain ⟨q0, q1, -, -⟩ := hq4
  rw [hgr] at q0
  rw [hgr, e30] at q1
  -- `b2`: the grind's result.
  refine Bus.Gkr.Fr.runBlock hS N_ge rfl hfr4 (b2_in_code.trans hp.1 (by simp [b2])) run_b2 rfl rfl
    (by decide) (by decide) fun st5 hfr5 hd5 hm5 hpc5 ↦ ?_
  have hm5' : Match (Env.ofMachine m4 [(base m0 128, 128)]) (Bus.after b2 sF) st5.data := by
    rw [Bus.after_eq run_b2]; exact hm5
  obtain ⟨-, -, hk2, f0⟩ := ok_b2
  have hc : SBool.eval (Env.ofMachine m4 [(base m0 128, 128)])
      (.cmp .eq .W32 (.un .trunc .W32 (.reg .X0)) (.lit 0)) =
      !((grind (grindingBits 4)).run s).isSome := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
    rw [show m4.regs.getXReg .X0 = m4.regs.X0 from rfl, q0]
    cases ((grind (grindingBits 4)).run s).isSome <;> decide
  simp only [PcOk, hc] at hpc5
  -- The registers so far.
  have tr : ∀ r, calleeSaved r = true → r ∈ mids → st5.data.regs.getXReg r =
      st.data.regs.getXReg r := fun r hc hr ↦ by
    rw [Bus.Gkr.reg_of hm5' (reg_keep hk2 hr), hcs4 r hc, tr2 r hc hr]
  cases hr : (grind (grindingBits 4)).run s with
  | none =>
    -- A failed grind: the exit with `0`.
    simp only [hr, Option.isSome_none, Bool.not_false, ↓reduceIte] at hpc5
    have hrun : (tablePhase L bus).run s = none := by rw [tablePhase_run, hr]; rfl
    refine Bus.Gkr.at_pc (hpc5.trans (hp.label (j := NativeRustcVmArm.Vm.TablePhase.b7Offset) NativeRustcVmArm.Vm.TablePhase.label_2_at)) (exit7 hp hS hfr5
      fun m' _ hx0' ↦ ⟨?_, fun x s' h ↦ (by rw [hrun] at h; cases h),
        fun x s' h ↦ (by rw [hrun] at h; cases h)⟩)
    rw [hx0', hrun]
    exact UInt64.toBitVec_inj.mp (Bus.Gkr.reg_lit hm5' f0)
  | some p =>
    obtain ⟨⟨⟩, s1⟩ := p
    simp only [hr, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc5
    have hts4 := q1 () s1 hr
    -- `b3`: `squeeze`.
    refine Bus.Gkr.at_pc hpc5 (Bus.Gkr.Fr.runBlock hS N_ge rfl hfr5
      (b3_in_code.trans hp.1 (by simp [b3])) run_b3 rfl rfl (by decide) (by decide)
      fun st6 hfr6 hd6 hm6 hpc6 ↦ ?_)
    have hm6' : Match (Env.ofMachine st5.data [(base m0 128, 128)]) (Bus.after b3 sF) st6.data := by
      rw [Bus.after_eq run_b3]; exact hm6
    obtain ⟨-, -, hk3, d0⟩ := ok_b3
    have tr6 : ∀ r, calleeSaved r = true → r ∈ mids → st6.data.regs.getXReg r =
        st.data.regs.getXReg r := fun r hc hr ↦ by
      rw [Bus.Gkr.reg_of hm6' (reg_keep hk3 hr), tr r hc hr]
    have e60 : st6.data.regs.X0.toBitVec = m0.regs.X0.toBitVec := by
      show (st6.data.regs.getXReg .X0).toBitVec = _
      rw [Bus.Gkr.reg_of hm6' d0, tr .X21 rfl (by simp), Bus.Gkr.reg_of hm1' h21]
      rfl
    have hle_q : 128 + squeezeStack ≤ tablePhaseStack := by unfold tablePhaseStack; omega
    have hpc6' : st6.pc = Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel ∧ retOf st6.data = Host.addrOf (k + NativeRustcVmArm.Vm.TablePhase.b4Offset) :=
      hpc6
    refine squeeze_call c hsq hfr6 hor hle_q keep_callee slots_le hof (fun _ h ↦ .inl h) hpc6'
      e60 (by rw [hd6, hd5]; exact hts4) fun m7 hfr7 hts7 hc0 hc1 hcs7 _ ↦ ?_
    have tr7 : ∀ r, calleeSaved r = true → r ∈ mids → m7.regs.getXReg r =
        st.data.regs.getXReg r := fun r hc hr ↦ by rw [hcs7 r hc, tr6 r hc hr]
    exact tail hp hpow hdot hsum hpre hr hfr7
      (by rw [tr7 .X19 rfl (by simp), Bus.Gkr.reg_of hm1' h19]; rfl)
      (by rw [tr7 .X20 rfl (by simp), Bus.Gkr.reg_of hm1' h20]; rfl)
      (by rw [tr7 .X21 rfl (by simp), Bus.Gkr.reg_of hm1' h21]; rfl)
      (by rw [tr7 .X22 rfl (by simp), Bus.Gkr.reg_of hm1' h22]; rfl) hc0 hc1 hts7

end

end NativeRustcVmArm.Tables.TablePhase
