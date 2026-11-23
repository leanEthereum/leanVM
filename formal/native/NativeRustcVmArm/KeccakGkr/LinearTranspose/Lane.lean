module

public import NativeRustcVmArm.Code.Vm.KeccakPi.Names
public import NativeRustcVmArm.KeccakGkr.LinearTranspose.Copy2
public import NativeRustcVmArm.Spec.KeccakGkr

/-!
# `linear_transpose`: the lanes of `g`

The lane loop `.LLinearTranspose_2`: for lane `l` (`Head`), `π l` by `keccak_pi` (`b2`), `ρ_l`
loaded and the source lane's address (`b3`), the lane copied (`b4` and the copy loop, or for
`l = 0` `b7` and the unrolled one), back to `.LLinearTranspose_1` (`b6`, `b9`), which steps to
the next lane or out (`b1`, `lane_loop`).
-/

namespace NativeRustcVmArm.KeccakGkr.LinearTranspose

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVmArm.Arrays NativeRustcVmArm.Sumcheck
open NativeRustcVmArm.Vm.LinearTranspose LeanVM.Parameters
open NativeRustcVm (Region)
open NativeRustcVm.KeccakGkr (gW colW outW weightsBytes)

@[expose] public section

/-- **The lane loop's head** at lane `l`. -/
structure Head [Labels] (m0 : MachineData) (ws : Array EW) (l : Nat) (st : MachineData) : Prop where
  regs : LaneRegs m0 st l
  g : ElemsAt st.dmem (gA m0) (gF ws) (64 * l)

/-- **`g` done**, at `.LLinearTranspose_7`. -/
structure GDone [Labels] (m0 : MachineData) (ws : Array EW) (st : MachineData) : Prop where
  ctx : Ctx m0 st
  g : ElemsAt st.dmem (gA m0) (gF ws) 1600

end

public section

variable [NativeRustcArm.Host] {ws : Array EW} {m0 : MachineData} {k : Nat}

/-- **The copy loop** of a lane. -/
theorem copy_loop (hp : Placed code k) (hpre : LinearTransposePre ws m0) {l z : Nat}
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b5Offset)) (hI : Copy m0 ws l z s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b6Offset) ∧ AfterLane m0 ws l s'.data)
      s :=
  Sym.loop (fun n s ↦ ∃ z, n = 64 - z ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b5Offset) ∧ Copy m0 ws l z s.data)
    (fun _ s ⟨z, hn, hpc, hI⟩ ↦ (copy_step hp hpre hpc hI).mono fun s' h ↦ by
      rcases h with ⟨hpc', hI'⟩ | h
      · exact Or.inr ⟨64 - (z + 1), by have := hI.z_lt; omega, z + 1, rfl, hpc', hI'⟩
      · exact Or.inl h)
    ⟨z, rfl, hpc, hI⟩

/-- **Lane `0`'s copy loop**. -/
theorem copy2_loop (hp : Placed code k) (hpre : LinearTransposePre ws m0) {z : Nat}
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b8Offset)) (hI : Copy2 m0 ws z s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b9Offset) ∧ AfterLane m0 ws 0 s'.data)
      s :=
  Sym.loop (fun n s ↦ ∃ z, n = 64 - z ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b8Offset) ∧ Copy2 m0 ws z s.data)
    (fun _ s ⟨z, hn, hpc, hI⟩ ↦ (copy2_step hp hpre hpc hI).mono fun s' h ↦ by
      rcases h with ⟨hpc', hI'⟩ | h
      · exact Or.inr ⟨64 - (z + 2), by have := hI.z_lt; omega, z + 2, rfl, hpc', hI'⟩
      · exact Or.inl h)
    ⟨z, rfl, hpc, hI⟩

theorem body_regs {s s' : MachineData} {l : Nat} (hI : LaneRegs m0 s l) (hb : Body m0 s')
    {env : Env} {S S' : SState} (hm : Match env S s) (hm' : Match env S' s')
    (h : [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26].all
      (fun r ↦ (S.reg r).isSome && S'.reg r == S.reg r) = true) : LaneRegs m0 s' l :=
  hI.keep hb (KeccakGkr.Match.regs_keep hm hm' _ h)

/-- **A lane**: from the head of lane `l`, the lane's 64 elements of `g`, at
`.LLinearTranspose_1`. -/
theorem lane_step (hp : Placed code k) (hpre : LinearTransposePre ws m0)
    (hpi : Spec (Labels.label NativeRustcVmArm.Vm.KeccakPi.entryLabel) KeccakPiPre KeccakPiPost) {l : Nat}
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b2Offset)) (hI : Head m0 ws l s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b1Offset) ∧ AfterLane m0 ws l s'.data)
      s := by
  have hS := hpre.1
  have hA := pre_areas hpre
  have hl := hI.regs.lt
  -- `b2`: `π l`
  refine exec_at (b2_in_code.trans hp.1 (by simp [b2])) e2 (Env.wf_nil _) hpc (match_nil _)
    fun s1 hm1 hpc1 ↦ ?_
  have hb1 : Body m0 s1.data :=
    hI.regs.ctx.body.of_block (match_nil _) hm1 (Env.wf_nil _) rfl free_ok (by decide)
  have hr1 := body_regs hI.regs hb1 (match_nil _) hm1 (by decide)
  have hx0 : s1.data.regs.X0.toNat = l := by
    have h := hm1.regs .X0 _ rfl
    show (s1.data.regs.getXReg .X0).toBitVec.toNat = l
    rw [h]
    exact hI.regs.x23
  refine call_then hpc1 hpi (show s1.data.regs.X0.toNat < 25 by omega) fun s2 hpc2 hpost ↦ ?_
  obtain ⟨hpi0, hdm2, hsv2⟩ := hpost
  have hb2 : Body m0 s2.data :=
    hb1.call hS (n := 0) (by decide) slots_le (wsOff hpre) (R := fun _ ↦ False)
      (fun p hp ↦ by rw [hdm2]) (fun _ h ↦ h.elim) hsv2
  have hr2 : LaneRegs m0 s2.data l :=
    hr1.keep hb2 fun r hr ↦ hsv2.1 r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  have hg2 : ElemsAt s2.data.dmem (gA m0) (gF ws) (64 * l) := by
    rw [hdm2, (hm1.dmem_eq (Env.wf_nil _) rfl)]; exact hI.g
  -- `b3`: `ρ_l`, the source lane
  have hrok := Areas.ok hA (r := rhoRegion) (Or.inr (by simp [rsR]))
  have hrho := rho_at hpre hb2
  let env := Env.ofMachine s2.data [(rhoAddr, 100)]
  have hwf : env.WF := wf_one (by
      have := hrho.mapped; rwa [rhoBytes_length] at this) hrok.2
  have hm : Match env rhoS s2.data :=
    match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
      ⟨by
        show (s2.data.regs.getXReg .X26).toBitVec = rhoAddr + BitVec.ofInt 64 0
        rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
        exact hr2.x26, trivial⟩ trivial
      ⟨by have := hr2.x23; show s2.data.regs.X23.toNat < 25; omega, trivial⟩ trivial
  refine exec_at (b3_in_code.trans hp.1 (by simp [b3])) e3 hwf hpc2 hm fun s3 hm3 hpc3 ↦ ?_
  have hb3 : Body m0 s3.data := hb2.of_block hm hm3 hwf rfl free_ok (by decide)
  have hr3 := body_regs hr2 hb3 hm hm3 (by decide)
  have hg3 : ElemsAt s3.data.dmem (gA m0) (gF ws) (64 * l) := by
    rw [hm3.dmem_eq hwf rfl]; exact hg2
  have hx8 : s3.data.regs.X8.toNat = keccakRhoW.getD l 0 := by
    have h := hm3.regs .X8 _ rfl
    show (s3.data.regs.getXReg .X8).toBitVec.toNat = _
    rw [h]
    show (env.load 0 (0 + (BitVec.ofInt 64 ((env.regs .X23).apply_mem_extend ⟨.UXTX, .E2⟩)).toNat) 4).toNat = _
    rw [memExtend2_toNat, show (env.regs .X23).toNat = l from hr2.x23, Nat.zero_add,
      Nat.mod_eq_of_lt (by omega), Nat.mul_comm, load_rho rfl hrho hl, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := rho_lt hl; omega)]
  have hx9 : s3.data.regs.X9.toBitVec = wA m0 + BitVec.ofNat 64 (1024 * keccakPi l) := by
    have h := hm3.regs .X9 _ rfl
    show (s3.data.regs.getXReg .X9).toBitVec = _
    rw [h]
    sym_simp
    rw [show env.regs .X22 = wA m0 from congrArg UInt64.toBitVec hr2.ctx.x22]
    have hX0 : (env.regs .X0).toNat = keccakPi l := by
      show s2.data.regs.X0.toNat = _; rw [hpi0, hx0]
    congr 1
    apply BitVec.eq_of_toNat_eq
    have := pi_lt hl
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, hX0, Nat.shiftLeft_eq]
    rw [Nat.mul_comm]
  simp only [PcOk] at hpc3
  sym_simp at hpc3
  by_cases h0 : l = 0
  · -- lane `0`: `b7`, the unrolled loop, `b9`
    subst h0
    have hc : (env.regs .X23 == 0#64) = true := by
      rw [beq_iff_eq]; apply BitVec.eq_of_toNat_eq; exact hr2.x23
    simp only [hc, ite_true] at hpc3
    refine exec_at (b7_in_code.trans hp.1 (by simp [b7])) e7 (Env.wf_nil _)
      (hpc3.trans (hp.label (j := NativeRustcVmArm.Vm.LinearTranspose.b7Offset) NativeRustcVmArm.Vm.LinearTranspose.label_5_at)) (match_nil _) fun s4 hm4 hpc4 ↦ ?_
    have hb4 : Body m0 s4.data := hb3.of_block (match_nil _) hm4 (Env.wf_nil _) rfl free_ok (by decide)
    have hr4 := body_regs hr3 hb4 (match_nil _) hm4 (by decide)
    have e89 := KeccakGkr.Match.regs_keep (match_nil _) hm4 [.X8, .X9] (by decide)
    refine (copy2_loop hp hpre (z := 0) hpc4 ⟨hr4, by decide, rfl, ?_, ?_, ?_, ?_, ?_⟩).bind
      fun s5 ⟨hpc5, hI5⟩ ↦ ?_
    · show (s4.data.regs.getXReg .X8).toBitVec.toNat = _
      rw [e89 .X8 (by simp)]; exact hx8
    · show (s4.data.regs.getXReg .X9).toBitVec = _
      rw [e89 .X9 (by simp)]; exact hx9
    · have h := hm4.regs .X10 _ rfl
      show (s4.data.regs.getXReg .X10).toBitVec = _
      rw [h]; exact hr3.x25
    · have h := hm4.regs .X11 _ rfl
      show (s4.data.regs.getXReg .X11).toBitVec.toNat = _
      rw [h]; rfl
    · rw [hm4.dmem_eq (Env.wf_nil _) rfl]; exact hg3
    refine exec_at (b9_in_code.trans hp.1 (by simp [b9])) e9 (Env.wf_nil _) hpc5 (match_nil _)
      fun s6 hm6 hpc6 ↦ .done _ ⟨hpc6.trans (hp.label (j := NativeRustcVmArm.Vm.LinearTranspose.b1Offset) NativeRustcVmArm.Vm.LinearTranspose.label_1_at), ?_⟩
    have hb6 : Body m0 s6.data := hI5.regs.ctx.body.of_block (match_nil _) hm6 (Env.wf_nil _) rfl free_ok
      (by decide)
    exact ⟨body_regs hI5.regs hb6 (match_nil _) hm6 (by decide), by
      rw [hm6.dmem_eq (Env.wf_nil _) rfl]; exact hI5.g⟩
  · have hc : (env.regs .X23 == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have := congrArg BitVec.toNat h
      rw [show (env.regs .X23).toNat = l from hr2.x23] at this; simp at this; omega
    simp only [hc, Bool.false_eq_true, ite_false, NativeRustcVmArm.Vm.LinearTranspose.b3_length, NativeRustcVmArm.Vm.LinearTranspose.b3Length] at hpc3
    refine exec_at (b4_in_code.trans hp.1 (by simp [b4])) e4 (Env.wf_nil _) hpc3 (match_nil _)
      fun s4 hm4 hpc4 ↦ ?_
    have hb4 : Body m0 s4.data := hb3.of_block (match_nil _) hm4 (Env.wf_nil _) rfl free_ok (by decide)
    have hr4 := body_regs hr3 hb4 (match_nil _) hm4 (by decide)
    have e89 := KeccakGkr.Match.regs_keep (match_nil _) hm4 [.X8, .X9] (by decide)
    refine (copy_loop hp hpre (z := 0) hpc4 ⟨hr4, by decide, ?_, ?_, ?_, ?_, ?_⟩).bind
      fun s5 ⟨hpc5, hI5⟩ ↦ ?_
    · show (s4.data.regs.getXReg .X8).toBitVec.toNat = _
      rw [e89 .X8 (by simp)]; exact hx8
    · show (s4.data.regs.getXReg .X9).toBitVec = _
      rw [e89 .X9 (by simp)]; exact hx9
    · have h := hm4.regs .X10 _ rfl
      show (s4.data.regs.getXReg .X10).toBitVec.toNat = _
      rw [h]; rfl
    · have h := hm4.regs .X11 _ rfl
      show (s4.data.regs.getXReg .X11).toBitVec = _
      rw [h]
      rw [show 8 + 1024 * l + 16 * 0 = 8 + 1024 * l by omega]
      exact hr3.x24
    · rw [hm4.dmem_eq (Env.wf_nil _) rfl]; exact hg3
    refine exec_at (b6_in_code.trans hp.1 (by simp [b6])) e6 (Env.wf_nil _) hpc5 (match_nil _)
      fun s6 hm6 hpc6 ↦ .done _ ⟨hpc6.trans (hp.label (j := NativeRustcVmArm.Vm.LinearTranspose.b1Offset) NativeRustcVmArm.Vm.LinearTranspose.label_1_at), ?_⟩
    have hb6 : Body m0 s6.data := hI5.regs.ctx.body.of_block (match_nil _) hm6 (Env.wf_nil _) rfl free_ok
      (by decide)
    exact ⟨body_regs hI5.regs hb6 (match_nil _) hm6 (by decide), by
      rw [hm6.dmem_eq (Env.wf_nil _) rfl]; exact hI5.g⟩

end

end NativeRustcVmArm.KeccakGkr.LinearTranspose
