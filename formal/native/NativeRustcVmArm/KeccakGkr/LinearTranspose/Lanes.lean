module

public import NativeRustcVmArm.Code.Vm.KeccakPi.Names
public import NativeRustcVmArm.KeccakGkr.LinearTranspose.Lane

/-!
# `linear_transpose`: the lane loop

`.LLinearTranspose_1` (`b1`) steps to the next lane's head or, after lane 24, out to
`.LLinearTranspose_7` with `g` done (`lanes_loop`).
-/

namespace NativeRustcVmArm.KeccakGkr.LinearTranspose

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVmArm.Arrays NativeRustcVmArm.Sumcheck
open NativeRustcVmArm.Vm.LinearTranspose LeanVM.Parameters

public section

variable [NativeRustcArm.Host] {ws : Array EW} {m0 : MachineData} {k : Nat}

/-- **The next lane**: from `.LLinearTranspose_1` after lane `l`, lane `l + 1`'s head, or `g`
done. -/
theorem next_lane (hp : Placed code k) {l : Nat} {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b1Offset)) (hI : AfterLane m0 ws l s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ (l + 1 < 25 ∧ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b2Offset) ∧
      Head m0 ws (l + 1) s'.data) ∨ (s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b10Offset) ∧ GDone m0 ws s'.data)) s := by
  have hl := hI.regs.lt
  refine exec_at (b1_in_code.trans hp.1 (by simp [b1])) e1 (Env.wf_nil _) hpc (match_nil _)
    fun s1 hm1 hpc1 ↦ ?_
  have hb1 : Body m0 s1.data :=
    hI.regs.ctx.body.of_block (match_nil _) hm1 (Env.wf_nil _) rfl free_ok (by decide)
  have hg : ElemsAt s1.data.dmem (gA m0) (gF ws) (64 * l + 64) := by
    rw [hm1.dmem_eq (Env.wf_nil _) rfl]; exact hI.g
  have e := KeccakGkr.Match.regs_keep (match_nil _) hm1 [.X19, .X20, .X21, .X22, .X26] (by decide)
  have hctx : Ctx m0 s1.data :=
    ⟨hb1, (e .X19 (by simp)).trans hI.regs.ctx.x19, (e .X20 (by simp)).trans hI.regs.ctx.x20,
      (e .X21 (by simp)).trans hI.regs.ctx.x21, (e .X22 (by simp)).trans hI.regs.ctx.x22⟩
  have h23 := hm1.regs .X23 _ rfl
  have h24 := hm1.regs .X24 _ rfl
  have h25 := hm1.regs .X25 _ rfl
  sym_simp at h23 h24 h25
  have hx23 : (s.data.regs.getXReg .X23).toBitVec.toNat = l := hI.regs.x23
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  simp only [Env.ofMachine_regs] at h23 h24 h25 hpc1
  have hx23' : (s.data.regs.getXReg .X23).toBitVec + 1#64 = BitVec.ofNat 64 (l + 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_add_ofNat' (by rw [hx23]; omega), hx23, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [hx23'] at hpc1
  by_cases hlast : l = 24
  · subst hlast
    simp only [show (BitVec.ofNat 64 (24 + 1) == 25#64) = true from rfl, ite_true] at hpc1
    refine .done _ (Or.inr ⟨hpc1.trans (hp.label (j := NativeRustcVmArm.Vm.LinearTranspose.b10Offset) NativeRustcVmArm.Vm.LinearTranspose.label_7_at), hctx, hg⟩)
  · have hc : (BitVec.ofNat 64 (l + 1) == 25#64) = false := by
      rw [beq_eq_false_iff_ne]; intro h; have := congrArg BitVec.toNat h
      simp at this; omega
    simp only [hc, Bool.false_eq_true, ite_false, NativeRustcVmArm.Vm.LinearTranspose.b1_length, NativeRustcVmArm.Vm.LinearTranspose.b1Length] at hpc1
    refine .done _ (Or.inl ⟨by omega, hpc1, ⟨⟨hctx, by omega, ?_, ?_, ?_, ?_⟩, ?_⟩⟩)
    · show (s1.data.regs.getXReg .X23).toBitVec.toNat = _
      rw [h23, hx23', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · show (s1.data.regs.getXReg .X24).toBitVec = _
      rw [h24, show (s.data.regs.getXReg .X24).toBitVec = _ from hI.regs.x24,
        show (1024#64 : BitVec 64) = BitVec.ofNat 64 1024 from rfl, NativeRustcVm.addr_add_add,
        show 8 + 1024 * l + 1024 = 8 + 1024 * (l + 1) by omega]
    · show (s1.data.regs.getXReg .X25).toBitVec = _
      rw [h25, show (s.data.regs.getXReg .X25).toBitVec = _ from hI.regs.x25,
        show (1024#64 : BitVec 64) = BitVec.ofNat 64 1024 from rfl, NativeRustcVm.addr_add_add,
        show 16 + 1024 * l + 1024 = 16 + 1024 * (l + 1) by omega]
    · show (s1.data.regs.getXReg .X26).toBitVec = _
      rw [e .X26 (by simp)]; exact hI.regs.x26
    · rw [show 64 * (l + 1) = 64 * l + 64 by omega]; exact hg

/-- **The lane loop**: from lane `l`'s head, `g` done. -/
theorem lanes_loop (hp : Placed code k) (hpre : LinearTransposePre ws m0)
    (hpi : Spec (Labels.label NativeRustcVmArm.Vm.KeccakPi.entryLabel) KeccakPiPre KeccakPiPost) {l : Nat}
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b2Offset)) (hI : Head m0 ws l s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b10Offset) ∧ GDone m0 ws s'.data) s :=
  Sym.loop (fun n s ↦ ∃ l, n = 25 - l ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b2Offset) ∧ Head m0 ws l s.data)
    (fun _ s ⟨l, hn, hpc, hI⟩ ↦ (lane_step hp hpre hpi hpc hI).bind fun s1 ⟨hpc1, hI1⟩ ↦
      (next_lane hp hpc1 hI1).mono fun s' h ↦ by
        rcases h with ⟨hlt, hpc', hI'⟩ | h
        · exact Or.inr ⟨25 - (l + 1), by omega, l + 1, rfl, hpc', hI'⟩
        · exact Or.inl h)
    ⟨l, rfl, hpc, hI⟩

end

end NativeRustcVmArm.KeccakGkr.LinearTranspose
