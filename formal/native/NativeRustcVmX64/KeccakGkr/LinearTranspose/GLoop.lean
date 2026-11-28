module

public import NativeRustcVmX64.KeccakGkr.LinearTranspose.Copy
public import NativeRustcVmX64.Code.Vm.KeccakPi.Names

/-!
# `linear_transpose`: the lane loop (x86-64)

`b4` steps the lane (`lane_end`); the copy loop and the lane loop run to `g` complete
(`lanes_loop`). A block without memory accesses keeps the context (`Ctx.of_regs`).
-/

namespace NativeRustcVmX64.KeccakGkr.LinearTranspose

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.LinearTranspose LeanVM.Parameters
open NativeRustcVm.Transcript (off off_zero off_off toNat_off)

public section

variable {ws : Array EW} {m0 : MachineData}

/-- **A block without memory accesses** keeps the context but the registers it sets. -/
theorem Ctx.of_regs [Labels] {d d' : MachineData} (hc : Ctx m0 d) (h : PreOk m0 ws) {S : SState}
    (hm : Match (Env.ofMachine d [] (fun _ ↦ 0) 0) S d') (hS : regOk S = true)
    (h12 : reg d' .r12 = reg d .r12) (h14 : reg d' .r14 = reg d .r14) : Ctx m0 d' := by
  have hd : d'.dmem = d.dmem := hm.dmem_eq (Env.wf_nil _) (regOk_mem hS)
  refine ⟨Frame.keep hc.frame (by rw [hd]; exact fun _ h ↦ h) (hm.regs .rsp _ (regOk_rsp hS))
    (R := fun _ ↦ False) (fun q _ ↦ by rw [hd]) (fun _ h ↦ h.elim) (frame_nw h), hd ▸ hc.same,
    h12.trans hc.r12, h14.trans hc.r14⟩

variable [Host] {k : Nat}

/-- `b4`: the next lane, or `g` complete. -/
theorem lane_end (hp : Placed code k) (h : PreOk m0 ws) {l : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b4Offset)) (hI : LaneEnd m0 ws l st.data) :
    Eventually (step1 Host.exe) (fun s' ↦ (l + 1 < 25 ∧ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b1Offset) ∧
      Head m0 ws (l + 1) s'.data) ∨ (s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b5Offset) ∧ GDone m0 ws s'.data)) st := by
  have hl := hI.l_lt
  refine exec_at (infix_of b4_in_code (by simp [b4]) hp) exit_b4 (Env.wf_nil _) nofun hpc
    (match_nil _) fun st' hm' hpc' ↦ ?_
  obtain ⟨hreg, hat, hr13, hrbp⟩ := ok_b4
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq (Env.wf_nil _) (regOk_mem hreg)
  have hc := hI.ctx.of_regs h hm' hreg (atoms_eq hm' hat (by simp)) (atoms_eq hm' hat (by simp))
  simp only [PcOk, SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_W64, ext_W64,
    Env.ofMachine_regs] at hpc'
  rw [show st.data.regs.get64 .r13 = _ from hI.r13, add_ofNat', beq_ofNat (by omega) (by omega)]
    at hpc'
  by_cases hlast : l + 1 = 25
  · rw [decide_eq_true hlast] at hpc'
    simp only [Bool.not_true, Bool.false_eq_true, ite_false] at hpc'
    refine .done _ (Or.inr ⟨hpc'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.LinearTranspose.b4_next), hc,
      (atoms_eq hm' hat (by simp)).trans hI.r15, (atoms_eq hm' hat (by simp)).trans hI.rbx, ?_⟩)
    rw [hd, show 1600 = 64 * l + 64 by omega]; exact hI.g
  · rw [decide_eq_false hlast] at hpc'
    simp only [Bool.not_false, ite_true] at hpc'
    refine .done _ (Or.inl ⟨by omega, hpc'.trans (label_of_infix hp b1_in_code rfl), hc, by omega,
      ?_, ?_, (atoms_eq hm' hat (by simp)).trans hI.r15, (atoms_eq hm' hat (by simp)).trans hI.rbx,
      by rw [hd, show 64 * (l + 1) = 64 * l + 64 by omega]; exact hI.g⟩)
    · rw [show reg st'.data .r13 = _ from hm'.regs .r13 _ hr13]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rw [show st.data.regs.get64 .r13 = _ from hI.r13, add_ofNat']
    · rw [show reg st'.data .rbp = _ from hm'.regs .rbp _ hrbp]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rw [show st.data.regs.get64 .rbp = _ from hI.rbp, BitVec.add_comm,
        NativeRustcVm.Transcript.off_add, show 24 + 1024 * l + 1024 = 24 + 1024 * (l + 1) by omega]

/-- **A lane's copy loop**. -/
theorem copy_loop (hp : Placed code k) (h : PreOk m0 ws) {l : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b3Offset)) (hI : CopyHead m0 ws l 0 st.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b4Offset) ∧ LaneEnd m0 ws l s'.data)
      st :=
  loop (fun n st ↦ ∃ t, n = 32 - t ∧ t < 32 ∧ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b3Offset) ∧
      CopyHead m0 ws l t st.data)
    (fun _ st ⟨t, hn, ht, hpc, hI⟩ ↦ (copy_step hp h hpc hI).mono fun s' h' ↦ by
      rcases h' with ⟨hlt, hpc', hI'⟩ | ⟨-, hpc', hE⟩
      · exact Or.inr ⟨32 - (t + 1), by omega, t + 1, rfl, hlt, hpc', hI'⟩
      · exact Or.inl ⟨hpc', hE⟩)
    ⟨0, rfl, by decide, hpc, hI⟩

/-- **The lane loop**: from lane `0`'s head, `g` complete. -/
theorem lanes_loop (hp : Placed code k) (h : PreOk m0 ws)
    (hpi : Spec (Labels.label NativeRustcVmX64.Vm.KeccakPi.entryLabel) KeccakPiPre KeccakPiPost) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b1Offset)) (hI : Head m0 ws 0 st.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b5Offset) ∧ GDone m0 ws s'.data) st :=
  loop (fun n st ↦ ∃ l, n = 25 - l ∧ l < 25 ∧ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b1Offset) ∧ Head m0 ws l st.data)
    (fun _ st ⟨l, hn, hl, hpc, hI⟩ ↦ (lane_head hp h hpi hpc hI).bind fun s1 ⟨hpc1, hI1⟩ ↦
      (copy_loop hp h hpc1 hI1).bind fun s2 ⟨hpc2, hI2⟩ ↦
        (lane_end hp h hpc2 hI2).mono fun s' h' ↦ by
          rcases h' with ⟨hlt, hpc', hI'⟩ | h'
          · exact Or.inr ⟨25 - (l + 1), by omega, l + 1, rfl, hlt, hpc', hI'⟩
          · exact Or.inl h')
    ⟨0, rfl, by decide, hpc, hI⟩

end

end NativeRustcVmX64.KeccakGkr.LinearTranspose
