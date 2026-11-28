module

public import NativeRustcVmX64.KeccakGkr.LinearTranspose.OutStep
public import NativeRustcVmX64.Code.Vm.KeccakPi.Names
public import NativeRustcVmX64.Code.Vm.LinearTranspose.Names

/-!
# `linear_transpose` on x86-64

**`linearTranspose_spec`**: the prologue (`entry`), `g` lane by lane (`lanes_loop`), the columns
(`columns`), the output (`out_start`, then per lane `lane_cols`, the element loop `out_step`,
`b18`), the epilogue (`b19`).
-/

namespace NativeRustcVmX64.KeccakGkr.LinearTranspose

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.LinearTranspose LeanVM.Parameters
open NativeRustcVm.Transcript (off off_zero off_off Mapped.keeps)

public section

variable {ws : Array EW} {m0 : MachineData} [Host] {k : Nat}

/-- **A lane's output**. -/
theorem out_loop (hp : Placed code k) (h : PreOk m0 ws) {l : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b17Offset)) (hI : OutHead m0 ws l 0 st.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b18Offset) ∧
      OutLane m0 ws l s'.data ∧ ElemsAt s'.data.dmem (oA m0) (oF ws) (64 * l + 64)) st :=
  loop (fun n st ↦ ∃ z, n = 64 - z ∧ z < 64 ∧ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b17Offset) ∧
      OutHead m0 ws l z st.data)
    (fun _ st ⟨z, hn, hz, hpc, hI⟩ ↦ (out_step hp h hpc hI).mono fun s' h' ↦ by
      rcases h' with ⟨hlt, hpc', hI'⟩ | ⟨-, hpc', hE⟩
      · exact Or.inr ⟨64 - (z + 1), by omega, z + 1, rfl, hlt, hpc', hI'⟩
      · exact Or.inl ⟨hpc', hE⟩)
    ⟨0, rfl, by decide, hpc, hI⟩

/-- `b18`: the next lane, or the output complete. -/
theorem out_lane_end (hp : Placed code k) (h : PreOk m0 ws) {l : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b18Offset)) (hI : OutLane m0 ws l st.data)
    (ho : ElemsAt st.data.dmem (oA m0) (oF ws) (64 * l + 64)) :
    Eventually (step1 Host.exe) (fun s' ↦ (l + 1 < 25 ∧ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b16Offset) ∧
      OutLane m0 ws (l + 1) s'.data) ∨ (s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b19Offset) ∧ OCtx m0 s'.data ∧
      ElemsAt s'.data.dmem (oA m0) (oF ws) 1600)) st := by
  have hl := hI.regs.l_lt
  refine exec_at (infix_of b18_in_code (by simp [b18]) hp) exit_b18 (Env.wf_nil _) nofun hpc
    (match_nil _) fun st' hm' hpc' ↦ ?_
  obtain ⟨hreg, hat, hrcx, hrbx, hr15⟩ := ok_b18
  have hd : st'.data.dmem = st.data.dmem := hm'.dmem_eq (Env.wf_nil _) (regOk_mem hreg)
  have hc := hI.regs.ctx.of_regs h hm' hreg (atoms_eq hm' hat (by simp))
  simp only [PcOk, SBool.eval, CmpOp.apply, Sym.eval, BinOp.apply, low_W64, ext_W64,
    Env.ofMachine_regs] at hpc'
  rw [show st.data.regs.get64 .rcx = _ from hI.regs.rcx, add_ofNat', beq_ofNat (by omega) (by omega)]
    at hpc'
  by_cases hlast : l + 1 = 25
  · rw [decide_eq_true hlast] at hpc'
    simp only [Bool.not_true, Bool.false_eq_true, ite_false] at hpc'
    refine .done _ (Or.inr ⟨hpc'.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.LinearTranspose.b18_next), hc,
      ?_⟩)
    rw [hd, show 1600 = 64 * l + 64 by omega]; exact ho
  · rw [decide_eq_false hlast] at hpc'
    simp only [Bool.not_false, ite_true] at hpc'
    refine .done _ (Or.inl ⟨by omega, hpc'.trans (label_of_infix hp b16_in_code rfl),
      ⟨⟨hc, by omega, ?_, (atoms_eq hm' hat (by simp)).trans hI.regs.r8,
        (atoms_eq hm' hat (by simp)).trans hI.regs.r9, (atoms_eq hm' hat (by simp)).trans hI.regs.rdi,
        (atoms_eq hm' hat (by simp)).trans hI.regs.rsi, ?_, ?_⟩, hd ▸ hI.g, hd ▸ hI.c,
        by rw [hd, show 64 * (l + 1) = 64 * l + 64 by omega]; exact ho⟩⟩)
    · rw [show reg st'.data .rcx = _ from hm'.regs .rcx _ hrcx]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rw [show st.data.regs.get64 .rcx = _ from hI.regs.rcx, add_ofNat']
    · rw [show reg st'.data .rbx = _ from hm'.regs .rbx _ hrbx]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rw [show st.data.regs.get64 .rbx = _ from hI.regs.rbx, BitVec.add_comm,
        NativeRustcVm.Transcript.off_add, show 8 + 1024 * l + 1024 = 8 + 1024 * (l + 1) by omega]
    · rw [show reg st'.data .r15 = _ from hm'.regs .r15 _ hr15]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
      rw [show st.data.regs.get64 .r15 = _ from hI.regs.r15, BitVec.add_comm,
        NativeRustcVm.Transcript.off_add, show 8 + 1024 * l + 1024 = 8 + 1024 * (l + 1) by omega]

/-- **The output**: from the columns complete to the epilogue. -/
theorem output (hp : Placed code k) (h : PreOk m0 ws) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b15Offset)) (hI : CDone m0 ws st.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b19Offset) ∧ OCtx m0 s'.data ∧
      ElemsAt s'.data.dmem (oA m0) (oF ws) 1600) st :=
  (out_start hp h hpc hI).bind fun s1 ⟨hpc1, hI1⟩ ↦
    loop (fun n st ↦ ∃ l, n = 25 - l ∧ l < 25 ∧ st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.LinearTranspose.b16Offset) ∧
        OutLane m0 ws l st.data)
      (fun _ st ⟨l, hn, hl, hpc, hI⟩ ↦ (lane_cols hp h hpc hI).bind fun s2 ⟨hpc2, hI2⟩ ↦
        (out_loop hp h hpc2 hI2).bind fun s3 ⟨hpc3, hI3, ho3⟩ ↦
          (out_lane_end hp h hpc3 hI3 ho3).mono fun s' h' ↦ by
            rcases h' with ⟨hlt, hpc', hI'⟩ | h'
            · exact Or.inr ⟨25 - (l + 1), by omega, l + 1, rfl, hlt, hpc', hI'⟩
            · exact Or.inl h')
      ⟨0, rfl, by decide, hpc1, hI1⟩

/-- **`linear_transpose` meets its contract**, given `keccak_pi`'s. -/
theorem linearTranspose_spec (hp : Placed code k)
    (hpi : Spec (Labels.label NativeRustcVmX64.Vm.KeccakPi.entryLabel) KeccakPiPre KeccakPiPost) (ws : Array EW) :
    Spec (Labels.label NativeRustcVmX64.Vm.LinearTranspose.entryLabel) (LinearTransposePre ws) (LinearTransposePost ws) := by
  intro m0 hpre
  have h := preOk hpre
  unfold NativeRustcVmX64.Vm.LinearTranspose.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.LinearTranspose.entry_at]
  refine (entry hp h).bind fun s1 ⟨hpc1, hI1⟩ ↦ ?_
  refine (lanes_loop hp h hpi hpc1 hI1).bind fun s2 ⟨hpc2, hI2⟩ ↦ ?_
  refine (columns hp h hpc2 hI2).bind fun s3 ⟨hpc3, hI3⟩ ↦ ?_
  refine (output hp h hpc3 hI3).bind fun s4 ⟨hpc4, hc4, ho4⟩ ↦ ?_
  have hwf := frame_wf (m0 := m0) (d := s4.data) (F := 64) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨Mapped.keeps (frame_mapped h.st (by rw [stack_eq])) hc4.frame.kept, frame_nw h⟩
    (by simp) (List.pairwise_singleton _ _)
  refine exec_at (infix_of b19_in_code (by simp [b19]) hp) exit_b19 hwf nofun hpc4
    (match_ofMachine ⟨rfl, trivial⟩ ⟨hc4.frame.rsp_eval, trivial⟩ trivial trivial trivial)
    fun s' hm' hpc' ↦ .done _ ?_
  obtain ⟨hepi, hmem⟩ := ok_b19
  obtain ⟨hsv, hrsp⟩ := Frame.epilogue hc4.frame hwf hm' hepi
  have hd : s'.data.dmem = s4.data.dmem := hm'.dmem_eq hwf hmem
  simp only [PcOk] at hpc'
  refine ⟨by rw [hpc']; exact hc4.frame.load_ret h.st (by rw [stack_eq]), hrsp, ?_, ?_, hsv⟩
  · rw [hd]; exact out_list ho4
  · intro q hq
    rw [hd]
    refine hc4.same q fun hO ↦ hq ?_
    rcases hO with hO | hO | hO | hO
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, hO⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), hO⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self)), hO⟩
    · exact ⟨_, List.mem_cons_self, hO⟩

end

end NativeRustcVmX64.KeccakGkr.LinearTranspose
