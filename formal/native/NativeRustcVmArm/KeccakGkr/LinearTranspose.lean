module

public import NativeRustcVmArm.Code.Vm.KeccakPi.Names
public import NativeRustcVmArm.Code.Vm.LinearTranspose.Names
public import NativeRustcVmArm.KeccakGkr.LinearTranspose.Outs

/-!
# `linear_transpose` meets its contract

The prologue (`b0`) saves X19 to X26 and X30 in the 80-byte frame and keeps the arguments in X19
to X22; the lane loop fills `g` (`lanes_loop`), the column loops sum its columns (`columns`), the
output loop the output (`output`); the epilogue (`b24`) restores the registers
(`linearTranspose_spec`).
-/

namespace NativeRustcVmArm.KeccakGkr.LinearTranspose

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model
open NativeRustcVmArm.Arrays NativeRustcVmArm.Sumcheck
open NativeRustcVmArm.Vm.LinearTranspose LeanVM.Parameters

public section

variable [NativeRustcArm.Host] {ws : Array EW} {m0 : MachineData} {k : Nat}

/-- **The prologue** (`b0`): lane `0`'s head. -/
theorem entry (hp : Placed code k) (hpre : LinearTransposePre ws m0) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b2Offset) ∧ Head m0 ws 0 s'.data)
      ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b0Offset)⟩ := by
  have hS := hpre.1
  have h80 : 80 ≤ linearTransposeStack := by decide
  obtain ⟨hmap, hnw, -⟩ := frame_ok hS h80
  have hwf := wf_one hmap hnw (m := m0)
  have hm : Match (Env.ofMachine m0 [(m0.regs.SP.toBitVec - BitVec.ofNat 64 80, 80)]) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS h80 rfl, trivial⟩
      (by
        show _ = (m0.regs.SP.toBitVec - BitVec.ofNat 64 80) + BitVec.ofInt 64 80
        rw [show BitVec.ofInt 64 80 = BitVec.ofNat 64 80 from rfl, BitVec.sub_add_cancel])
      trivial trivial trivial trivial
  refine exec_then (b0_in_code.trans hp.1 (by simp [b0])) e0 hwf hm fun s1 hm1 hpc1 ↦
    .done _ ⟨?_, ?_⟩
  · simp only [PcOk] at hpc1
    exact hpc1.trans (hp.label (j := NativeRustcVmArm.Vm.LinearTranspose.b2Offset) NativeRustcVmArm.Vm.LinearTranspose.label_2_at)
  have hb : Body m0 s1.data := by
    refine Frame.of_entry hS h80 hm1 rfl (by decide +kernel) (fun r hr hn ↦ ?_) (by decide +kernel)
    simp only [calleeRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
      first | rfl | (exfalso; exact hn (by simp [slots]))
  have h19 := hm1.regs .X19 _ rfl
  have h20 := hm1.regs .X20 _ rfl
  have h21 := hm1.regs .X21 _ rfl
  have h22 := hm1.regs .X22 _ rfl
  have h23 := hm1.regs .X23 _ rfl
  have h24 := hm1.regs .X24 _ rfl
  have h25 := hm1.regs .X25 _ rfl
  have h26 := hm1.regs .X26 _ rfl
  sym_simp at h19 h20 h21 h22 h23 h24 h25 h26
  simp only [Env.ofMachine_regs] at h19 h20 h21 h22 h24 h25
  refine ⟨⟨⟨hb, UInt64.toBitVec_inj.mp h19, UInt64.toBitVec_inj.mp h20, UInt64.toBitVec_inj.mp h21,
    UInt64.toBitVec_inj.mp h22⟩, by decide, ?_, ?_, ?_, ?_⟩, fun _ h ↦ absurd h (by omega)⟩
  · show (s1.data.regs.getXReg .X23).toBitVec.toNat = 0
    rw [h23]; rfl
  · show (s1.data.regs.getXReg .X24).toBitVec = _
    rw [h24]; rfl
  · show (s1.data.regs.getXReg .X25).toBitVec = _
    rw [h25]; rfl
  · show (s1.data.regs.getXReg .X26).toBitVec = _
    rw [h26]; rfl

omit [NativeRustcArm.Host] in
/-- The output's elements as the model's list. -/
theorem out_list [Labels] {d : DataMem} (h : ElemsAt d (oA m0) (oF ws) 1600) :
    NativeRustcVm.EWsAt d (oA m0) (keccakLinearTranspose ws).toList := by
  apply ElemsAt.ewsAt
  rw [Array.length_toList, NativeRustcVm.KeccakGkr.linearTranspose_size']
  intro i hi
  obtain ⟨l, z, hz, rfl⟩ : ∃ l z, z < 64 ∧ i = 64 * l + z :=
    ⟨i / 64, i % 64, Nat.mod_lt _ (by decide), by omega⟩
  have e : (keccakLinearTranspose ws).toList.getD (64 * l + z) 0 = oF ws (64 * l + z) := by
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, ← Array.getD_eq_getD_getElem?,
      NativeRustcVm.KeccakGkr.linearTranspose_getD' ws (by omega) hz, oF,
      show (64 * l + z) / 64 = l by omega, show (64 * l + z) % 64 = z by omega]
  have := h _ hi
  rw [← e] at this
  exact this

/-- **The epilogue** (`b24`): the registers restored, the output returned. -/
theorem finish (hp : Placed code k) (hpre : LinearTransposePre ws m0) {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b24Offset)) (hI : OutDone m0 ws s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = retOf m0 ∧ LinearTransposePost ws m0 s'.data)
      s := by
  have hS := hpre.1
  have h80 : 80 ≤ linearTransposeStack := by decide
  obtain ⟨hmap, hnw, -⟩ := frame_ok hS h80
  have hb := hI.ctx.body
  have hwf := wf_one (m := s.data) (fun i hi ↦ hb.kept _ (hmap i hi)) hnw
  have hm : Match (Env.ofMachine s.data [(m0.regs.SP.toBitVec - BitVec.ofNat 64 80, 80)]) exitS
      s.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS h80 rfl, trivial⟩
      (by rw [hb.sp]; simp [Sym.eval]) trivial trivial trivial trivial
  refine exec_at (b24_in_code.trans hp.1 (by simp [b24])) e24 hwf hpc hm fun s' hm' hpc' ↦
    .done _ ?_
  obtain ⟨hsaved, hx30, hdm⟩ :=
    hb.saved hm' hwf (List.mem_map.mpr ⟨(0, .X30), by simp [slots], rfl⟩) (by decide +kernel) rfl
  refine ⟨?_, ?_, fun p hp' ↦ ?_, hsaved⟩
  · simp only [PcOk] at hpc'
    rw [hpc']
    simp only [retOf, hx30]
  · rw [hdm]; exact out_list hI.o
  · rw [hdm]; exact hb.same p hp'

/-- **`linear_transpose` meets its contract**, given `keccak_pi`'s. -/
theorem linearTranspose_spec (hp : Placed code k)
    (hpi : Spec (Labels.label NativeRustcVmArm.Vm.KeccakPi.entryLabel) KeccakPiPre KeccakPiPost) (ws : Array EW) :
    Spec (Labels.label NativeRustcVmArm.Vm.LinearTranspose.entryLabel) (LinearTransposePre ws) (LinearTransposePost ws) := by
  intro m0 hpre
  have hl : Labels.label NativeRustcVmArm.Vm.LinearTranspose.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.LinearTranspose.b0Offset) := hp.label (j := NativeRustcVmArm.Vm.LinearTranspose.entryOffset) NativeRustcVmArm.Vm.LinearTranspose.entry_at
  rw [hl]
  exact (entry hp hpre).bind fun s1 ⟨hpc1, hI1⟩ ↦
    (lanes_loop hp hpre hpi hpc1 hI1).bind fun s2 ⟨hpc2, hI2⟩ ↦
      (columns hp hpre hpc2 hI2).bind fun s3 ⟨hpc3, hI3⟩ ↦
        (output hp hpre hpc3 hI3).bind fun s4 ⟨hpc4, hI4⟩ ↦ finish hp hpre hpc4 hI4

end

end NativeRustcVmArm.KeccakGkr.LinearTranspose
