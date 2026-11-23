module

public import NativeRustcVmArm.Code.Vm.Decode.Names
public import NativeRustcVmArm.Top.Leanvm.Calls2

/-!
# `leanvm_verify`: the empty wire, and the dispatch on `L`

`decodeEmpty` (`b15`, the call on the dangling pointer `1`, `b16`) and `stage2` (`b10`).
-/

namespace NativeRustcVmArm.Top.Leanvm

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.LeanvmVerify NativeVm
open NativeRustcVm (WordAt WordsAt Region)
open NativeRustcVm.Wire (streamW openingsW)
open NativeVm.Wire (decodeM PhaseOut)

public section

variable [Host] {k : Nat}

/-- **An empty wire**: from `b15`. -/
theorem decodeEmpty (hp : Placed code k)
    (hdec : Spec (Labels.label NativeRustcVmArm.Vm.Decode.entryLabel) DecodePre DecodePost)
    {a : NativeVm.Entry.Areas} {bytes : List UInt8} {bytecode : List UInt64} {pub : Vector UInt64 4}
    {m0 : MachineData} (hpre : LeanvmVerifyPre a bytes bytecode pub m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LeanvmVerify.b15Offset)) (h1 : C1 a bytes bytecode pub m0 st.data)
    (hL0 : bytes.length = 0) :
    Eventually (step1 Host.exe) (Decoded k a bytes bytecode pub m0) st := by
  have g := geo_of hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, hmap⟩, -, -, -, -, -⟩ := hpre'
  have hs := g.s
  have hF := g.F
  have hsb : (m0.regs.SP.toBitVec - BitVec.ofNat 64 leanvmVerifyStack).toNat =
      m0.regs.SP.toBitVec.toNat - 19344 := g.sb
  have hS := leanvmVerifyStack_eq
  have hsl := m0.regs.SP.toBitVec.isLt
  have hs128 : 128 ≤ m0.regs.SP.toBitVec.toNat := by omega
  have hal16 := g.al
  have hFm0 : Mapped m0.dmem (frameOf m0) 128 :=
    Mapped.within hmap (by rw [hsb]; omega) (by rw [hsb, hF]; omega) (by rw [hsb, hF]; omega)
  obtain ⟨hwf, hm⟩ := frameEnv h1.body hs128 hal16 (Mapped.kept hFm0 h1.body.kept)
  refine exec_at (hb NativeRustcVmArm.Vm.LeanvmVerify.b15Offset hp b15_in_code (by simp [b15])) run_b15 hwf hpc hm
    fun st15 hm15 hpc15 ↦ ?_
  have hk := b15_keeps
  rw [after_eq run_b15] at hk
  have hmem := b15_mem
  rw [after_eq run_b15] at hmem
  have hw := b15_pub
  rw [after_eq run_b15] at hw
  have hP := preCall hpre h1 hm hwf hm15 hk hmem hw rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hX1 : st15.data.regs.X1 = bytes.length.toUInt64 := by
    rw [hL0]; exact UInt64.toBitVec_inj.mp (hm15.regs .X1 _ rfl)
  have hD := decPre hpre hP.body (fun h ↦ absurd hL0 (by omega)) hX1 hP.x2 hP.x3 hP.x4
  have hBy : BytesAt st15.data.dmem st15.data.regs.X0.toBitVec bytes := by
    rw [List.eq_nil_of_length_eq_zero hL0]
    exact NativeRustcVm.BytesAt.nil _ _
  have hX1n : st15.data.regs.X1.toNat = bytes.length := by rw [hX1, hL0]; rfl
  refine callDecode hdec hpre hpc15 hP hD hBy hX1n fun st16 hpc16 hres hB16 hpub16 hsaved ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.LeanvmVerify.b15Offset + b15.length = k + NativeRustcVmArm.Vm.LeanvmVerify.b16Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.LeanvmVerify.b15_next]] at hpc16
  -- `b16`: the verdict's test.
  refine exec_at (hb NativeRustcVmArm.Vm.LeanvmVerify.b16Offset hp b16_in_code (by simp [b16])) run_b16 (Env.wf_nil _) hpc16
    (match_nil _) fun st17 hm17 hpc17 ↦ ?_
  have hk17 := none_keeps b16 (by simp)
  rw [after_eq run_b16] at hk17
  have hB17 := bodyNo hB16 hs128 (match_nil _) hm17 (Env.wf_nil _) rfl hk17.1 hk17.2
  have hd17 : st17.data.dmem = st16.data.dmem := hm17.dmem_eq (Env.wf_nil _) hk17.2
  cases hr : decodeM bytes with
  | none =>
    rw [hr] at hres
    simp only [PcOk, evalBit0 (Env.ofMachine st16.data []) (x := 0)
      (congrArg UInt64.toBitVec hres)] at hpc17
    simp only [show ((0 : UInt64).toBitVec.getLsbD 0) = false from rfl, Bool.not_false,
      ite_true] at hpc17
    rw [lbl_1 hp] at hpc17
    exact Eventually.mono (failExit hp hs128 hal16 hpc17 hB17
      (by rw [hd17]; exact Mapped.kept hFm0 hB16.kept)) fun st' h ↦ Or.inl ⟨hr, h⟩
  | some r =>
    rw [hr] at hres
    have hc2 := c2_of hP hsaved hB16 hpub16 hres.2
    simp only [PcOk, evalBit0 (Env.ofMachine st16.data []) (x := 1)
      (congrArg UInt64.toBitVec hres.1)] at hpc17
    simp only [show ((1 : UInt64).toBitVec.getLsbD 0) = true from rfl, Bool.not_true,
      Bool.false_eq_true, ite_false, show k + NativeRustcVmArm.Vm.LeanvmVerify.b16Offset + b16.length = k + NativeRustcVmArm.Vm.LeanvmVerify.b17Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.LeanvmVerify.b16_next]] at hpc17
    exact Eventually.done _ (Or.inr ⟨r, hr, hpc17,
      hc2.step hs128 hm17 hk17.1 hk17.2 rfl rfl rfl rfl rfl rfl⟩)

/-- **The decoder**, from `.LLeanvmVerify_10`. -/
theorem stage2 (hp : Placed code k)
    (hdec : Spec (Labels.label NativeRustcVmArm.Vm.Decode.entryLabel) DecodePre DecodePost)
    {a : NativeVm.Entry.Areas} {bytes : List UInt8} {bytecode : List UInt64} {pub : Vector UInt64 4}
    {m0 : MachineData} (hpre : LeanvmVerifyPre a bytes bytecode pub m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LeanvmVerify.b10Offset)) (h1 : C1 a bytes bytecode pub m0 st.data) :
    Eventually (step1 Host.exe) (Decoded k a bytes bytecode pub m0) st := by
  have g := geo_of hpre
  have hs := g.s
  have hL := hpre.2.2.1.L32
  have hs128 : 128 ≤ m0.regs.SP.toBitVec.toNat := by omega
  refine exec_at (hb NativeRustcVmArm.Vm.LeanvmVerify.b10Offset hp b10_in_code (by simp [b10])) run_b10 (Env.wf_nil _) hpc (match_nil _)
    fun st10 hm10 hpc10 ↦ ?_
  have hk10 := none_keeps b10 (by simp)
  rw [after_eq run_b10] at hk10
  have h10 := h1.step hs128 hm10 hk10.1 hk10.2 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  simp only [PcOk, evalRegNat0 (Env.ofMachine st.data []) (r := .X19)
    (congrArg UInt64.toBitVec h1.x19) (by omega)] at hpc10
  by_cases hL0 : bytes.length = 0
  · simp only [hL0, decide_true, ite_true] at hpc10
    rw [lbl_13 hp] at hpc10
    exact decodeEmpty hp hdec hpre hpc10 h10 hL0
  · simp only [hL0, decide_false, Bool.false_eq_true, ite_false,
      show k + NativeRustcVmArm.Vm.LeanvmVerify.b10Offset + b10.length = k + NativeRustcVmArm.Vm.LeanvmVerify.b11Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.LeanvmVerify.b10_next]] at hpc10
    exact decodeWire hp hdec hpre hpc10 h10 (by omega)

end

end NativeRustcVmArm.Top.Leanvm
