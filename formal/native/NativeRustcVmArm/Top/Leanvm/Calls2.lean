module

public import NativeRustcVmArm.Code.Vm.Decode.Names
public import NativeRustcVmArm.Top.Leanvm.Calls

/-!
# `leanvm_verify`: the decoder's paths

`decodeWire` (`b11`, `b12`, the call, `b13`, `b14`), `decodeEmpty` (`b15`, the call, `b16`) and
`stage2`, which dispatches on `L` at `b10`: each ends in `Decoded`.
-/

namespace NativeRustcVmArm.Top.Leanvm

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.LeanvmVerify NativeVm
open NativeRustcVm (WordAt WordsAt Region)
open NativeRustcVm.Top (workAreaBytes usedRegions ApartFrom Aligned)
open NativeRustcVm.Wire (streamW openingsW)
open NativeVm.Wire (decodeM PhaseOut)
open LeanVM.Parameters (E)

public section

/-- `C2` after the call, from `PreCall` and `Saved`. -/
theorem c2_of {a : NativeVm.Entry.Areas} {bytes : List UInt8} {bytecode : List UInt64}
    {pub : Vector UInt64 4} {m0 st st' : MachineData} {r : List E × List PhaseOut}
    (hP : PreCall a bytes bytecode pub m0 st) (hsaved : Saved st st')
    (hB : Body m0 128 slots (R2 a bytes.length m0) st')
    (hpub : WordsAt st'.dmem (frameOf m0 + BitVec.ofNat 64 8) pub.toList)
    (hd : NativeRustcVm.Transcript.DecodedAt st'.dmem ⟨a.decoded.toBitVec,
      decodedWords bytes.length, bytes.length⟩ (streamW r.1) (openingsW r.2)) :
    C2 a bytes bytecode pub m0 st' r :=
  ⟨hB, hpub, hd, (hsaved.1 .X19 rfl).trans hP.x19, (hsaved.1 .X20 rfl).trans hP.x20,
    (hsaved.1 .X21 rfl).trans hP.x21, (hsaved.1 .X22 rfl).trans hP.x22,
    (hsaved.1 .X23 rfl).trans hP.x23, (hsaved.1 .X24 rfl).trans hP.x24⟩

/-- `C2` across a block without memory keeping X19 to X24. -/
theorem C2.step [Labels] {a : NativeVm.Entry.Areas} {bytes : List UInt8} {bytecode : List UInt64}
    {pub : Vector UInt64 4} {m0 st st' : MachineData} {r : List E × List PhaseOut} {S : SState}
    (h : C2 a bytes bytecode pub m0 st r) (hs : 128 ≤ m0.regs.SP.toBitVec.toNat)
    (hm : Match (Env.ofMachine st []) S st') (hk : keepsRegs noneS S nonslots = true)
    (hmem : S.mem = []) (r19 : S.reg .X19 = some (.reg .X19))
    (r20 : S.reg .X20 = some (.reg .X20)) (r21 : S.reg .X21 = some (.reg .X21))
    (r22 : S.reg .X22 = some (.reg .X22)) (r23 : S.reg .X23 = some (.reg .X23))
    (r24 : S.reg .X24 = some (.reg .X24)) : C2 a bytes bytecode pub m0 st' r := by
  have hd : st'.dmem = st.dmem := hm.dmem_eq (Env.wf_nil _) hmem
  exact ⟨bodyNo h.body hs (match_nil _) hm (Env.wf_nil _) rfl hk hmem, hd ▸ h.pubAt,
    hd ▸ h.dec, (keepReg' _ hm r19).trans h.x19, (keepReg' _ hm r20).trans h.x20,
    (keepReg' _ hm r21).trans h.x21, (keepReg' _ hm r22).trans h.x22,
    (keepReg' _ hm r23).trans h.x23, (keepReg' _ hm r24).trans h.x24⟩

theorem evalW32 [Labels] (env : Env) {x : UInt64} (h : env.regs .X0 = x.toBitVec) :
    (SBool.cmp .eq .W32 (.reg .X0) (.lit 0)).eval env = (x.toBitVec.setWidth 32 == 0#32) := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W32, h]
  rfl

theorem evalBit0 [Labels] (env : Env) {x : UInt64} (h : env.regs .X0 = x.toBitVec) :
    (SBool.not (SBool.bit .W32 (.reg .X0) 0)).eval env = !(x.toBitVec.getLsbD 0) := by
  simp only [SBool.eval, Sym.eval, low_W32, h, BitVec.getLsbD_setWidth]
  simp

variable [Host] {k : Nat}

/-- **A nonempty wire**: from `b11`. -/
theorem decodeWire (hp : Placed code k)
    (hdec : Spec (Labels.label NativeRustcVmArm.Vm.Decode.entryLabel) DecodePre DecodePost)
    {a : NativeVm.Entry.Areas} {bytes : List UInt8} {bytecode : List UInt64} {pub : Vector UInt64 4}
    {m0 : MachineData} (hpre : LeanvmVerifyPre a bytes bytecode pub m0) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LeanvmVerify.b11Offset)) (h1 : C1 a bytes bytecode pub m0 st.data)
    (hL0 : 0 < bytes.length) :
    Eventually (step1 Host.exe) (Decoded k a bytes bytecode pub m0) st := by
  have g := geo_of hpre
  have hpre' := hpre
  obtain ⟨⟨-, -, hmap⟩, -, hin, hal, -, -⟩ := hpre'
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
  -- `b11`: the wire's address nonzero.
  refine exec_at (hb NativeRustcVmArm.Vm.LeanvmVerify.b11Offset hp b11_in_code (by simp [b11])) run_b11 (Env.wf_nil _) hpc (match_nil _)
    fun st11 hm11 hpc11 ↦ ?_
  have hk11 := none_keeps b11 (by simp)
  rw [after_eq run_b11] at hk11
  have h11 := h1.step hs128 hm11 hk11.1 hk11.2 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  simp only [PcOk, evalReg0 (Env.ofMachine st.data []) (r := .X9) (x := a.wire)
    (congrArg UInt64.toBitVec h1.x9), hal.wire hL0, decide_false, Bool.false_eq_true,
    ite_false, show k + NativeRustcVmArm.Vm.LeanvmVerify.b11Offset + b11.length = k + NativeRustcVmArm.Vm.LeanvmVerify.b12Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.LeanvmVerify.b11_next]] at hpc11
  -- `b12`: the public input in the frame, `decode`'s arguments.
  obtain ⟨hwf, hm⟩ := frameEnv h11.body hs128 hal16 (Mapped.kept hFm0 h11.body.kept)
  refine exec_at (hb NativeRustcVmArm.Vm.LeanvmVerify.b12Offset hp b12_in_code (by simp [b12])) run_b12 hwf hpc11 hm
    fun st12 hm12 hpc12 ↦ ?_
  have hk := b12_keeps
  rw [after_eq run_b12] at hk
  have hmem := b12_mem
  rw [after_eq run_b12] at hmem
  have hw := b12_pub
  rw [after_eq run_b12] at hw
  have hP := preCall hpre h11 hm hwf hm12 hk hmem hw rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hX0 : st12.data.regs.X0 = a.wire := (UInt64.toBitVec_inj.mp (hm12.regs .X0 _ rfl)).trans h11.x9
  have hX1 : st12.data.regs.X1 = bytes.length.toUInt64 :=
    (UInt64.toBitVec_inj.mp (hm12.regs .X1 _ rfl)).trans h11.x19
  have hD := decPre hpre hP.body (fun _ ↦ hX0) hX1 hP.x2 hP.x3 hP.x4
  have hBy : BytesAt st12.data.dmem st12.data.regs.X0.toBitVec bytes := by
    rw [hX0]
    have gw := g.wire hL0
    have gwN := g.wireN
    have ewi : a.wire.toBitVec.toNat = a.wire.toNat := rfl
    exact bytesAt_keep (wireBytes hin).1 hP.body.same (by omega) fun q hq ↦ by
      unfold InStack at hq; omega
  have hX1n : st12.data.regs.X1.toNat = bytes.length := by
    rw [hX1]; exact natToU64 (by have := hin.L32; omega)
  refine callDecode hdec hpre hpc12 hP hD hBy hX1n fun st13 hpc13 hres hB13 hpub13 hsaved ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.LeanvmVerify.b12Offset + b12.length = k + NativeRustcVmArm.Vm.LeanvmVerify.b13Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.LeanvmVerify.b12_next]] at hpc13
  -- `b13`: the verdict's test.
  refine exec_at (hb NativeRustcVmArm.Vm.LeanvmVerify.b13Offset hp b13_in_code (by simp [b13])) run_b13 (Env.wf_nil _) hpc13
    (match_nil _) fun st14 hm14 hpc14 ↦ ?_
  have hk14 := none_keeps b13 (by simp)
  rw [after_eq run_b13] at hk14
  have hB14 := bodyNo hB13 hs128 (match_nil _) hm14 (Env.wf_nil _) rfl hk14.1 hk14.2
  have hd14 : st14.data.dmem = st13.data.dmem := hm14.dmem_eq (Env.wf_nil _) hk14.2
  cases hr : decodeM bytes with
  | none =>
    rw [hr] at hres
    simp only [PcOk, evalW32 (Env.ofMachine st13.data []) (x := 0)
      (congrArg UInt64.toBitVec hres)] at hpc14
    simp only [show ((0 : UInt64).toBitVec.setWidth 32 == 0#32) = true from rfl,
      ite_true] at hpc14
    rw [lbl_1 hp] at hpc14
    exact Eventually.mono (failExit hp hs128 hal16 hpc14 hB14
      (by rw [hd14]; exact Mapped.kept hFm0 hB13.kept)) fun st' h ↦ Or.inl ⟨hr, h⟩
  | some r =>
    rw [hr] at hres
    have hc2 := c2_of hP hsaved hB13 hpub13 hres.2
    simp only [PcOk, evalW32 (Env.ofMachine st13.data []) (x := 1)
      (congrArg UInt64.toBitVec hres.1)] at hpc14
    rw [show ((1 : UInt64).toBitVec.setWidth 32 == 0#32) = false from rfl,
      show k + NativeRustcVmArm.Vm.LeanvmVerify.b13Offset + b13.length = k + NativeRustcVmArm.Vm.LeanvmVerify.b14Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.LeanvmVerify.b13_next]] at hpc14
    simp only [Bool.false_eq_true, ite_false] at hpc14
    have h14 := hc2.step hs128 hm14 hk14.1 hk14.2 rfl rfl rfl rfl rfl rfl
    refine exec_at (hb NativeRustcVmArm.Vm.LeanvmVerify.b14Offset hp b14_in_code (by simp [b14])) run_b14 (Env.wf_nil _) hpc14
      (match_nil _) fun st15 hm15 hpc15 ↦ ?_
    have hk15 := none_keeps b14 (by simp)
    rw [after_eq run_b14] at hk15
    have h15 := h14.step hs128 hm15 hk15.1 hk15.2 rfl rfl rfl rfl rfl rfl
    simp only [PcOk] at hpc15
    rw [lbl_14 hp] at hpc15
    exact Eventually.done _ (Or.inr ⟨r, hr, hpc15, h15⟩)

end

end NativeRustcVmArm.Top.Leanvm
