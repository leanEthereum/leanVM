module

public import NativeRustcVmArm.Code.Vm.Decode.Names
public import NativeRustcVmArm.Top.Leanvm.Stage2

/-!
# `leanvm_verify`: the decoder's two calls

`decodeEmpty` (from `b15`, the empty wire: the dangling pointer `1`) and `decodeWire` (from `b12`,
a nonempty wire): `decode`'s call, then `0` when it refuses the bytes, else `C2` at
`.LLeanvmVerify_14`.
-/

namespace NativeRustcVmArm.Top.Leanvm

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.LeanvmVerify NativeVm
open NativeRustcVm (WordAt WordsAt Region)
open NativeRustcVm.Top (workAreaBytes usedRegions ApartFrom Aligned)
open NativeRustcVm.Wire (streamW openingsW)
open NativeVm.Wire (decodeM PhaseOut)
open LeanVM.Parameters (E)

/-- What `decode` ends in: `0` and the bytes refused, or the decoded proof at
`.LLeanvmVerify_14`. -/
@[expose] public def Decoded [Host] (k : Nat) (a : NativeVm.Entry.Areas) (bytes : List UInt8)
    (bytecode : List UInt64) (pub : Vector UInt64 4) (m0 : MachineData) (st : MachineState) :
    Prop :=
  (decodeM bytes = none ∧ st.pc = retOf m0 ∧ st.data.regs.X0 = 0 ∧
      SameOutside m0.dmem st.data.dmem (R2 a bytes.length m0) ∧ Saved m0 st.data) ∨
    (∃ r, decodeM bytes = some r ∧ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.LeanvmVerify.b17Offset) ∧
      C2 a bytes bytecode pub m0 st.data r)

public section

variable [Host] {k : Nat}

/-- The frame's setup and the registers before `bl decode`. -/
structure PreCall (a : NativeVm.Entry.Areas) (bytes : List UInt8) (bytecode : List UInt64)
    (pub : Vector UInt64 4) (m0 st : MachineData) : Prop where
  body : Body m0 128 slots (InStack m0 leanvmVerifyStack) st
  pubAt : WordsAt st.dmem (frameOf m0 + BitVec.ofNat 64 8) pub.toList
  x2 : st.regs.X2 = a.decoded
  x3 : st.regs.X3 = (decodedWords bytes.length).toUInt64
  x4 : st.regs.X4 = a.work
  x19 : st.regs.X19 = bytes.length.toUInt64
  x20 : st.regs.X20 = bytecode.length.toUInt64
  x21 : st.regs.X21 = (decodedWords bytes.length).toUInt64
  x22 : st.regs.X22 = a.work
  x23 : st.regs.X23 = a.decoded
  x24 : st.regs.X24 = a.bytecode

/-- `b12`/`b15`'s effect: from `C1`, the frame body after the stores and the registers. -/
theorem preCall {a : NativeVm.Entry.Areas} {bytes : List UInt8} {bytecode : List UInt64}
    {pub : Vector UInt64 4} {m0 st st' : MachineData} {S : SState}
    (hpre : LeanvmVerifyPre a bytes bytecode pub m0) (h1 : C1 a bytes bytecode pub m0 st)
    (hm₀ : Match (Env.ofMachine st [(frameOf m0, 128)]) frameS st)
    (hwf : (Env.ofMachine st [(frameOf m0, 128)]).WF)
    (hm : Match (Env.ofMachine st [(frameOf m0, 128)]) S st')
    (hk : keepsRegs frameS S nonslots = true)
    (hmem : ∀ w ∈ S.mem, w.r = 0 ∧ 8 ≤ w.off ∧ w.off + w.n ≤ 40)
    (hw : ∀ p ∈ pubWords, ∀ i < 8, findWrite 0 (p.1 + i) S.mem = some (.reg p.2, i))
    (r2 : S.reg .X2 = some (.reg .X23)) (r3 : S.reg .X3 = some (.reg .X21))
    (r4 : S.reg .X4 = some (.reg .X22)) (r19 : S.reg .X19 = some (.reg .X19))
    (r20 : S.reg .X20 = some (.reg .X20)) (r21 : S.reg .X21 = some (.reg .X21))
    (r22 : S.reg .X22 = some (.reg .X22)) (r23 : S.reg .X23 = some (.reg .X23))
    (r24 : S.reg .X24 = some (.reg .X24)) : PreCall a bytes bytecode pub m0 st' := by
  have g := geo_of hpre
  have hs := g.s
  have hF := g.F
  have hS := leanvmVerifyStack_eq
  have hsl := m0.regs.SP.toBitVec.isLt
  have mv : ∀ {r r' : XReg} {x : UInt64}, S.reg r = some (.reg r') → st.regs.getXReg r' = x →
      st'.regs.getXReg r = x := fun h e ↦ (UInt64.toBitVec_inj.mp (hm.regs _ _ h)).trans e
  refine ⟨h1.body.block' slotsIn (by omega) hm₀ hm hwf rfl hk (fun _ hr hn ↦ nonslot hr hn)
      fun q hq ↦ ?_, pubAt_of hw h1.x13 h1.x12 h1.x11 h1.x10 hm, mv r2 h1.x23, mv r3 h1.x21,
    mv r4 h1.x22, mv r19 h1.x19, mv r20 h1.x20, mv r21 h1.x21, mv r22 h1.x22, mv r23 h1.x23,
    mv r24 h1.x24⟩
  have := written_sub (r := 0) rfl hmem hq
  rw [hF] at this
  refine ⟨?_, by omega⟩
  unfold InStack; omega

/-- **`decode`'s call**, its return at `next`. -/
theorem callDecode (hdec : Spec (Labels.label NativeRustcVmArm.Vm.Decode.entryLabel) DecodePre DecodePost)
    {a : NativeVm.Entry.Areas} {bytes : List UInt8} {bytecode : List UInt64} {pub : Vector UInt64 4}
    {m0 : MachineData} (hpre : LeanvmVerifyPre a bytes bytecode pub m0) {st : MachineState}
    {next : Int64} (hpc : PcOk (Env.ofMachine st.data []) (.call NativeRustcVmArm.Vm.Decode.entryLabel) next st)
    (hP : PreCall a bytes bytecode pub m0 st.data) (hD : DecodePre st.data)
    (hBy : BytesAt st.data.dmem st.data.regs.X0.toBitVec bytes)
    (hX1 : st.data.regs.X1.toNat = bytes.length)
    {Q : MachineState → Prop}
    (cont : ∀ st' : MachineState, st'.pc = next →
      (match decodeM bytes with
        | some r => st'.data.regs.X0 = (1 : UInt64) ∧ NativeRustcVm.Transcript.DecodedAt
            st'.data.dmem ⟨a.decoded.toBitVec, decodedWords bytes.length, bytes.length⟩
            (streamW r.1) (openingsW r.2)
        | none => st'.data.regs.X0 = (0 : UInt64) : Prop) →
      Body m0 128 slots (R2 a bytes.length m0) st'.data →
      WordsAt st'.data.dmem (frameOf m0 + BitVec.ofNat 64 8) pub.toList →
      Saved st.data st'.data → Eventually (step1 Host.exe) Q st') :
    Eventually (step1 Host.exe) Q st := by
  refine call_then hpc hdec hD fun st' hpc' hpost ↦ ?_
  obtain ⟨hres, hsame, hsaved⟩ := hpost
  obtain ⟨hB', hpub'⟩ := afterCall hpre hP.body hP.pubAt hP.x2 hP.x3 hP.x4 hsame hsaved
  have hX3 : st.data.regs.X3.toNat = decodedWords bytes.length := by
    rw [hP.x3]; exact natToU64 (by have := (geo_of hpre).decN; omega)
  have h := hres bytes hX1.symm hBy
  rw [hX1, hP.x2, hX3] at h
  exact cont st' hpc' h hB' hpub' hsaved

end

end NativeRustcVmArm.Top.Leanvm
