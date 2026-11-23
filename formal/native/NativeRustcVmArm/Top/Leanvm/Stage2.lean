module

public import NativeRustcVmArm.Top.Leanvm.Decode

/-!
# `leanvm_verify`: the decoder's call

`stage2`: from `C1` at `.LLeanvmVerify_10`, the call of `decode` (by `b12` or `b15`), then `0`
when it refuses the bytes, else `C2` at `.LLeanvmVerify_14`. `afterCall`: what the frame keeps
across the call.
-/

namespace NativeRustcVmArm.Top.Leanvm

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.LeanvmVerify NativeVm
open NativeRustcVm (WordAt WordsAt Region)
open NativeRustcVm.Top (workAreaBytes entryRegions ApartFrom Aligned)
open NativeRustcVm.Wire (streamW openingsW)
open NativeVm.Wire (decodeM PhaseOut)
open LeanVM.Parameters (E)

public section

/-- Across `decode`: the body, the public input in the frame, the registers. -/
theorem afterCall [Labels] {a : NativeVm.Entry.Areas} {bytes : List UInt8} {bytecode : List UInt64}
    {pub : Vector UInt64 4} {m0 st st' : MachineData}
    (hpre : LeanvmVerifyPre a bytes bytecode pub m0)
    (hB : Body m0 128 slots (InStack m0 leanvmVerifyStack) st)
    (hpub : WordsAt st.dmem (frameOf m0 + BitVec.ofNat 64 8) pub.toList)
    (hx2 : st.regs.X2 = a.decoded) (hx3 : st.regs.X3 = (decodedWords bytes.length).toUInt64)
    (hx4 : st.regs.X4 = a.work)
    (hsame : SameOutside st.dmem st'.dmem (NativeRustcVm.InAny [⟨st.regs.X2.toBitVec,
      8 * st.regs.X3.toNat⟩, ⟨st.regs.X4.toBitVec, NativeRustcVm.Wire.workBytes⟩,
      stackR st decodeStack]))
    (hsaved : Saved st st') :
    Body m0 128 slots (R2 a bytes.length m0) st' ∧
      WordsAt st'.dmem (frameOf m0 + BitVec.ofNat 64 8) pub.toList := by
  have g := geo_of hpre
  have hs := g.s
  have hF := g.F
  have hsl := m0.regs.SP.toBitVec.isLt
  have hS := leanvmVerifyStack_eq
  have hsp : st.regs.SP.toBitVec = frameOf m0 := hB.sp
  have hDS : decodeStack = 1280 := rfl
  have hwb : NativeRustcVm.Wire.workBytes = 483584 := rfl
  have hwa : workAreaBytes = 495552 := rfl
  have hX3 : st.regs.X3.toNat = decodedWords bytes.length := by
    rw [hx3]; exact natToU64 (by have := g.decN; omega)
  have gd := g.dec
  have gdN := g.decN
  have gw := g.work
  have gwN := g.workN
  have ed : a.decoded.toBitVec.toNat = a.decoded.toNat := rfl
  have ew : a.work.toBitVec.toNat = a.work.toNat := rfl
  have hsbD : (stackBelow st decodeStack).toNat = m0.regs.SP.toBitVec.toNat - 1408 := by
    show (st.regs.SP.toBitVec - BitVec.ofNat 64 decodeStack).toNat = _
    rw [hsp, hDS, toNat_subAddr (by rw [hF]; omega), hF]; omega
  have hW : ∀ q, NativeRustcVm.InAny [⟨st.regs.X2.toBitVec, 8 * st.regs.X3.toNat⟩,
      ⟨st.regs.X4.toBitVec, NativeRustcVm.Wire.workBytes⟩, stackR st decodeStack] q →
      R2 a bytes.length m0 q ∧ (q.toNat < m0.regs.SP.toBitVec.toNat - 128 ∨
        m0.regs.SP.toBitVec.toNat ≤ q.toNat) := by
    intro q hq
    simp only [NativeRustcVm.InAny, List.mem_cons, List.mem_nil_iff, or_false, exists_eq_or_imp,
      exists_eq_left, NativeRustcVm.Region.Holds, stackR] at hq
    rw [hx2, hX3, hx4] at hq
    rcases hq with hq | hq | hq
    · have hq' := (NativeRustcVm.inRange_iff gdN).mp hq
      exact ⟨Or.inr (Or.inl hq), by omega⟩
    · have hq' := (NativeRustcVm.inRange_iff (show a.work.toBitVec.toNat +
        NativeRustcVm.Wire.workBytes ≤ 2 ^ 64 by omega)).mp hq
      refine ⟨Or.inr (Or.inr ((NativeRustcVm.inRange_iff gwN).mpr (by omega))), by omega⟩
    · have hq' := (NativeRustcVm.inRange_iff (show (stackBelow st decodeStack).toNat +
        decodeStack ≤ 2 ^ 64 by rw [hsbD, hDS]; omega)).mp hq
      rw [hsbD, hDS] at hq'
      refine ⟨Or.inl ?_, by omega⟩
      unfold InStack; omega
  have hF8 : (frameOf m0 + BitVec.ofNat 64 8).toNat = m0.regs.SP.toBitVec.toNat - 120 := by
    rw [toNat_addr (by rw [hF]; omega), hF]; omega
  refine ⟨(hB.mono fun q h ↦ Or.inl h).call slotsIn (by omega) hsame hsaved
    fun q hq ↦ ⟨(hW q hq).1, by have := (hW q hq).2; omega⟩, ?_⟩
  refine wordsAt_keep hpub hsame (by rw [Vector.length_toList, hF8]; omega) fun q hq ↦ ?_
  rw [Vector.length_toList, hF8]
  have := (hW q hq).2
  omega

end

end NativeRustcVmArm.Top.Leanvm
