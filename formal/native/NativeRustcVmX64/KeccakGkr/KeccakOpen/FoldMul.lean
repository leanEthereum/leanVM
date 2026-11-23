module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.FoldLoad
public import NativeRustcVmX64.Code.Vm.KeccakOpen
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-! # `keccak_open`: loading an inner-loop element and multiplying its difference -/

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.KeccakOpen
open NativeRustcVm.Transcript (off off_zero off_off off_add DecArea)

public section

variable [Host] {k : Nat} {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

/-- Load the two buffer elements, call `EW::mul`, and preserve the fold's frame. -/
theorem load_mul (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (h : PreOk a s c m0) {cx : Cx} (ha : cx.a = a)
    {j s0 : Nat} (hj : j < 64) {ib cx0 cx1 lo0 lo1 : Reg64} {keep : List Reg64}
    {b : List Directive} {kb : Nat} (hin : b.IsInfixAt code kb) (hne : b ≠ [])
    {S : SState} (hex : exec b (loS ib s0) = some (S, .call NativeRustcVmX64.Vm.EWMul.entryLabel))
    (hok : lOk cx0 cx1 lo0 lo1 keep S = true)
    {fa fb : Nat → EW} {cc : EW} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + kb)) (hm : Mid cx m0 8 st.data)
    (hib : reg st.data ib = BitVec.ofNat 64 (s0 + 16 * j))
    (hc0 : reg st.data cx0 = cc.c0.toBitVec) (hc1 : reg st.data cx1 = cc.c1.toBitVec)
    (hbufA : ElemsAt st.data.dmem (off (fbA m0) 112) fa 64)
    (hbufB : ElemsAt st.data.dmem (off (fbA m0) 1136) fb 64) :
    Eventually (step1 Host.exe) (fun st' ↦ st'.pc = Host.addrOf (k + kb + b.length) ∧
      Mid cx m0 8 st'.data ∧
      reg st'.data .rax = (cc * (fa j + fb j)).c0.toBitVec ∧
      reg st'.data .rdx = (cc * (fa j + fb j)).c1.toBitVec ∧
      reg st'.data lo0 = (fa j).c0.toBitVec ∧ reg st'.data lo1 = (fa j).c1.toBitVec ∧
      (∀ r e, calleeSaved r = true → S.reg r = some e →
        reg st'.data r = e.eval (loadEnv m0 st.data j (Host.addrOf (k + kb + b.length)).toBitVec)) ∧
      NativeRustcVm.SameOutside st.data.dmem st'.data.dmem (MulRange m0)) st := by
  simp only [lOk, Bool.and_eq_true, beq_iff_eq, and_assoc] at hok
  obtain ⟨hdi, hsi, hdx, hcx, hlo0, hlo1, hsp, hmem, hcl0, hcl1, _⟩ := hok
  have hwf := load_wf h hm.fr.kept hj (ret := (Host.addrOf (k + kb + b.length)).toBitVec)
  have hl := load_buffer hj hbufA hbufB (ret := (Host.addrOf (k + kb + b.length)).toBitVec)
  refine exec_at (infix_of hin hne hp) hex hwf (fun _ _ ↦ rfl) hpc (load_match hm hib)
    fun st1 hm1 hpc1 ↦ ?_
  have hs1 : NativeRustcVm.SameOutside st.data.dmem st1.data.dmem
      (NativeRustcVm.InRange (fbA m0) 8) :=
    sameOutside_low hwf hm1 (r := 0) (N := 8) (hi := 8) rfl (by decide) (by
      intro w hw
      rw [hmem] at hw
      simp only [List.mem_singleton] at hw
      subst hw
      exact ⟨rfl, by decide⟩)
  have hsp1 : rspOf st1.data = fbA m0 := by
    show st1.data.regs.get64 .rsp = _
    rw [hm1.regs .rsp _ hsp]
    change fbA m0 + BitVec.ofInt 64 0 = _
    rw [ofInt0, BitVec.add_zero]
  have hf1 := frame_low h hm.fr (o' := 0) (by rw [off_zero]; exact hsp1) (hm1.kept hwf) hs1
  have hmid1 := Mid.keep h hm hf1 (hm1.kept hwf) hs1 (fun _ hq ↦ low_safe h hq) ha
  have hd : reg st1.data .rdi = cc.c0.toBitVec := (hm1.regs .rdi _ hdi).trans hc0
  have hsi' : reg st1.data .rsi = cc.c1.toBitVec := (hm1.regs .rsi _ hsi).trans hc1
  have dx : reg st1.data .rdx = (fa j + fb j).c0.toBitVec := by
    rw [show reg st1.data .rdx = _ from hm1.regs .rdx _ hdx]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, hl.1, hl.2.2.1]
    change (fb j).c0.toBitVec ^^^ (fa j).c0.toBitVec = ((fa j).c0 ^^^ (fb j).c0).toBitVec
    rw [UInt64.toBitVec_xor, BitVec.xor_comm]
  have cx' : reg st1.data .rcx = (fa j + fb j).c1.toBitVec := by
    rw [show reg st1.data .rcx = _ from hm1.regs .rcx _ hcx]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, hl.2.1, hl.2.2.2]
    change (fb j).c1.toBitVec ^^^ (fa j).c1.toBitVec = ((fa j).c1 ^^^ (fb j).c1).toBitVec
    rw [UInt64.toBitVec_xor, BitVec.xor_comm]
  have hle : 2208 + ewMulStack ≤ keccakOpenStack := by decide
  refine call_then hpc1 hmul (stackOk_callee h.st hf1.kept hsp1 hle)
    fun st2 hpc2 hrsp2 ⟨h0, h1, hs2, hsv2⟩ ↦ ?_
  rw [hd, hsi', dx, cx', UInt64.ofBitVec_toBitVec, UInt64.ofBitVec_toBitVec,
    UInt64.ofBitVec_toBitVec, UInt64.ofBitVec_toBitVec] at h0 h1
  have hcal : ∀ q, NativeRustcVm.InRange (stackBelow st1.data ewMulStack) ewMulStack q →
      ¬ NativeRustcVm.InRange (fbA m0) 2216 q := fun q hq ↦
    (inRange_callee hsp1 h.st.2.1 h.st.1 hle hq).2
  have hf2 := hf1.call hsv2 hrsp2 hs2 hcal (frame_noWrap h.st (by rw [stack_eq]; decide)) slots_le'
  have hmid2 := Mid.keep h hmid1 hf2 hsv2.2 hs2 (fun _ hq ↦ mul_safe h hsp1 hq) ha
  refine .done _ ⟨hpc2, hmid2, h0, h1, ?_, ?_, ?_, ?_⟩
  · exact (hsv2.1 lo0 hcl0).trans ((hm1.regs lo0 _ hlo0).trans hl.1)
  · exact (hsv2.1 lo1 hcl1).trans ((hm1.regs lo1 _ hlo1).trans hl.2.1)
  · intro r e hr he
    exact (hsv2.1 r hr).trans (hm1.regs r e he)
  · intro q hq
    exact (hs2 q fun hq' ↦ hq (mul_range h hsp1 hq')).trans
      (hs1 q fun hq' ↦ hq (low_range h hq'))

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
