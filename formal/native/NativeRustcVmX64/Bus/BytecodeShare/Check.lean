module

public import NativeRustcVmX64.Bus.BytecodeShare.Loop
public import NativeRustcVm.Arrays.EqKernel
public import NativeRustcVmX64.Code.Vm.BytecodeShare.Names
public import NativeRustcVmX64.Code.Vm.Dot.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EqKernel.Names

/-!
# `bytecode_share`: the kernel, the dot product, the check (x86-64)

From `b6` (the value read): `eq_kernel` of the slot point into the kernel (`b6`; it cannot fail,
`b7`), `dot` of the kernel and the weights (`b8`), times the value (`b9`), compared with the
sumcheck's claim limb by limb (`b10`, `b11`); a mismatch is the tag `0`, else the copy.
-/

namespace NativeRustcVmX64.Bus.BytecodeShare

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.BytecodeShare NativeRustcVmX64.Transcript
open NativeRustcVmX64.Sumcheck NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVm.Bus (busPointCap)

public section

theorem beq_ew (x y : EW) : (x == y) = (x.c0 == y.c0 && x.c1 == y.c1) := by
  cases x; cases y; rfl

theorem inRange_zero {q : BitVec 64} : ¬ NativeRustcVm.InRange 0 0 q := by
  unfold NativeRustcVm.InRange; omega

section
variable [Labels] {a : DecArea} {s0 : TState} {m0 : MachineData}

/-- **Bytes of the frame kept by a call** writing a local `[lo, lo + n)` of the frame. -/
theorem keep_local_call (h : BytecodeSharePre a s0 m0) {d d' : MachineData} (hat : At m0 432 d)
    {Nc : Nat} (hle : 432 + Nc ≤ bytecodeShareStack) {lo n : Nat} (hlo : lo + n ≤ 440)
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ NativeRustcVm.InRange (off (fa m0) lo) n q ∨
        NativeRustcVm.InRange (stackBelow d Nc) Nc q))
    {o : Nat} {bs : List UInt8} (ho : 8 ≤ o) (hon : o + bs.length ≤ 432)
    (hdis : o + bs.length ≤ lo ∨ lo + n ≤ o)
    (hb : NativeRustcVm.BytesAt d.dmem (off (fa m0) o) bs) :
    NativeRustcVm.BytesAt d'.dmem (off (fa m0) o) bs :=
  keep_call h hat hle hso ho hon (fun i hi ↦ not_local h (by omega) hlo (by omega)) hb

/-- **Bytes of the frame kept by a call** writing only its own stack. -/
theorem keep_stack_call (h : BytecodeSharePre a s0 m0) {d d' : MachineData} (hat : At m0 432 d)
    {Nc : Nat} (hle : 432 + Nc ≤ bytecodeShareStack)
    (hso : NativeRustcVm.SameOutside d.dmem d'.dmem
      (fun q ↦ False ∨ NativeRustcVm.InRange (stackBelow d Nc) Nc q))
    {o : Nat} {bs : List UInt8} (ho : 8 ≤ o) (hon : o + bs.length ≤ 432)
    (hb : NativeRustcVm.BytesAt d.dmem (off (fa m0) o) bs) :
    NativeRustcVm.BytesAt d'.dmem (off (fa m0) o) bs :=
  keep_call h hat hle hso ho hon (fun _ _ h ↦ h) hb

end

variable [Host] {a : DecArea} {s0 s3 : TState} {m0 : MachineData} {k : Nat}

/-- **From `b6` to the copy or the tag `0`.** -/
theorem check (hp : Placed code k) (h : BytecodeSharePre a s0 m0)
    (hek : Spec (Labels.label NativeRustcVmX64.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost)
    (hdot : Spec (Labels.label NativeRustcVmX64.Vm.Dot.entryLabel) DotPre DotPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {sh cl v : EW} {sp : Array EW} {st : MachineData} (hf : BF m0 (OT m0) 8 st)
    (w120 : NativeRustcVm.WordAt st.dmem (off (fa m0) 120) sh.c0)
    (w112 : NativeRustcVm.WordAt st.dmem (off (fa m0) 112) sh.c1)
    (w104 : NativeRustcVm.WordAt st.dmem (off (fa m0) 104) cl.c0)
    (w96 : NativeRustcVm.WordAt st.dmem (off (fa m0) 96) cl.c1)
    (hv0 : NativeRustcVm.WordAt st.dmem (off (fa m0) 136) v.c0)
    (hv1 : NativeRustcVm.WordAt st.dmem (off (fa m0) 144) v.c1)
    (hsp : NativeRustcVm.EWsAt st.dmem (off (fa m0) 32) sp.toList) (hsz : sp.size = 4)
    (hts : TStateAt st.dmem (tAt m0) a s3)
    (hres : res s0 m0 = if (cl == dot (eqKernel sp) (wts m0) * v) = true then
      some ((sh, slice m0 (bAt m0) (reg m0 .r8) ++ sp, v), s3) else none) :
    Eventually (step1 Host.exe) (Goal a s0 m0) ⟨st, Host.addrOf (k + NativeRustcVmX64.Vm.BytecodeShare.b6Offset)⟩ := by
  have c := ctx_of h
  obtain ⟨hS, -, -, -, hw, -⟩ := pre_parts h
  have hspL : sp.toList.length = 4 := by rw [Array.length_toList, hsz]
  have hspB : (sp.toList.flatMap NativeRustcVm.ewBytes).length = 64 := by
    rw [NativeRustcVm.length_ewsBytes, hspL]
  have hwB : ∀ x : UInt64, (NativeRustcVm.wordBytes x).length = 8 := NativeRustcVm.length_wordBytes
  have hfnw := c.noWrap_frame
  unfold NativeRustcVm.NoWrap at hfnw
  have hfa : (fa m0).toNat = (stackBelow m0 432).toNat := rfl
  -- `b6`: the value, the kernel zeroed, `eq_kernel` called.
  have hwf := wf_envB h hf.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.BytecodeShare.b6Offset + b6.length)).toBitVec
  refine exec_then (infix_of b6_in_code (by simp [b6]) hp) exit_b6 hwf (fun _ _ ↦ rfl)
    (match_bodyS hf _) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hrdi1, hrsi1, hrdx1, hrcx1, hr15_1, hk1, hW24, hws1⟩ := ok_b6
  obtain ⟨hf1, hs1⟩ := BF.block h hf hm1 hmid1 hk1
  have hin1 := writesIn_of_mid hmid1
  have kb1 : ∀ {o : Nat} {bs : List UInt8}, o + bs.length ≤ 128 → 32 ≤ o →
      NativeRustcVm.BytesAt st.dmem (off (fa m0) o) bs →
      NativeRustcVm.BytesAt st1.data.dmem (off (fa m0) o) bs := fun h1 h2 hb ↦
    keep_frame hwf hm1 hin1 (by omega) (fun w hw' _ ↦ by
      rcases (hws1 w hw').2 with h3 | h3 | h3 <;> omega) hb
  have hsp1 := kb1 (by rw [hspB]; omega) le_rfl hsp
  have w120_1 := kb1 (bs := NativeRustcVm.wordBytes _) (by simp [hwB]) (by omega) w120
  have w112_1 := kb1 (bs := NativeRustcVm.wordBytes _) (by simp [hwB]) (by omega) w112
  have w104_1 := kb1 (bs := NativeRustcVm.wordBytes _) (by simp [hwB]) (by omega) w104
  have w96_1 := kb1 (bs := NativeRustcVm.wordBytes _) (by simp [hwB]) (by omega) w96
  have w24_1 : NativeRustcVm.WordAt st1.data.dmem (off (fa m0) 24) v.c1 :=
    wordAt_written hm1 (r := 0) rfl (by omega) hW24 (load_ofMachine (o := 144) rfl hv1)
  have r15_1 : reg st1.data .r15 = v.c0.toBitVec :=
    (hm1.regs .r15 _ hr15_1).trans (load_ofMachine (o := 136) rfl hv0)
  have hts1 : TStateAt st1.data.dmem (tAt m0) a s3 :=
    tstate_keep h hs1 (hm1.kept hwf) (fun q hq ↦ .inr (.inr (c.inRange_frame hq))) hts
  have hat1 := hf1.at h (fun q hq ↦ OT_OA q hq)
  have e_rdi : reg st1.data .rdi = off (fa m0) 32 := (hm1.regs .rdi _ hrdi1).trans (eval_ptr0 32)
  have e_rdx : reg st1.data .rdx = off (fa m0) 128 := (hm1.regs .rdx _ hrdx1).trans (eval_ptr0 128)
  have e_rsi : (reg st1.data .rsi).toNat = 4 := by
    rw [show reg st1.data .rsi = _ from hm1.regs .rsi _ hrsi1]; rfl
  have e_rcx : (reg st1.data .rcx).toNat = 16 := by
    rw [show reg st1.data .rcx = _ from hm1.regs .rcx _ hrcx1]; rfl
  have o32 := c.outOk_frame hat1 le_ek (o := 32) (n := 64) (by omega) (by omega)
  have o128 := c.outOk_frame hat1 le_ek (o := 128) (n := 256) (by omega) (by omega)
  refine call_then hpc1 hek ?pre fun st2 hpc2 hrsp2 hpost2 ↦ ?_
  case pre =>
    unfold EqKernelPre SliceOk
    rw [e_rdi, e_rdx, e_rsi, e_rcx]
    refine ⟨c.stackOk hat1 le_ek, by omega, ⟨⟨o32.1, o32.2.1⟩, o32.2.2.2.2.1⟩,
      ⟨⟨o128.1, o128.2.1⟩, o128.2.2.2.2.1⟩, ?_⟩
    unfold NativeRustcX64.Apart
    rw [toNat_off (by omega), toNat_off (by omega)]
    omega
  obtain ⟨hk2, hch2, hsv2⟩ := hpost2
  unfold Changes at hch2
  simp only [e_rsi, e_rcx, show (2 : Nat) ^ 4 ≤ 16 from by decide, ↓reduceIte] at hk2
  rw [e_rdx, e_rdi] at hk2
  rw [e_rdx, e_rcx] at hch2
  obtain ⟨hx0, -, hker⟩ := hk2
  have hsl : slice st1.data (off (fa m0) 32) (reg st1.data .rsi) = sp := by
    unfold slice
    rw [e_rsi, ← hspL, NativeRustcVm.ewsOf_of_ewsAt hsp1, Array.toArray_toList]
  rw [hsl] at hker
  have hch2' : NativeRustcVm.SameOutside st1.data.dmem st2.data.dmem (fun q ↦
      NativeRustcVm.InRange (off (fa m0) 128) 256 q ∨
        NativeRustcVm.InRange (stackBelow st1.data eqKernelStack) eqKernelStack q) := hch2
  have hf2 : BF m0 (OT m0) 8 st2.data :=
    hf1.call h (fun q hq ↦ OT_OA q hq) le_ek hsv2 hrsp2
      (R := NativeRustcVm.InRange (off (fa m0) 128) 256)
      (fun q hq ↦ ⟨.inr (stk_local h (by omega) hq), notHigh_local h (by omega) hq⟩) hch2'
  have kc2 := fun {o : Nat} {bs : List UInt8} (h1 : 8 ≤ o) (h2 : o + bs.length ≤ 128) ↦
    keep_local_call (bs := bs) h hat1 le_ek (lo := 128) (n := 256) (by omega) hch2' h1 (by omega)
      (.inl h2)
  have hsp2 := kc2 (by omega) (by rw [hspB]; omega) hsp1
  have w120_2 := kc2 (bs := NativeRustcVm.wordBytes _) (by omega) (by simp [hwB]) w120_1
  have w112_2 := kc2 (bs := NativeRustcVm.wordBytes _) (by omega) (by simp [hwB]) w112_1
  have w104_2 := kc2 (bs := NativeRustcVm.wordBytes _) (by omega) (by simp [hwB]) w104_1
  have w96_2 := kc2 (bs := NativeRustcVm.wordBytes _) (by omega) (by simp [hwB]) w96_1
  have w24_2 := kc2 (bs := NativeRustcVm.wordBytes _) (by omega) (by simp [hwB]) w24_1
  have hts2 : TStateAt st2.data.dmem (tAt m0) a s3 :=
    tstate_keep h hch2' hsv2.2 (fun q hq ↦ .inr (.inr (hq.elim (stk_local h (by omega))
      fun hq ↦ (c.inRange_callee hat1 le_ek hq).1))) hts1
  have hker2 : NativeRustcVm.EWsAt st2.data.dmem (off (fa m0) 128) (eqKernel sp).toList := hker
  have r15_2 : reg st2.data .r15 = v.c0.toBitVec := (hsv2.1 .r15 rfl).trans r15_1
  -- `b7`: `eq_kernel` succeeded.
  have hwf7 := wf_envB h hf2.frame.kept 0
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) exit_b7 hwf7 nofun
    (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.BytecodeShare.b6_next)) (match_bodyS hf2 0) fun st7 hm7 hpc7 ↦ ?_
  obtain ⟨-, -, -, -, -, -, -, -, -, hmid7, hmem7, hk7, -⟩ := ok_test
  obtain ⟨hf7, -⟩ := BF.block h hf2 hm7 hmid7 (KeepsB.mono hk7 (by simp [six]))
  have hd7 : st7.data.dmem = st2.data.dmem := hm7.dmem_eq hwf7 hmem7
  have hc7 : c7.eval (envB m0 st2.data 0) = false := by
    show CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (reg st2.data .rax) (BitVec.ofNat 64 1))
      (BitVec.ofNat 64 0) = false
    rw [hx0]; decide
  simp only [PcOk, hc7, Bool.false_eq_true, ↓reduceIte] at hpc7
  -- `b8`: `dot` of the kernel and the weights.
  have hwf8 := wf_envB h hf7.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.BytecodeShare.b8Offset + b8.length)).toBitVec
  refine exec_at (infix_of b8_in_code (by simp [b8]) hp) exit_b8 hwf8 (fun _ _ ↦ rfl)
    (hpc7.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.BytecodeShare.b7_next)) (match_bodyS hf7 _) fun st8 hm8 hpc8 ↦ ?_
  obtain ⟨hmid8, hrdi8, hrsi8, hrdx8, hrcx8, hk8, hws8⟩ := ok_b8
  obtain ⟨hf8, hs8⟩ := BF.block h hf7 hm8 hmid8 (KeepsB.mono hk8 (by simp [six]))
  have hin8 := writesIn_of_mid hmid8
  have kb8 : ∀ {o : Nat} {bs : List UInt8}, 8 ≤ o → o + bs.length ≤ 432 →
      NativeRustcVm.BytesAt st7.data.dmem (off (fa m0) o) bs →
      NativeRustcVm.BytesAt st8.data.dmem (off (fa m0) o) bs := fun h1 h2 hb ↦
    keep_frame hwf8 hm8 hin8 (by omega) (miss_of_writesF hws8 h1 (.inr (by omega))) hb
  have hat8 := hf8.at h (fun q hq ↦ OT_OA q hq)
  have e8di : reg st8.data .rdi = off (fa m0) 128 := (hm8.regs .rdi _ hrdi8).trans (eval_ptr0 128)
  have e8si : reg st8.data .rsi = BitVec.ofNat 64 16 := hm8.regs .rsi _ hrsi8
  have e8dx : reg st8.data .rdx = wAt m0 :=
    (hm8.regs .rdx _ hrdx8).trans ((hm7.regs .r14 _ (KeepsB.reg hk7 (by simp [six]))).trans hf2.r14)
  have e8cx : reg st8.data .rcx = BitVec.ofNat 64 16 := hm8.regs .rcx _ hrcx8
  -- the weights, unchanged
  have hwAt0 := NativeRustcVm.ewsAt_of_mapped (d := m0.dmem) hw.1.1
  have hwAt : NativeRustcVm.EWsAt st8.data.dmem (wAt m0) (NativeRustcVm.ewsOf m0.dmem (wAt m0) 16) :=
    NativeRustcVm.BytesAt.of_sameOutside hwAt0 hf8.same fun i hi hq ↦ by
      rw [NativeRustcVm.length_ewsBytes, NativeRustcVm.length_ewsOf] at hi
      have hin : NativeRustcVm.InRange (wAt m0) (16 * 16) (off (wAt m0) i) :=
        inRange_off_self hi (by have := hw.1.2; unfold NativeRustcX64.NoWrap at this; omega)
      rcases hq with hq | hq
      · exact not_inRange_of_apart (pre_parts h).2.2.2.2.2.2.2.2.2.2.2.1 hw.1.2 c.fp.1.2 hin hq
      · exact not_inRange_of_apart hw.2 hw.1.2 c.noWrap_stack hin (inRange_mono hq (by omega))
  have hwsl : slice st8.data (wAt m0) (BitVec.ofNat 64 16) = wts m0 := by
    unfold slice
    have := NativeRustcVm.ewsOf_of_ewsAt hwAt
    rw [NativeRustcVm.length_ewsOf] at this
    rw [show (BitVec.ofNat 64 16).toNat = 16 from rfl, this]
  have hker8 : NativeRustcVm.EWsAt st8.data.dmem (off (fa m0) 128) (eqKernel sp).toList := by
    have hkz : (eqKernel sp).toList.length = 16 := by
      rw [Array.length_toList, NativeRustcVm.size_eqKernel, hsz]; rfl
    have := NativeRustcVm.length_ewsBytes (eqKernel sp).toList
    exact kb8 (by omega) (by omega) (by rw [hd7]; exact hker2)
  have hksl : slice st8.data (off (fa m0) 128) (BitVec.ofNat 64 16) = eqKernel sp := by
    have hkz : (eqKernel sp).toList.length = 16 := by
      rw [Array.length_toList, NativeRustcVm.size_eqKernel, hsz]; rfl
    unfold slice
    rw [show (BitVec.ofNat 64 16).toNat = 16 from rfl, ← hkz, NativeRustcVm.ewsOf_of_ewsAt hker8,
      Array.toArray_toList]
  have o128' := c.outOk_frame hat8 le_dot (o := 128) (n := 256) (by omega) (by omega)
  refine call_then hpc8 hdot ?pre8 fun st3 hpc3 hrsp3 hpost3 ↦ ?_
  case pre8 =>
    unfold DotPre SliceOk
    rw [e8di, e8si, e8dx, e8cx]
    exact ⟨c.stackOk hat8 le_dot, ⟨⟨o128'.1, o128'.2.1⟩, o128'.2.2.2.2.1⟩,
      ⟨⟨Mapped.keeps hw.1.1 hf8.frame.kept, hw.1.2⟩, c.apart hat8 le_dot hw.2⟩⟩
  obtain ⟨hdotv, hch3, hsv3⟩ := hpost3
  rw [e8di, e8si, e8dx, e8cx, hksl, hwsl] at hdotv
  have hch3' : NativeRustcVm.SameOutside st8.data.dmem st3.data.dmem (fun q ↦
      NativeRustcVm.InRange 0 0 q ∨
        NativeRustcVm.InRange (stackBelow st8.data dotStack) dotStack q) := hch3
  have hf3 : BF m0 (OT m0) 8 st3.data :=
    hf8.call h (fun q hq ↦ OT_OA q hq) le_dot hsv3 hrsp3 (R := NativeRustcVm.InRange 0 0)
      (fun q hq ↦ absurd hq inRange_zero) hch3'
  have hch3'' : NativeRustcVm.SameOutside st8.data.dmem st3.data.dmem (fun q ↦
      False ∨ NativeRustcVm.InRange (stackBelow st8.data dotStack) dotStack q) :=
    NativeRustcVm.SameOutside.mono hch3' fun q hq ↦ hq.imp_left inRange_zero
  have kc3 := fun {o : Nat} {bs : List UInt8} (h1 : 8 ≤ o) (h2 : o + bs.length ≤ 432) ↦
    keep_stack_call (bs := bs) h hat8 le_dot hch3'' h1 h2
  have hts3 : TStateAt st3.data.dmem (tAt m0) a s3 :=
    tstate_keep h hch3'' hsv3.2 (fun q hq ↦ .inr (.inr (hq.elim False.elim
      fun hq ↦ (c.inRange_callee hat8 le_dot hq).1)))
      (tstate_keep h hs8 (hm8.kept hwf8) (fun q hq ↦ .inr (.inr (c.inRange_frame hq)))
        (by rw [hd7]; exact hts2))
  have k8_3 : ∀ {o : Nat} {bs : List UInt8}, 8 ≤ o → o + bs.length ≤ 432 →
      NativeRustcVm.BytesAt st2.data.dmem (off (fa m0) o) bs →
      NativeRustcVm.BytesAt st3.data.dmem (off (fa m0) o) bs := fun h1 h2 hb ↦
    kc3 h1 h2 (kb8 h1 h2 (by rw [hd7]; exact hb))
  have r15_3 : reg st3.data .r15 = v.c0.toBitVec :=
    (hsv3.1 .r15 rfl).trans ((hm8.regs .r15 _ (KeepsB.reg hk8 (by simp [six]))).trans
      ((hm7.regs .r15 _ (KeepsB.reg hk7 (by simp [six]))).trans r15_2))
  -- `b9`: times the value.
  have hwf9 := wf_envB h hf3.frame.kept (Host.addrOf (k + NativeRustcVmX64.Vm.BytecodeShare.b9Offset + b9.length)).toBitVec
  refine exec_at (infix_of b9_in_code (by simp [b9]) hp) exit_b9 hwf9 (fun _ _ ↦ rfl)
    (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.BytecodeShare.b8_next)) (match_bodyS hf3 _) fun st9 hm9 hpc9 ↦ ?_
  obtain ⟨hmid9, hrdi9, hrsi9, hrdx9, hrcx9, hk9, hws9⟩ := ok_b9
  obtain ⟨hf9, hs9⟩ := BF.block h hf3 hm9 hmid9 (KeepsB.mono hk9 (by simp [six]))
  have hin9 := writesIn_of_mid hmid9
  have kb9 : ∀ {o : Nat} {bs : List UInt8}, 8 ≤ o → o + bs.length ≤ 432 →
      NativeRustcVm.BytesAt st3.data.dmem (off (fa m0) o) bs →
      NativeRustcVm.BytesAt st9.data.dmem (off (fa m0) o) bs := fun h1 h2 hb ↦
    keep_frame hwf9 hm9 hin9 (by omega) (miss_of_writesF hws9 h1 (.inr (by omega))) hb
  have hat9 := hf9.at h (fun q hq ↦ OT_OA q hq)
  have w24_3 := k8_3 (bs := NativeRustcVm.wordBytes _) (by omega) (by simp [hwB]) w24_2
  have e9 : EW.mul ⟨.ofBitVec (reg st9.data .rdi), .ofBitVec (reg st9.data .rsi)⟩
      ⟨.ofBitVec (reg st9.data .rdx), .ofBitVec (reg st9.data .rcx)⟩ =
      dot (eqKernel sp) (wts m0) * v := by
    rw [show reg st9.data .rdi = _ from hm9.regs .rdi _ hrdi9,
      show reg st9.data .rsi = _ from hm9.regs .rsi _ hrsi9,
      show reg st9.data .rdx = _ from hm9.regs .rdx _ hrdx9,
      show reg st9.data .rcx = _ from hm9.regs .rcx _ hrcx9]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [load_ofMachine (o := 24) rfl w24_3, show st3.data.regs.get64 .r15 = _ from r15_3, ← hdotv]
    rfl
  refine call_then hpc9 hmul (c.stackOk hat9 le_mul) fun st4 hpc4 hrsp4 hpost4 ↦ ?_
  obtain ⟨hm40, hm41, hch4, hsv4⟩ := hpost4
  rw [e9] at hm40 hm41
  have hch4' : NativeRustcVm.SameOutside st9.data.dmem st4.data.dmem (fun q ↦
      False ∨ NativeRustcVm.InRange (stackBelow st9.data ewMulStack) ewMulStack q) :=
    NativeRustcVm.SameOutside.mono hch4 fun _ hq ↦ .inr hq
  have hf4 : BF m0 (OT m0) 8 st4.data :=
    hf9.call h (fun q hq ↦ OT_OA q hq) le_mul hsv4 hrsp4 (R := fun _ ↦ False)
      (fun _ hq ↦ hq.elim) hch4'
  have k3_4 : ∀ {o : Nat} {bs : List UInt8}, 8 ≤ o → o + bs.length ≤ 432 →
      NativeRustcVm.BytesAt st2.data.dmem (off (fa m0) o) bs →
      NativeRustcVm.BytesAt st4.data.dmem (off (fa m0) o) bs := fun h1 h2 hb ↦
    keep_stack_call h hat9 le_mul hch4' h1 h2 (kb9 h1 h2 (k8_3 h1 h2 hb))
  have hts4 : TStateAt st4.data.dmem (tAt m0) a s3 :=
    tstate_keep h hch4' hsv4.2 (fun q hq ↦ .inr (.inr (hq.elim False.elim
      fun hq ↦ (c.inRange_callee hat9 le_mul hq).1)))
      (tstate_keep h hs9 (hm9.kept hwf9) (fun q hq ↦ .inr (.inr (c.inRange_frame hq))) hts3)
  have w104_4 := k3_4 (bs := NativeRustcVm.wordBytes _) (by omega) (by simp [hwB]) w104_2
  have w96_4 := k3_4 (bs := NativeRustcVm.wordBytes _) (by omega) (by simp [hwB]) w96_2
  have w120_4 := k3_4 (bs := NativeRustcVm.wordBytes _) (by omega) (by simp [hwB]) w120_2
  have w112_4 := k3_4 (bs := NativeRustcVm.wordBytes _) (by omega) (by simp [hwB]) w112_2
  have w24_4 := k3_4 (bs := NativeRustcVm.wordBytes _) (by omega) (by simp [hwB]) w24_2
  have hsp4 := k3_4 (by omega) (by rw [hspB]; omega) hsp2
  have r15_4 : reg st4.data .r15 = v.c0.toBitVec :=
    (hsv4.1 .r15 rfl).trans ((hm9.regs .r15 _ (KeepsB.reg hk9 (by simp [six]))).trans r15_3)
  have hl14 : Labels.label NativeRustcVmX64.Vm.BytecodeShare.label_14 = Host.addrOf (k + NativeRustcVmX64.Vm.BytecodeShare.b15Offset) := hp.label NativeRustcVmX64.Vm.BytecodeShare.label_14_at
  -- `b10`, `b11`: the check, limb by limb.
  have hwf10 := wf_envB h hf4.frame.kept 0
  refine exec_at (infix_of b10_in_code (by simp [b10]) hp) exit_b10 hwf10 nofun
    (hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.BytecodeShare.b9_next)) (match_bodyS hf4 0) fun st10 hm10 hpc10 ↦ ?_
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hmid10, hmem10, hk10, hmid11, hmem11, hk11⟩ := ok_test
  obtain ⟨hf10, -⟩ := BF.block h hf4 hm10 hmid10 (KeepsB.mono hk10 (by simp [six]))
  have hd10 : st10.data.dmem = st4.data.dmem := hm10.dmem_eq hwf10 hmem10
  have hc10 : c10.eval (envB m0 st4.data 0) = !decide (cl.c0 = (dot (eqKernel sp) (wts m0) * v).c0) := by
    show (!(CmpOp.apply .eq .W64 ((envB m0 st4.data 0).load 0 104 8) (reg st4.data .rax))) = _
    rw [load_ofMachine (o := 104) rfl w104_4, hm40, eq64]
    simp only [UInt64.toBitVec_inj]
  simp only [PcOk, hc10] at hpc10
  have hP : (cl == dot (eqKernel sp) (wts m0) * v) =
      (decide (cl.c0 = (dot (eqKernel sp) (wts m0) * v).c0) &&
        decide (cl.c1 = (dot (eqKernel sp) (wts m0) * v).c1)) := by
    rw [beq_ew]; rfl
  by_cases h0 : cl.c0 = (dot (eqKernel sp) (wts m0) * v).c0
  swap
  · rw [decide_eq_false h0] at hpc10
    simp only [Bool.not_false, ↓reduceIte] at hpc10
    rw [hl14] at hpc10
    obtain ⟨d10, pc10⟩ := st10
    simp only at hpc10
    subst hpc10
    exact none15 hp h hf10 (fun q hq ↦ OT_OA q hq) (by rw [hres, hP, decide_eq_false h0]; rfl)
  rw [decide_eq_true h0] at hpc10
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc10
  have hwf11 := wf_envB h hf10.frame.kept 0
  refine exec_at (infix_of b11_in_code (by simp [b11]) hp) exit_b11 hwf11 nofun
    (hpc10.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.BytecodeShare.b10_next)) (match_bodyS hf10 0)
    fun st11 hm11 hpc11 ↦ ?_
  obtain ⟨hf11, -⟩ := BF.block h hf10 hm11 hmid11 (KeepsB.mono hk11 (by simp [six]))
  have hd11 : st11.data.dmem = st10.data.dmem := hm11.dmem_eq hwf11 hmem11
  have hc11 : c11.eval (envB m0 st10.data 0) =
      !decide (cl.c1 = (dot (eqKernel sp) (wts m0) * v).c1) := by
    show (!(CmpOp.apply .eq .W64 ((envB m0 st10.data 0).load 0 96 8) (reg st10.data .rdx))) = _
    rw [load_ofMachine (o := 96) rfl (by rw [hd10]; exact w96_4),
      show reg st10.data .rdx = _ from hm10.regs .rdx _ (KeepsB.reg hk10 (by simp)),
      show (Sym.reg Reg64.rdx).eval (envB m0 st4.data 0) = reg st4.data .rdx from rfl, hm41, eq64]
    simp only [UInt64.toBitVec_inj]
  simp only [PcOk, hc11] at hpc11
  by_cases h1 : cl.c1 = (dot (eqKernel sp) (wts m0) * v).c1
  swap
  · rw [decide_eq_false h1] at hpc11
    simp only [Bool.not_false, ↓reduceIte] at hpc11
    rw [hl14] at hpc11
    obtain ⟨d11, pc11⟩ := st11
    simp only at hpc11
    subst hpc11
    exact none15 hp h hf11 (fun q hq ↦ OT_OA q hq)
      (by rw [hres, hP, decide_eq_true h0, decide_eq_false h1]; rfl)
  rw [decide_eq_true h1] at hpc11
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc11
  rw [NativeRustcVmX64.Vm.BytecodeShare.b11_length] at hpc11
  have hok : res s0 m0 = some ((sh, slice m0 (bAt m0) (reg m0 .r8) ++ sp, v), s3) := by
    rw [hres, hP, decide_eq_true h0, decide_eq_true h1]; rfl
  have hdm : st11.data.dmem = st4.data.dmem := hd11.trans hd10
  obtain ⟨d11, pc11⟩ := st11
  simp only at hpc11 hdm hf11
  subst hpc11
  refine copy_spec hp h hf11 ?_ fun st' hcp ↦ finish hp h hcp (by rw [hdm]; exact w120_4)
    (by rw [hdm]; exact w112_4) (by rw [hdm]; exact w24_4) (by rw [hdm]; exact hsp4) hsz
    (by rw [hdm]; exact hts4) hok
  rw [show reg d11 .r15 = _ from hm11.regs .r15 _ (KeepsB.reg hk11 (by simp [six])),
    show (Sym.reg Reg64.r15).eval (envB m0 st10.data 0) = reg st10.data .r15 from rfl,
    show reg st10.data .r15 = _ from hm10.regs .r15 _ (KeepsB.reg hk10 (by simp [six]))]
  exact r15_4

end

end NativeRustcVmX64.Bus.BytecodeShare
