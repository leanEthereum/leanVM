module

public import NativeRustcVmX64.KeccakGkr.FirstClaim.Keep
public import NativeRustcVmX64.Code.Vm.Dot.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EqKernel.Names

/-!
# `first_claim`: the segment's kernel and `last` (x86-64)

`b5` zeroes the segment's kernel at `32` and calls `eq_kernel` on the segment into it, `b6` checks
it succeeded; `b7` calls `dot` on the first 25 lanes and the output lanes, `b8` multiplies the
kernel's entry `1` by it (`EW::mul`): `last` in RAX, RDX (`last`, to `LDone`).
-/

namespace NativeRustcVmX64.KeccakGkr.FirstClaim

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeRustcVmX64.Vm.FirstClaim
open NativeRustcVm (Region)
open NativeRustcVm.Transcript (off off_zero off_off toNat_off inRange_iff' Mapped.keeps
  bytesAt_congr inRange_off_self Touch)
open NativeVm.Math.Keccak (bitW)

@[expose] public section

/-- `last`: the segment kernel's last entry times the dot product of the first 25 lanes with the
output lanes. -/
def lastOf (segment lanePoint output : Array EW) : EW :=
  (eqKernel segment).getD (keccakSegments - 1) 0 * dot ((eqKernel lanePoint).extract 0 25) output

/-- **`last` computed**: in RAX, RDX; `inst`'s address and length still in the frame. -/
structure LDone (m0 : MachineData) (segment lanePoint output : Array EW) (st : MachineData) :
    Prop where
  body : Body m0 st
  il : IL m0 st.dmem
  w : ElemsAt st.dmem (wA m0) (bitW (eqKernel lanePoint)) 1600
  rax : reg st .rax = (lastOf segment lanePoint output).c0.toBitVec
  rdx : reg st .rdx = (lastOf segment lanePoint output).c1.toBitVec
  r12 : reg st .r12 = reg m0 .rcx
  r15 : reg st .r15 = outA m0

end

public section

variable {inst segment lanePoint output : Array EW} {m0 : MachineData}

variable [Host] {k : Nat}

/-- **`b5` to `b8`**: the segment's kernel, `last`. -/
theorem last (hp : Placed code k) (hpre : FirstClaimPre inst segment lanePoint output m0)
    (heq : Spec (Labels.label NativeRustcVmX64.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hdot : Spec (Labels.label NativeRustcVmX64.Vm.Dot.entryLabel) DotPre DotPost) {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b5Offset)) (hI : WDone m0 lanePoint st.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b9Offset) ∧
      LDone m0 segment lanePoint output s'.data) st := by
  have h := preOk hpre
  have hn := nums h
  have hr1 := hn.r1
  have hr2 := hn.r2
  have hfb := fbA_toNat h
  have hfmap := frame_mapped h.st (F := 1376) (by rw [stack_eq]; decide)
  -- `b5`: the segment's kernel zeroed, `call eq_kernel`.
  have hwf := wf_body h hI.body.frame.kept (d := st.data) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b5Offset + b5.length)).toBitVec)
  refine exec_at (infix_of b5_in_code (by simp [b5]) hp) exit_b5 hwf (fun _ _ ↦ rfl) hpc
    (match_callS hI.body.frame) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hwi1, hlo1, hrdi, hrsi, hrdx, hrcx, hr12, hat1⟩ := ok_b5
  have hf1 : Frame m0 1376 slots 0 st1.data := Frame.of_block hI.body.frame hwf hm1 hmid1 slots_le'
  have hs1 := sameOutside_touch hwf hm1 (r := 0) rfl (by decide) (within_spec hwi1)
  have hs1W := sameOutside_W hwf hm1 (r := 0) rfl (W := fun j ↦ j < 8 ∨ (32 ≤ j ∧ j < 64))
    (fun w hw ↦ by
      obtain ⟨hr, -, hhi⟩ := within_spec hwi1 w hw
      have := hlo1 w hw
      exact ⟨hr, by omega, fun j h1 h2 ↦ by omega⟩)
  have hsp1 : rspOf st1.data = fbA m0 := by rw [hf1.sp, off_zero]
  have hso1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem (Out m0) := fun q hq ↦
    (hs1 q fun ht ↦ hq (touch_out h (fun _ hj ↦ by omega) ht)).trans (hI.body.same q hq)
  have e7 : reg st1.data .rdi = reg m0 .rcx := (hm1.regs .rdi _ hrdi).trans hI.rbx
  have e6 : (reg st1.data .rsi).toNat = 1 := by
    rw [show reg st1.data .rsi = _ from hm1.regs .rsi _ hrsi]; rfl
  have e2 : reg st1.data .rdx = off (fbA m0) 32 := (hm1.regs .rdx _ hrdx).trans (eval_ptr0 32)
  have e1 : (reg st1.data .rcx).toNat = 2 := by
    rw [show reg st1.data .rcx = _ from hm1.regs .rcx _ hrcx]; rfl
  have hsgl : (segment.toList.flatMap NativeRustcVm.ewBytes).length = 16 := by
    rw [ews_len, Array.length_toList, h.segSz]
  have hg := hn.g
  have hsg := hn.sg
  have hseg : NativeRustcVm.EWsAt st1.data.dmem (reg m0 .rcx) segment.toList := by
    have := hn.og; have := hn.wg
    exact keep_in h hso1 (by rw [hsgl]; omega) (by rw [hsgl]; omega) (by rw [hsgl]; omega)
      (by rw [hsgl]; omega) h.segAt
  -- `eq_kernel` on the segment into the kernel.
  have hek : eqKernelStack = 256 := by decide
  have hsb1 : (stackBelow st1.data eqKernelStack).toNat = (rspOf m0).toNat - 1632 := by
    rw [stackBelow_callee hsp1 (by rw [hek]; omega), stackBelow_toNat (by rw [hek]; omega), hek]
  have hf32 : (off (fbA m0) 32).toNat = (rspOf m0).toNat - 1376 + 32 := fb_off h (by decide)
  have hgm : NativeRustcVm.Mapped m0.dmem (reg m0 .rcx) (16 * 1) :=
    rd_mapped h (r := ewsRegion (reg m0 .rcx) 1) (List.mem_cons_of_mem _ List.mem_cons_self)
  have hpre1 : EqKernelPre st1.data := by
    unfold EqKernelPre SliceOk Readable OffStack
    rw [e7, e2, e6, e1]
    refine ⟨stackOk_callee h.st hf1.kept hsp1 (by rw [stack_eq, hek]), by decide,
      ⟨⟨Mapped.keeps hgm hf1.kept, by show _ + _ ≤ _; omega⟩, ?_⟩,
      ⟨⟨Mapped.keeps (mapped_off hfmap (by decide)) hf1.kept, by show _ + _ ≤ _; rw [hf32]; omega⟩,
        ?_⟩, ?_⟩
    · show _ + _ ≤ _ ∨ _ + _ ≤ _
      rw [hsb1, hek]; omega
    · show _ + _ ≤ _ ∨ _ + _ ≤ _
      rw [hf32, hsb1, hek]; omega
    · show _ + _ ≤ _ ∨ _ + _ ≤ _
      rw [hf32]; omega
  refine call_then hpc1 heq hpre1 fun st2 hpc2 hrsp2 ⟨hpost, hch, hsv2⟩ ↦ ?_
  rw [e6, e1] at hpost
  simp only [show 2 ^ 1 ≤ 2 by decide, ite_true] at hpost
  obtain ⟨hr0, -, hker⟩ := hpost
  have hslice : slice st1.data (reg st1.data .rdi) (reg st1.data .rsi) = segment := by
    unfold slice
    rw [e7, e6, ← h.segSz, ← Array.length_toList, NativeRustcVm.ewsOf_of_ewsAt hseg]
  rw [hslice, e2] at hker
  unfold Changes at hch
  rw [e2, e1, hek] at hch
  obtain ⟨hb2, hch2⟩ := call_body h hf1 hso1 hsv2 hrsp2 (s := 256) (by decide) hch
    (frame_D h (o := 32) (n := 16 * 2) (by decide))
  -- `b6`: `eq_kernel`'s result checked.
  have hwf2 := wf_body h hb2.frame.kept (d := st2.data) (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of b6_in_code (by simp [b6]) hp) exit_b6 hwf2 nofun
    (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.FirstClaim.b5_next)) (match_callS hb2.frame) fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid3, hmem3, hat3⟩ := ok_test b6 (by simp)
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf2 hmem3
  have hb3 : Body m0 st3.data := hb2.of_mem (Frame.of_block hb2.frame hwf2 hm3 hmid3 slots_le') hd3
  have hc3 : test1.eval (frameEnv m0 st2.data 1376 [(argA m0, 24)] (fun _ ↦ 0) 0) = false := by
    show CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (reg st2.data .rax) (BitVec.ofNat 64 1))
      (BitVec.ofNat 64 0) = false
    rw [hr0]; decide
  simp only [PcOk, hc3, Bool.false_eq_true, ite_false] at hpc3
  -- `b7`: `dot` of the first 25 lanes and the output lanes.
  have hwf3 := wf_body h hb3.frame.kept (d := st3.data) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b7Offset + b7.length)).toBitVec)
  refine exec_at (infix_of b7_in_code (by simp [b7]) hp) exit_b7 hwf3 (fun _ _ ↦ rfl)
    (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.FirstClaim.b6_next)) (match_callS hb3.frame) fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hmid4, hwi4, hrdi4, hrsi4, hrdx4, hrcx4, hrbp4, hr144, hat4⟩ := ok_b7
  have hf4 : Frame m0 1376 slots 0 st4.data := Frame.of_block hb3.frame hwf3 hm4 hmid4 slots_le'
  have hs4 := sameOutside_touch hwf3 hm4 (r := 0) rfl (by decide) (within_spec hwi4)
  have hsp4 : rspOf st4.data = fbA m0 := by rw [hf4.sp, off_zero]
  have hso4 : NativeRustcVm.SameOutside m0.dmem st4.data.dmem (Out m0) := fun q hq ↦
    (hs4 q fun ht ↦ hq (touch_out h (fun _ hj ↦ by omega) ht)).trans (hb3.same q hq)
  -- the kernel's entry `1`
  have hk1 : (eqKernel segment).size = 2 := by
    rw [NativeVm.Math.Keccak.eqKernel_size, h.segSz]; rfl
  have ea := NativeRustcVm.ewAt_iff.mp (ewsAt_getD hker (i := 1) (by rw [hk1]; decide))
  have w48 : NativeRustcVm.WordAt st3.data.dmem (off (fbA m0) 48)
      ((eqKernel segment).getD 1 0).c0 := by
    rw [hd3, show (48 : Nat) = 32 + 16 * 1 from rfl, ← off_off]; exact ea.1
  have w56 : NativeRustcVm.WordAt st3.data.dmem (off (fbA m0) 56)
      ((eqKernel segment).getD 1 0).c1 := by
    rw [hd3, show (56 : Nat) = 32 + 16 * 1 + 8 from rfl, ← NativeRustcVm.Transcript.off_add,
      ← off_off]
    exact ea.2
  have v48 : reg st4.data .rbp = ((eqKernel segment).getD 1 0).c0.toBitVec := by
    rw [show reg st4.data .rbp = _ from hm4.regs .rbp _ hrbp4]
    show Env.load _ 0 48 8 = _
    exact load_of_wordAt w48
  have v56 : reg st4.data .r14 = ((eqKernel segment).getD 1 0).c1.toBitVec := by
    rw [show reg st4.data .r14 = _ from hm4.regs .r14 _ hr144]
    show Env.load _ 0 56 8 = _
    exact load_of_wordAt w56
  -- the lanes, the output lanes
  have hlsz : (eqKernel lanePoint).size = 32 := by
    rw [NativeVm.Math.Keccak.eqKernel_size, h.lpSz]; rfl
  have hlanes3 : NativeRustcVm.EWsAt st3.data.dmem (off (fbA m0) 328)
      (eqKernel lanePoint).toList := by
    rw [hd3]
    exact keep_fcall h hch2 (by rw [lanes_len h]; omega) (by decide)
      (by rw [lanes_len h]; omega)
      (keep_W h hs1W (by rw [lanes_len h]; omega) (fun i _ hW ↦ by omega)
        hI.lanes)
  have hlanes4 : NativeRustcVm.EWsAt st4.data.dmem (off (fbA m0) 328)
      (eqKernel lanePoint).toList :=
    keep_touch h hs4 (by rw [lanes_len h]; omega) (by rw [lanes_len h]; omega) hlanes3
  have hopl : (output.toList.flatMap NativeRustcVm.ewBytes).length = 400 := by
    rw [ews_len, Array.length_toList, h.opSz]
  have hu := hn.u
  have hsu := hn.su
  have hout4 : NativeRustcVm.EWsAt st4.data.dmem (reg m0 .r9) output.toList := by
    have := hn.ou; have := hn.wu
    exact keep_in h hso4 (by rw [hopl]; omega) (by rw [hopl]; omega) (by rw [hopl]; omega)
      (by rw [hopl]; omega) h.opAt
  have f7 : reg st4.data .rdi = off (fbA m0) 328 := (hm4.regs .rdi _ hrdi4).trans (eval_ptr0 328)
  have f6 : (reg st4.data .rsi).toNat = 25 := by
    rw [show reg st4.data .rsi = _ from hm4.regs .rsi _ hrsi4]; rfl
  have f1 : (reg st4.data .rcx).toNat = 25 := by
    rw [show reg st4.data .rcx = _ from hm4.regs .rcx _ hrcx4]; rfl
  have a1 : ∀ r ∈ [Reg64.rbx, .r13, .r15], reg st1.data r = reg st.data r :=
    fun r hr ↦ atoms_eq hm1 hat1 hr
  have a3 : ∀ r ∈ [Reg64.rdx, .rbx, .rbp, .r12, .r13, .r14, .r15],
      reg st3.data r = reg st2.data r := fun r hr ↦ atoms_eq hm3 hat3 hr
  have f2 : reg st4.data .rdx = reg m0 .r9 :=
    (hm4.regs .rdx _ hrdx4).trans ((a3 .r13 (by simp)).trans
      ((hsv2.1 .r13 rfl).trans ((a1 .r13 (by simp)).trans hI.r13)))
  have hdt : dotStack = 208 := by decide
  have hsb4 : (stackBelow st4.data dotStack).toNat = (rspOf m0).toNat - 1584 := by
    rw [stackBelow_callee hsp4 (by rw [hdt]; omega), stackBelow_toNat (by rw [hdt]; omega), hdt]
  have hf328 : (off (fbA m0) 328).toNat = (rspOf m0).toNat - 1376 + 328 := fb_off h (by decide)
  have hum : NativeRustcVm.Mapped m0.dmem (reg m0 .r9) (16 * 25) :=
    rd_mapped h (r := ewsRegion (reg m0 .r9) 25) (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have hpre4 : DotPre st4.data := by
    unfold DotPre SliceOk Readable OffStack
    rw [f7, f6, f2, f1]
    refine ⟨stackOk_callee h.st hf4.kept hsp4 (by rw [stack_eq]; decide),
      ⟨⟨Mapped.keeps (mapped_off hfmap (by decide)) hf4.kept, by show _ + _ ≤ _; rw [hf328]; omega⟩,
        ?_⟩, ⟨⟨Mapped.keeps hum hf4.kept, by show _ + _ ≤ _; omega⟩, ?_⟩⟩
    · show _ + _ ≤ _ ∨ _ + _ ≤ _
      rw [hf328, hsb4, hdt]; omega
    · show _ + _ ≤ _ ∨ _ + _ ≤ _
      rw [hsb4, hdt]; omega
  refine call_then hpc4 hdot hpre4 fun st5 hpc5 hrsp5 ⟨hdv, hch5, hsv5⟩ ↦ ?_
  have hdotv : ewRet st5.data = dot ((eqKernel lanePoint).extract 0 25) output := by
    rw [hdv]
    unfold slice
    rw [f7, f6, f2, f1]
    have x1 := NativeRustcVm.ewsOf_of_ewsAt (hlanes4.take 25)
    rw [List.length_take, Array.length_toList, hlsz, show min 25 32 = 25 from rfl] at x1
    have x2 := NativeRustcVm.ewsOf_of_ewsAt hout4
    rw [Array.length_toList, h.opSz] at x2
    rw [x1, x2, extract_zero, Array.toArray_toList]
  unfold Changes at hch5
  obtain ⟨hb5, hc5⟩ := call_body h hf4 hso4 hsv5 hrsp5 (s := dotStack) (by decide)
    (D := fun _ ↦ False) (NativeRustcVm.Transcript.SameOutside.mono hch5 fun q hq ↦
      hq.elim (fun h0 ↦ absurd h0 (Nat.not_lt_zero _)) Or.inr)
    (fun _ hq ↦ hq.elim)
  -- `b8`: `EW::mul` of the kernel's entry `1` and the dot product.
  have hwf5 := wf_body h hb5.frame.kept (d := st5.data) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b8Offset + b8.length)).toBitVec)
  refine exec_at (infix_of b8_in_code (by simp [b8]) hp) exit_b8 hwf5 (fun _ _ ↦ rfl)
    (hpc5.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.FirstClaim.b7_next)) (match_callS hb5.frame) fun st6 hm6 hpc6 ↦ ?_
  obtain ⟨hmid6, hwi6, hrdi6, hrsi6, hrdx6, hrcx6, hat6⟩ := ok_b8
  have hf6 : Frame m0 1376 slots 0 st6.data := Frame.of_block hb5.frame hwf5 hm6 hmid6 slots_le'
  have hs6 := sameOutside_touch hwf5 hm6 (r := 0) rfl (by decide) (within_spec hwi6)
  have hsp6 : rspOf st6.data = fbA m0 := by rw [hf6.sp, off_zero]
  have hso6 : NativeRustcVm.SameOutside m0.dmem st6.data.dmem (Out m0) := fun q hq ↦
    (hs6 q fun ht ↦ hq (touch_out h (fun _ hj ↦ by omega) ht)).trans (hb5.same q hq)
  have g7 : reg st6.data .rdi = ((eqKernel segment).getD 1 0).c0.toBitVec :=
    (hm6.regs .rdi _ hrdi6).trans ((hsv5.1 .rbp rfl).trans v48)
  have g6 : reg st6.data .rsi = ((eqKernel segment).getD 1 0).c1.toBitVec :=
    (hm6.regs .rsi _ hrsi6).trans ((hsv5.1 .r14 rfl).trans v56)
  have g2 : reg st6.data .rdx = reg st5.data .rax := hm6.regs .rdx _ hrdx6
  have g1 : reg st6.data .rcx = reg st5.data .rdx := hm6.regs .rcx _ hrcx6
  have hprod : EW.mul ⟨.ofBitVec (reg st6.data .rdi), .ofBitVec (reg st6.data .rsi)⟩
      ⟨.ofBitVec (reg st6.data .rdx), .ofBitVec (reg st6.data .rcx)⟩ =
      lastOf segment lanePoint output := by
    rw [g7, g6, g2, g1, UInt64.ofBitVec_toBitVec, UInt64.ofBitVec_toBitVec]
    show EW.mul _ (ewRet st5.data) = _
    rw [hdotv, lastOf, show keccakSegments - 1 = 1 by decide]
    rfl
  have hpre6 : EWMulPre st6.data := stackOk_callee h.st hf6.kept hsp6 (by rw [stack_eq]; decide)
  refine call_then hpc6 hmul hpre6 fun st7 hpc7 hrsp7 ⟨hrax, hrdx7, hch7, hsv7⟩ ↦ ?_
  rw [hprod] at hrax hrdx7
  obtain ⟨hb7, hc7⟩ := call_body h hf6 hso6 hsv7 hrsp7 (s := ewMulStack) (by decide)
    (D := fun _ ↦ False) (NativeRustcVm.Transcript.SameOutside.mono hch7 fun _ hq ↦ Or.inr hq)
    (fun _ hq ↦ hq.elim)
  -- `inst`'s address and length kept
  have kf : ∀ {o : Nat} {bs : List UInt8}, 16 ≤ o → o + bs.length ≤ 32 →
      NativeRustcVm.BytesAt st.data.dmem (off (fbA m0) o) bs →
      NativeRustcVm.BytesAt st7.data.dmem (off (fbA m0) o) bs := fun h16 hle hb ↦
    keep_call h hc7 (by omega) (keep_touch h hs6 (by omega) (by omega)
      (keep_call h hc5 (by omega) (keep_touch h hs4 (by omega) (by omega) (by
        show NativeRustcVm.BytesAt st3.data.dmem _ _
        rw [hd3]
        exact keep_fcall h hch2 (by omega) (by decide) (by omega)
          (keep_W h hs1W (by omega) (fun i hi hW ↦ by omega) hb)))))
  -- the bit weights kept
  have hw7 : ElemsAt st7.data.dmem (wA m0) (bitW (eqKernel lanePoint)) 1600 := by
    have tk : ∀ {W : Nat → Prop}, (∀ j, W j → j < 1376) →
        ∀ q, Touch (fbA m0) (1376 + 8) W q → ¬ NativeRustcVm.InRange (wA m0) 25600 q :=
      fun hW ↦ stk_w h fun _ hq ↦ touch_stk h hW hq
    have ck : ∀ q, (False ∨ Low m0 q) → ¬ NativeRustcVm.InRange (wA m0) 25600 q :=
      stk_w h fun _ hq ↦ hq.elim (fun hf ↦ hf.elim) (low_stk h)
    have w1 := w_keep h hs1 (tk fun _ hj ↦ by omega) hI.w
    have w2 := w_keep h hch2 (stk_w h fun _ hq ↦ hq.elim (fd_stk h (by decide)) (low_stk h)) w1
    have w4 := w_keep h hs4 (tk fun _ hj ↦ by omega) (by
      show ElemsAt st3.data.dmem _ _ _; rw [hd3]; exact w2)
    exact w_keep h hc7 ck (w_keep h hs6 (tk fun _ hj ↦ by omega) (w_keep h hc5 ck w4))
  refine .done _ ⟨hpc7.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.FirstClaim.b8_next), hb7,
    ⟨kf (by decide) (by simp [NativeRustcVm.length_wordBytes]) hI.il.ip,
      kf (by decide) (by simp [NativeRustcVm.length_wordBytes]) hI.il.il⟩, hw7, hrax, hrdx7,
    ?_, ?_⟩
  · have a4 : ∀ r ∈ [Reg64.rbx, .r12, .r15], reg st4.data r = reg st3.data r :=
      fun r hr ↦ atoms_eq hm4 hat4 hr
    have a6 : ∀ r ∈ [Reg64.rbx, .r12, .r15], reg st6.data r = reg st5.data r :=
      fun r hr ↦ atoms_eq hm6 hat6 hr
    have e12 : reg st1.data .r12 = reg m0 .rcx := (hm1.regs .r12 _ hr12).trans hI.rbx
    exact (hsv7.1 .r12 rfl).trans ((a6 .r12 (by simp)).trans ((hsv5.1 .r12 rfl).trans
      ((a4 .r12 (by simp)).trans ((a3 .r12 (by simp)).trans ((hsv2.1 .r12 rfl).trans e12)))))
  · have a4 : ∀ r ∈ [Reg64.rbx, .r12, .r15], reg st4.data r = reg st3.data r :=
      fun r hr ↦ atoms_eq hm4 hat4 hr
    have a6 : ∀ r ∈ [Reg64.rbx, .r12, .r15], reg st6.data r = reg st5.data r :=
      fun r hr ↦ atoms_eq hm6 hat6 hr
    exact (hsv7.1 .r15 rfl).trans ((a6 .r15 (by simp)).trans ((hsv5.1 .r15 rfl).trans
      ((a4 .r15 (by simp)).trans ((a3 .r15 (by simp)).trans
        ((hsv2.1 .r15 rfl).trans ((a1 .r15 (by simp)).trans hI.r15))))))

end

end NativeRustcVmX64.KeccakGkr.FirstClaim
