module

public import NativeRustcVmX64.KeccakGkr.FirstClaim.Mu
public import NativeRustcVmX64.Code.Vm.BufEW30Extend.Names

/-!
# `first_claim`: the claim's point (x86-64)

`b11` stores the instance weights' count at `64`, empties the point (a `Buf<EW, 30>` at `840`)
and calls `Buf::extend` with `inst`'s coordinates from `4` on (none if `|inst| < 4`); `b12` checks
it succeeded; `b13` extends the point with the segment, `b14` checks it succeeded (`tail`, to
`PDone`).
-/

namespace NativeRustcVmX64.KeccakGkr.FirstClaim

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.FirstClaim
open NativeRustcVm (Region)
open NativeRustcVm.Transcript (off off_zero off_off toNat_off inRange_iff' Mapped.keeps
  bytesAt_congr inRange_off_self Touch)
open NativeVm.Math.Keccak (bitW)

@[expose] public section

/-- The claim's point: `inst`'s coordinates from `4` on, then the segment. -/
def pointOf (inst segment : Array EW) : Array EW := inst.extract 4 inst.size ++ segment

/-- **The claim in the frame**: `last` in R13, RBP, the instance weights (a `Buf<EW, 16>` at
`64`) and the point (a `Buf<EW, 30>` at `840`). -/
structure PDone (m0 : MachineData) (inst segment lanePoint output : Array EW)
    (st : MachineData) : Prop where
  body : Body m0 st
  w : ElemsAt st.dmem (wA m0) (bitW (eqKernel lanePoint)) 1600
  mu : NativeRustcVm.BufEWAt st.dmem (off (fbA m0) 64) 16 (eqKernel (inst.extract 0 4)).toList
  pt : NativeRustcVm.BufEWAt st.dmem (off (fbA m0) 840) 30 (pointOf inst segment).toList
  r13 : reg st .r13 = (lastOf segment lanePoint output).c0.toBitVec
  rbp : reg st .rbp = (lastOf segment lanePoint output).c1.toBitVec
  r15 : reg st .r15 = outA m0

end

public section

/-- `cmpq $4, %rbx; cmovae`: `inst`'s coordinates from `4` on, or `8` (a dangling pointer). -/
theorem rsi_eval (x p : BitVec 64) :
    (if (!CmpOp.apply .ult .W64 x (BitVec.ofNat 64 4)) = true then
      BinOp.apply .add .W64 (BitVec.ofNat 64 64) p else BitVec.ofNat 64 8) =
      if x.toNat < 4 then BitVec.ofNat 64 8 else p + BitVec.ofNat 64 (16 * 4) := by
  have e : CmpOp.apply .ult .W64 x (BitVec.ofNat 64 4) = decide (x.toNat < 4) := by
    simp [CmpOp.apply, BitVec.ult]
  rw [e]
  by_cases hc : x.toNat < 4
  · simp [hc]
  · simp only [hc, decide_false, Bool.not_false, ite_true, ite_false, BinOp.apply, low_W64,
      ext_W64]
    exact BitVec.add_comm _ _

/-- `subq $4, %rbx; cmovae`: their number. -/
theorem rdx_eval (x : BitVec 64) :
    (if (!CmpOp.apply .ult .W64 x (BitVec.ofNat 64 4)) = true then
      BinOp.apply .sub .W64 x (BitVec.ofNat 64 4) else BitVec.ofNat 64 0).toNat = x.toNat - 4 := by
  have e : CmpOp.apply .ult .W64 x (BitVec.ofNat 64 4) = decide (x.toNat < 4) := by
    simp [CmpOp.apply, BitVec.ult]
  rw [e]
  by_cases hc : x.toNat < 4
  · simp [hc]; omega
  · simp only [hc, decide_false, Bool.not_false, ite_true, BinOp.apply, low_W64, ext_W64]
    rw [BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    omega

theorem ofBitVec_eq {x : BitVec 64} {n : Nat} (h : x.toNat = n) :
    UInt64.ofBitVec x = n.toUInt64 := by
  rw [← h]; exact UInt64.ofNat_toNat.symm

variable {inst segment lanePoint output : Array EW} {m0 : MachineData}

/-- The segment's element kept from the entry. -/
theorem seg_keep (h : PreOk inst segment lanePoint output m0) {d : DataMem}
    (hs : NativeRustcVm.SameOutside m0.dmem d (Out m0)) :
    NativeRustcVm.EWsAt d (reg m0 .rcx) segment.toList := by
  have hn := nums h
  have := hn.g; have := hn.og; have := hn.wg; have := hn.sg; have := hn.r1
  have hl : (segment.toList.flatMap NativeRustcVm.ewBytes).length = 16 := by
    rw [ews_len, Array.length_toList, h.segSz]
  exact keep_in h hs (by rw [hl]; omega) (by rw [hl]; omega) (by rw [hl]; omega)
    (by rw [hl]; omega) h.segAt

variable [Host] {k : Nat}

/-- **`b11` to `b14`**: the claim's point. -/
theorem tail (hp : Placed code k) (hpre : FirstClaimPre inst segment lanePoint output m0)
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW30Extend.entryLabel) (BufEWExtendPre 30) (BufEWExtendPost 30))
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b11Offset))
    (hI : MDone m0 inst segment lanePoint output st.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b15Offset) ∧
      PDone m0 inst segment lanePoint output s'.data) st := by
  have h := preOk hpre
  have hn := nums h
  have hr1 := hn.r1
  have hr2 := hn.r2
  have hfb := fbA_toNat h
  have hn30 := h.le30
  have hfmap := frame_mapped h.st (F := 1376) (by rw [stack_eq]; decide)
  have hmus : (eqKernel (inst.extract 0 4)).size ≤ 16 := by
    rw [mu_size]; exact pow_min4 _
  -- `b11`: the count stored, the point emptied, `call extend`.
  have hwf := wf_body h hI.body.frame.kept (d := st.data) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b11Offset + b11.length)).toBitVec)
  refine exec_at (infix_of b11_in_code (by simp [b11]) hp) exit_b11 hwf (fun _ _ ↦ rfl) hpc
    (match_callS hI.body.frame) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hwi1, hlo1, hz1, hw64, hrdi, hrsi, hrdx, hat1⟩ := ok_b11
  have hf1 : Frame m0 1376 slots 0 st1.data := Frame.of_block hI.body.frame hwf hm1 hmid1 slots_le'
  have hs1 := sameOutside_touch hwf hm1 (r := 0) rfl (by decide) (within_spec hwi1)
  have hs1W := sameOutside_W hwf hm1 (r := 0) rfl
    (W := fun j ↦ j < 8 ∨ (64 ≤ j ∧ j < 72) ∨ (840 ≤ j ∧ j < 1328))
    (fun w hw ↦ by
      obtain ⟨hr, -, hhi⟩ := within_spec hwi1 w hw
      have := hlo1 w hw
      exact ⟨hr, by omega, fun j h1 h2 ↦ by omega⟩)
  have hsp1 : rspOf st1.data = fbA m0 := by rw [hf1.sp, off_zero]
  have hso1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem (Out m0) := fun q hq ↦
    (hs1 q fun ht ↦ hq (touch_out h (fun _ hj ↦ by omega) ht)).trans (hI.body.same q hq)
  -- the count, the empty point, `mu`'s items kept
  have hcnt : NativeRustcVm.WordAt st1.data.dmem (off (fbA m0) 64)
      (eqKernel (inst.extract 0 4)).toList.length.toUInt64 := by
    have := wordAt_write hm1 (r := 0) (o := 64) (v := .reg .rdx) rfl (by decide) hw64
    rwa [ofBitVec_eq (n := (eqKernel (inst.extract 0 4)).toList.length)
      (by rw [Array.length_toList]; exact hI.rdx)] at this
  have hz : NativeRustcVm.WordAt st1.data.dmem (off (fbA m0) 840) 0 :=
    wordAt_write hm1 (r := 0) (o := 840) (v := .lit 0) rfl (by decide) fun i hi ↦ by
      have := zeros_spec hz1 (q := 0) (by decide) i hi
      rwa [show 840 + 8 * 0 + i = 840 + i by omega] at this
  have hmul :
      ((eqKernel (inst.extract 0 4)).toList.flatMap NativeRustcVm.ewBytes).length ≤ 256 := by
    rw [ews_len, Array.length_toList]; omega
  have hmu1 : NativeRustcVm.EWsAt st1.data.dmem (off (fbA m0) 72)
      (eqKernel (inst.extract 0 4)).toList :=
    keep_W h hs1W (by omega) (fun i hi hW ↦ by omega) hI.mu
  -- the arguments of `extend`
  have e7 : reg st1.data .rdi = off (fbA m0) 840 := (hm1.regs .rdi _ hrdi).trans (eval_ptr0 840)
  have hsz : reg m0 .rdx = BitVec.ofNat 64 inst.size := by
    apply BitVec.eq_of_toNat_eq; rw [← h.sz, BitVec.toNat_ofNat]; omega
  have e6 : reg st1.data .rsi =
      if inst.size < 4 then BitVec.ofNat 64 8 else reg m0 .rsi + BitVec.ofNat 64 (16 * 4) := by
    rw [show reg st1.data .rsi = _ from hm1.regs .rsi _ hrsi]
    show (if (!CmpOp.apply .ult .W64 (reg st.data .rbx) (BitVec.ofNat 64 4)) = true then
      BinOp.apply .add .W64 (BitVec.ofNat 64 64) (reg st.data .r14) else BitVec.ofNat 64 8) = _
    rw [rsi_eval, hI.rbx, hI.r14, h.sz]
  have e2 : (reg st1.data .rdx).toNat = inst.size - 4 := by
    rw [show reg st1.data .rdx = _ from hm1.regs .rdx _ hrdx]
    show (if (!CmpOp.apply .ult .W64 (reg st.data .rbx) (BitVec.ofNat 64 4)) = true then
      BinOp.apply .sub .W64 (reg st.data .rbx) (BitVec.ofNat 64 4) else BitVec.ofNat 64 0).toNat = _
    rw [rdx_eval, hI.rbx, h.sz]
  have hinst := inst_keep h hso1
  have hi := hn.i
  have hsi := hn.si
  have hbe : bufEWExtendStack = 8 := rfl
  have hsb1 : (stackBelow st1.data bufEWExtendStack).toNat = (rspOf m0).toNat - 1384 := by
    rw [sb_call h hsp1 (by decide), hbe]; omega
  have hf840 : (off (fbA m0) 840).toNat = (rspOf m0).toNat - 1376 + 840 := fb_off h (by decide)
  have him : NativeRustcVm.Mapped m0.dmem (reg m0 .rsi) (16 * inst.size) :=
    rd_mapped h (r := ewsRegion (reg m0 .rsi) inst.size) List.mem_cons_self
  have hip : inst.size < 4 ∨ (4 ≤ inst.size ∧
      ((reg m0 .rsi + BitVec.ofNat 64 (16 * 4)).toNat = (reg m0 .rsi).toNat + 64 ∨
        ((reg m0 .rsi + BitVec.ofNat 64 (16 * 4)).toNat = 0 ∧ inst.size = 4))) := by
    by_cases hc : inst.size < 4
    · exact Or.inl hc
    · refine Or.inr ⟨by omega, ?_⟩
      by_cases hw : (reg m0 .rsi).toNat + 64 < 2 ^ 64
      · exact Or.inl (toNat_off hw)
      · refine Or.inr ⟨?_, by omega⟩
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
  have hX :
      NativeRustcVm.Mapped st1.data.dmem (reg st1.data .rsi) (16 * (reg st1.data .rdx).toNat) ∧
      NativeRustcVm.NoWrap (reg st1.data .rsi) (16 * (reg st1.data .rdx).toNat) ∧
      NativeRustcVm.Apart (off (fbA m0) 840) (8 + 16 * 30) (reg st1.data .rsi)
        (16 * (reg st1.data .rdx).toNat) ∧
      NativeRustcVm.Apart (reg st1.data .rsi) (16 * (reg st1.data .rdx).toNat)
        (stackBelow st1.data bufEWExtendStack) (bufEWExtendStack + 8) ∧
      slice st1.data (reg st1.data .rsi) (reg st1.data .rdx) = inst.extract 4 inst.size := by
    unfold slice
    rw [e6, e2, extract_from]
    rcases hip with hc | ⟨hc, hc'⟩
    · rw [ite_eq_left hc, show inst.size - 4 = 0 by omega, Nat.mul_zero,
        List.drop_eq_nil_of_le (by rw [Array.length_toList]; omega)]
      refine ⟨fun i hi ↦ absurd hi (Nat.not_lt_zero _), by unfold NativeRustcVm.NoWrap; decide,
        ?_, ?_, rfl⟩
      · show _ ∨ _; right; rw [hf840, BitVec.toNat_ofNat]; omega
      · show _ ∨ _; left; rw [hsb1, BitVec.toNat_ofNat]; omega
    · rw [ite_eq_right (by omega)]
      have hd := NativeRustcVm.ewsOf_of_ewsAt (hinst.drop 4)
      rw [List.length_drop, Array.length_toList] at hd
      refine ⟨Mapped.keeps (mapped_off him (o := 16 * 4) (by omega)) hf1.kept, ?_, ?_, ?_,
        by rw [hd]⟩
      · unfold NativeRustcVm.NoWrap; rcases hc' with x | ⟨x, y⟩ <;> rw [x] <;> omega
      · show _ ∨ _; rw [hf840]; rcases hc' with x | ⟨x, y⟩ <;> rw [x] <;> omega
      · show _ ∨ _; rw [hsb1, hbe]; rcases hc' with x | ⟨x, y⟩ <;> rw [x] <;> omega
  have hpre1 : BufEWExtendPre 30 st1.data := by
    unfold BufEWExtendPre Readable OffStack
    rw [e7, NativeRustcVm.wordOf_of_wordAt hz]
    refine ⟨stackOk_callee h.st hf1.kept hsp1 (by rw [stack_eq, hbe]; decide), by decide,
      ⟨Mapped.keeps (mapped_off hfmap (by decide)) hf1.kept, by
        show _ + _ ≤ _; rw [hf840]; omega⟩, ⟨hX.1, hX.2.1⟩, hX.2.2.1, ?_, hX.2.2.2.1⟩
    show _ + _ ≤ _ ∨ _ + _ ≤ _
    rw [hf840, hsb1, hbe]; omega
  refine call_then hpc1 hext hpre1 fun st2 hpc2 hrsp2 ⟨hpost, hch, hsv2⟩ ↦ ?_
  rw [e7, NativeRustcVm.wordOf_of_wordAt hz, e2] at hpost
  simp only [UInt64.toNat_zero, Nat.zero_add] at hpost
  rw [ite_eq_left (by omega)] at hpost
  obtain ⟨hr2, hpt⟩ := hpost
  have hbuf0 : NativeRustcVm.bufEWOf st1.data.dmem (off (fbA m0) 840) = [] := by
    unfold NativeRustcVm.bufEWOf
    rw [NativeRustcVm.wordOf_of_wordAt hz]
    rfl
  rw [hbuf0, hX.2.2.2.2, List.nil_append] at hpt
  unfold Changes at hch
  rw [e7, hbe] at hch
  obtain ⟨hb2, hch2⟩ := call_body h hf1 hso1 hsv2 hrsp2 (s := 8) (by decide) hch
    (frame_D h (o := 840) (n := 8 + 16 * 30) (by decide))
  -- `b12`: `extend`'s result checked.
  have hwf2 := wf_body h hb2.frame.kept (d := st2.data) (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of b12_in_code (by simp [b12]) hp) exit_b12 hwf2 nofun
    (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.FirstClaim.b11_next)) (match_callS hb2.frame)
    fun st3 hm3 hpc3 ↦ ?_
  obtain ⟨hmid3, hmem3, hat3⟩ := ok_test b12 (by simp)
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq hwf2 hmem3
  have hb3 : Body m0 st3.data := hb2.of_mem (Frame.of_block hb2.frame hwf2 hm3 hmid3 slots_le') hd3
  have hc3 : testA.eval (frameEnv m0 st2.data 1376 [(argA m0, 24)] (fun _ ↦ 0) 0) = false := by
    show CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (reg st2.data .rax) (reg st2.data .rax))
      (BitVec.ofNat 64 0) = false
    rw [al_test]
    unfold boolRet at hr2
    rw [hr2]; decide
  simp only [PcOk, hc3, Bool.false_eq_true, ite_false] at hpc3
  have a1 : ∀ r ∈ [Reg64.rbp, .r12, .r13, .r15], reg st1.data r = reg st.data r :=
    fun r hr ↦ atoms_eq hm1 hat1 hr
  have a3 : ∀ r ∈ [Reg64.rdx, .rbx, .rbp, .r12, .r13, .r14, .r15],
      reg st3.data r = reg st2.data r := fun r hr ↦ atoms_eq hm3 hat3 hr
  -- `b13`: `extend` with the segment.
  have hwf3 := wf_body h hb3.frame.kept (d := st3.data) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.FirstClaim.b13Offset + b13.length)).toBitVec)
  refine exec_at (infix_of b13_in_code (by simp [b13]) hp) exit_b13 hwf3 (fun _ _ ↦ rfl)
    (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.FirstClaim.b12_next)) (match_callS hb3.frame)
    fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hmid4, hwi4, hrdi4, hrsi4, hrdx4, hat4⟩ := ok_b13
  have hf4 : Frame m0 1376 slots 0 st4.data := Frame.of_block hb3.frame hwf3 hm4 hmid4 slots_le'
  have hs4 := sameOutside_touch hwf3 hm4 (r := 0) rfl (by decide) (within_spec hwi4)
  have hsp4 : rspOf st4.data = fbA m0 := by rw [hf4.sp, off_zero]
  have hso4 : NativeRustcVm.SameOutside m0.dmem st4.data.dmem (Out m0) := fun q hq ↦
    (hs4 q fun ht ↦ hq (touch_out h (fun _ hj ↦ by omega) ht)).trans (hb3.same q hq)
  have f7 : reg st4.data .rdi = off (fbA m0) 840 := (hm4.regs .rdi _ hrdi4).trans (eval_ptr0 840)
  have f6 : reg st4.data .rsi = reg m0 .rcx :=
    (hm4.regs .rsi _ hrsi4).trans ((a3 .r12 (by simp)).trans ((hsv2.1 .r12 rfl).trans
      ((a1 .r12 (by simp)).trans hI.r12)))
  have f2 : (reg st4.data .rdx).toNat = 1 := by
    rw [show reg st4.data .rdx = _ from hm4.regs .rdx _ hrdx4]; rfl
  have hpt4 : NativeRustcVm.BufEWAt st4.data.dmem (off (fbA m0) 840) 30
      (inst.extract 4 inst.size).toList := by
    have := hpt
    rw [← hd3] at this
    exact ⟨this.1, keep_touch h hs4 (by rw [NativeRustcVm.length_wordBytes]; decide)
      (by rw [NativeRustcVm.length_wordBytes]; omega) this.2.1,
      by
        have e := this.2.2
        rw [show off (fbA m0) 840 + 8#64 = off (fbA m0) 848 from off_off _ _ _] at e ⊢
        have hl :
            ((inst.extract 4 inst.size).toList.flatMap NativeRustcVm.ewBytes).length ≤ 480 := by
          rw [ews_len, Array.length_toList, Array.size_extract]; omega
        exact keep_touch h hs4 (by omega) (by omega) e⟩
  have hlen4 : (inst.extract 4 inst.size).toList.length = inst.size - 4 := by simp
  have hcnt4 : (NativeRustcVm.wordOf st4.data.dmem (off (fbA m0) 840)).toNat = inst.size - 4 := by
    rw [NativeRustcVm.wordOf_of_wordAt hpt4.2.1, Nat.toUInt64,
      UInt64.toNat_ofNat_of_lt' (show _ < UInt64.size by simp [UInt64.size]; omega), hlen4]
  have hseg := seg_keep h hso4
  have hg := hn.g
  have hsg := hn.sg
  have hsb4 : (stackBelow st4.data bufEWExtendStack).toNat = (rspOf m0).toNat - 1384 := by
    rw [sb_call h hsp4 (by decide), hbe]; omega
  have hgm : NativeRustcVm.Mapped m0.dmem (reg m0 .rcx) (16 * 1) :=
    rd_mapped h (r := ewsRegion (reg m0 .rcx) 1) (List.mem_cons_of_mem _ List.mem_cons_self)
  have hpre4 : BufEWExtendPre 30 st4.data := by
    unfold BufEWExtendPre Readable OffStack
    rw [f7, f6, f2, hcnt4]
    refine ⟨stackOk_callee h.st hf4.kept hsp4 (by rw [stack_eq, hbe]; decide), by omega,
      ⟨Mapped.keeps (mapped_off hfmap (by decide)) hf4.kept, by
        show _ + _ ≤ _; rw [hf840]; omega⟩, ⟨Mapped.keeps hgm hf4.kept, by
        show _ + _ ≤ _; omega⟩, ?_, ?_, ?_⟩
    · show _ + _ ≤ _ ∨ _ + _ ≤ _
      rw [hf840]; omega
    · show _ + _ ≤ _ ∨ _ + _ ≤ _
      rw [hf840, hsb4, hbe]; omega
    · show _ + _ ≤ _ ∨ _ + _ ≤ _
      rw [hsb4, hbe]; omega
  refine call_then hpc4 hext hpre4 fun st5 hpc5 hrsp5 ⟨hpost5, hch5, hsv5⟩ ↦ ?_
  rw [f7, hcnt4, f2, ite_eq_left (by omega)] at hpost5
  obtain ⟨hr5, hpt5⟩ := hpost5
  have hsl5 : slice st4.data (reg st4.data .rsi) (reg st4.data .rdx) = segment := by
    unfold slice
    rw [f6, f2, show 1 = segment.toList.length by rw [Array.length_toList, h.segSz],
      NativeRustcVm.ewsOf_of_ewsAt hseg]
  rw [bufEWOf_eq hpt4 (by decide), hsl5, ← Array.toList_append] at hpt5
  unfold Changes at hch5
  rw [f7, hbe] at hch5
  obtain ⟨hb5, hch5'⟩ := call_body h hf4 hso4 hsv5 hrsp5 (s := 8) (by decide) hch5
    (frame_D h (o := 840) (n := 8 + 16 * 30) (by decide))
  -- `b14`: `extend`'s result checked.
  have hwf5 := wf_body h hb5.frame.kept (d := st5.data) (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of b14_in_code (by simp [b14]) hp) exit_b14 hwf5 nofun
    (hpc5.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.FirstClaim.b13_next)) (match_callS hb5.frame)
    fun st6 hm6 hpc6 ↦ ?_
  obtain ⟨hmid6, hmem6, hat6⟩ := ok_test b14 (by simp)
  have hd6 : st6.data.dmem = st5.data.dmem := hm6.dmem_eq hwf5 hmem6
  have hb6 : Body m0 st6.data := hb5.of_mem (Frame.of_block hb5.frame hwf5 hm6 hmid6 slots_le') hd6
  have hc6 : testA.eval (frameEnv m0 st5.data 1376 [(argA m0, 24)] (fun _ ↦ 0) 0) = false := by
    show CmpOp.apply .eq .W8 (BinOp.apply .and .W8 (reg st5.data .rax) (reg st5.data .rax))
      (BitVec.ofNat 64 0) = false
    rw [al_test]
    unfold boolRet at hr5
    rw [hr5]; decide
  simp only [PcOk, hc6, Bool.false_eq_true, ite_false] at hpc6
  have a4 : ∀ r ∈ [Reg64.rbp, .r12, .r13, .r15], reg st4.data r = reg st3.data r :=
    fun r hr ↦ atoms_eq hm4 hat4 hr
  have a6 : ∀ r ∈ [Reg64.rdx, .rbx, .rbp, .r12, .r13, .r14, .r15],
      reg st6.data r = reg st5.data r := fun r hr ↦ atoms_eq hm6 hat6 hr
  have hreg : ∀ r ∈ [Reg64.rbp, .r13, .r15], reg st6.data r = reg st.data r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      exact (a6 _ (by simp)).trans ((hsv5.1 _ rfl).trans ((a4 _ (by simp)).trans
        ((a3 _ (by simp)).trans ((hsv2.1 _ rfl).trans (a1 _ (by simp))))))
  -- the instance weights, the bit weights kept
  have kmu : ∀ {o : Nat} {bs : List UInt8}, 64 ≤ o → o + bs.length ≤ 328 →
      NativeRustcVm.BytesAt st1.data.dmem (off (fbA m0) o) bs →
      NativeRustcVm.BytesAt st6.data.dmem (off (fbA m0) o) bs := fun h64 hle hb ↦ by
    rw [hd6]
    refine keep_fcall h hch5' (by omega) (by decide) (by omega)
      (keep_touch h hs4 (by omega) (by omega) ?_)
    show NativeRustcVm.BytesAt st3.data.dmem _ _
    rw [hd3]
    exact keep_fcall h hch2 (by omega) (by decide) (by omega) hb
  have hmu6 : NativeRustcVm.BufEWAt st6.data.dmem (off (fbA m0) 64) 16
      (eqKernel (inst.extract 0 4)).toList :=
    ⟨by rw [Array.length_toList]; exact hmus,
      kmu (by decide) (by rw [NativeRustcVm.length_wordBytes]; decide) hcnt,
      by rw [show off (fbA m0) 64 + 8#64 = off (fbA m0) 72 from off_off _ _ _]
         exact kmu (by decide) (by omega) hmu1⟩
  have hw6 : ElemsAt st6.data.dmem (wA m0) (bitW (eqKernel lanePoint)) 1600 := by
    have ck : ∀ q, (NativeRustcVm.InRange (off (fbA m0) 840) (8 + 16 * 30) q ∨ Low m0 q) →
        ¬ NativeRustcVm.InRange (wA m0) 25600 q :=
      stk_w h fun _ hq ↦ hq.elim (fd_stk h (by decide)) (low_stk h)
    have w1 := w_keep h hs1 (stk_w h fun _ hq ↦ touch_stk h (fun _ hj ↦ by omega) hq) hI.w
    have w2 := w_keep h hch2 ck w1
    have w4 := w_keep h hs4 (stk_w h fun _ hq ↦ touch_stk h (fun _ hj ↦ by omega) hq)
      (by show ElemsAt st3.data.dmem _ _ _; rw [hd3]; exact w2)
    rw [hd6]
    exact w_keep h hch5' ck w4
  refine .done _ ⟨hpc6.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.FirstClaim.b14_next), hb6, hw6, hmu6,
    by rw [hd6]; exact hpt5, ?_, ?_, ?_⟩
  · rw [hreg .r13 (by simp)]; exact hI.r13
  · rw [hreg .rbp (by simp)]; exact hI.rbp
  · rw [hreg .r15 (by simp)]; exact hI.r15

end

end NativeRustcVmX64.KeccakGkr.FirstClaim
