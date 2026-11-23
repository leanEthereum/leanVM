module

public import NativeRustcVmX64.KeccakGkr.SlotWeights.Pre
public import NativeRustcVmX64.KeccakGkr.SlotWeights.Arith
public import NativeRustcVm.Transcript.Loop
public import NativeRustcVmX64.Code.Vm.EqKernel.Names

/-!
# `slot_weights`: the prologue (x86-64)

`b0` pushes RBP to RBX, reserves 104 bytes, saves `first`, `count` and the weights' address in
the frame, zeroes the segment kernel's four elements at `48` and calls `eq_kernel` on the point's
last `|point| - (logSteps - 4)` coordinates (`ptrS`, `lenS`: rustc's saturating `logSteps - 4`)
into them; `b1` saves its result at `8` and checks it succeeded, `b2` starts the rows' zeroing loop
(`prologue`, to `ZeroInv` at row `0`).
-/

namespace NativeRustcVmX64.KeccakGkr.SlotWeights

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.SlotWeights
open NativeRustcVm (Region)
open NativeRustcVm.Transcript (off off_zero off_off toNat_off inRange_iff' not_inRange_of_apart
  Mapped.keeps bytesAt_congr inRange_off_self)
open NativeRustcVm.KeccakGkr (rowsFlat rowsBytes weightsBytes WeightsAt)

@[expose] public section

/-- **The zeroing loop's head** at row `r`: the rows before it zero. -/
structure ZeroInv (m0 : MachineData) (c : KeccakClaimW) (r : Nat) (st : MachineData) : Prop where
  ctx : Ctx m0 c st
  r_lt : r < 64
  rax : reg st .rax = off (rowsA m0) (1024 * r + 56)
  rcx : reg st .rcx = BitVec.ofNat 64 (1024 * r)
  rows : ElemsAt st.dmem (rowsA m0) (fun _ ↦ 0) (64 * r)

end

public section

variable {c : KeccakClaimW} {m0 : MachineData}

theorem stack_eq : slotWeightsStack = 416 := by decide

theorem extract_eq_drop (p : Array EW) (n : Nat) :
    p.extract n p.size = (p.toList.drop n).toArray := by
  apply Array.toList_inj.mp
  simp [Array.toList_extract, List.extract]

/-- The frame's first `160` bytes are the top of the stack. -/
theorem frame_out (h : PreOk m0 c) {q : BitVec 64} (hq : NativeRustcVm.InRange (fbA m0) 160 q) :
    Out m0 q :=
  Or.inr (inRange_frame_stack h.st.2.1 h.st.1 (by rw [stack_eq]; decide) hq)

/-- Bytes at an offset of an area kept where memory changed only off them. -/
theorem keep_off {d d' : DataMem} {b : BitVec 64} {o : Nat} {bs : List UInt8}
    {R : BitVec 64 → Prop} (h : NativeRustcVm.BytesAt d (off b o) bs)
    (hs : NativeRustcVm.SameOutside d d' R) (hR : ∀ i < bs.length, ¬ R (off b (o + i))) :
    NativeRustcVm.BytesAt d' (off b o) bs :=
  bytesAt_congr h fun i hi ↦ by rw [NativeRustcVm.Transcript.off_add]; exact hs _ (hR i hi)

variable [Host] {k : Nat}

/-- **The prologue**: from the entry to the zeroing loop's head at row `0`. -/
theorem prologue (hp : Placed code k) (hpre : SlotWeightsPre c m0)
    (heq : Spec (Labels.label NativeRustcVmX64.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b3Offset) ∧ ZeroInv m0 c 0 s'.data)
      ⟨m0, Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b0Offset)⟩ := by
  have h := preOk hpre
  have hsz := h.sz
  have hpt := h.ptAt
  have hlt := h.fit.1
  have hle2 := h.fit.2
  set L := (reg m0 .rdi).toNat - 4 with hL
  set n := c.point.size with hn
  have hR8 := h.args.2
  have hN : 416 ≤ (rspOf m0).toNat := by have := h.st.1; rw [stack_eq] at this; exact this
  have hfb : (fbA m0).toNat = (rspOf m0).toNat - 160 := fbA_toNat h
  have hsb : (stackBelow m0 slotWeightsStack).toNat = (rspOf m0).toNat - 416 := by
    rw [stackBelow_toNat (by rw [stack_eq]; exact hN), stack_eq]
  have hptS : (stackBelow m0 slotWeightsStack).toNat + (slotWeightsStack + 8) ≤ (ptA m0).toNat ∨
      (ptA m0).toNat + 16 * n ≤ (stackBelow m0 slotWeightsStack).toNat := h.ptS
  rw [hsb, stack_eq] at hptS
  have hptn : (ptA m0).toNat + 16 * n ≤ 2 ^ 64 := h.pt.2
  -- `b0`: the prologue, `call eq_kernel`.
  have hwf0 := wf_body h (d := m0) (fun _ h ↦ h) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b0Offset + b0.length)).toBitVec)
  have hm0 : Match (frameEnv m0 m0 160 [(argA m0, 8)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b0Offset + b0.length)).toBitVec) entryS m0 :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial ⟨arg_alias, trivial⟩
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf0 (fun _ _ ↦ rfl) hm0
    fun st1 hm1 hpc1 => ?_
  obtain ⟨hpro, hws1, hw16, hw24, hw40, hx7, hx6, hx2, hx1⟩ := ok_b0
  have hf1 : Frame m0 160 slots 0 st1.data :=
    Frame.of_prologue Frame.entry hwf0 hm1 hpro slots_le (by decide)
  have hs1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem (NativeRustcVm.InRange (fbA m0) 160) :=
    sameOutside_low hwf0 hm1 (r := 0) rfl (by decide) hws1
  have hsp1 : rspOf st1.data = fbA m0 := by rw [hf1.sp, off_zero]
  have l16 := wordAt_write hm1 (r := 0) (o := 16) (v := .reg .r8) rfl (by decide) hw16
  have l24 := wordAt_write hm1 (r := 0) (o := 24) (v := .reg .r9) rfl (by decide) hw24
  have l40 := wordAt_write hm1 (r := 0) (o := 40) (v := .reg .rcx) rfl (by decide) hw40
  have hcL : L ≤ (reg m0 .rdx).toNat := by omega
  have hX7 : reg st1.data .rdi = off (ptA m0) (16 * L) :=
    (hm1.regs .rdi _ hx7).trans (ptrS_eval _ hcL)
  have hX6 : (reg st1.data .rsi).toNat = n - L := by
    rw [show reg st1.data .rsi = _ from hm1.regs .rsi _ hx6, lenS_eval _ hcL]
    exact congrArg (· - L) hsz.symm
  have hX2 : reg st1.data .rdx = off (fbA m0) 48 := (hm1.regs .rdx _ hx2).trans (eval_ptr0 48)
  have hX1 : (reg st1.data .rcx).toNat = 4 := by
    rw [show reg st1.data .rcx = _ from hm1.regs .rcx _ hx1]; rfl
  -- `eq_kernel` into the frame's four elements.
  have hek : eqKernelStack = 256 := by decide
  have hsp1n : (stackBelow st1.data eqKernelStack).toNat = (rspOf m0).toNat - 416 := by
    rw [stackBelow_callee hsp1 (by rw [hek]; omega), stackBelow_toNat (by rw [hek]; omega), hek]
  have hptr : (off (ptA m0) (16 * L)).toNat = (ptA m0).toNat + 16 * L := toNat_off (by omega)
  have hf48 : (off (fbA m0) 48).toNat = (rspOf m0).toNat - 160 + 48 := by
    rw [toNat_off (by omega), hfb]
  have hfmap := frame_mapped h.st (F := 160) (by rw [stack_eq]; decide)
  -- the point's segment coordinates, kept by the prologue
  have hdrop : NativeRustcVm.EWsAt st1.data.dmem (off (ptA m0) (16 * L)) (c.point.toList.drop L) :=
    bytesAt_congr (NativeRustcVm.EWsAt.drop hpt L) fun i hi ↦ hs1 _ fun hq ↦ by
      rw [NativeRustcVm.Transcript.length_flatMap_ewBytes, List.length_drop, Array.length_toList]
        at hi
      rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), toNat_off (by omega)] at hq
      omega
  have hpre1 : EqKernelPre st1.data := by
    unfold EqKernelPre SliceOk Readable OffStack
    rw [hX7, hX2, hX6, hX1]
    refine ⟨stackOk_callee h.st hf1.kept hsp1 (by rw [stack_eq, hek]), by omega,
      ⟨⟨Mapped.keeps (mapped_off h.pt.1 (by show 16 * L + 16 * (n - L) ≤ 16 * n; omega))
        hf1.kept, by show _ + _ ≤ _; rw [hptr]; omega⟩, ?_⟩,
      ⟨⟨Mapped.keeps (mapped_off hfmap (by decide)) hf1.kept, by show _ + _ ≤ _; rw [hf48]; omega⟩,
        ?_⟩, ?_⟩
    · show _ + _ ≤ _ ∨ _ + _ ≤ _
      rw [hptr, hsp1n, hek]; omega
    · show _ + _ ≤ _ ∨ _ + _ ≤ _
      rw [hf48, hsp1n, hek]; omega
    · show _ + _ ≤ _ ∨ _ + _ ≤ _
      rw [hptr, hf48]; omega
  refine call_then hpc1 heq hpre1 fun st2 hpc2 hrsp2 ⟨hpost, hch, hsv2⟩ => ?_
  have h4 : 2 ^ (n - L) ≤ 4 := by
    rcases (show n - L = 1 ∨ n - L = 2 by omega) with e | e <;> rw [e] <;> decide
  rw [hX6, hX1] at hpost
  simp only [h4, ite_true] at hpost
  obtain ⟨hr0, -, hker⟩ := hpost
  have hslice : slice st1.data (reg st1.data .rdi) (reg st1.data .rsi) =
      c.point.extract L c.point.size := by
    unfold slice
    rw [hX7, hX6, extract_eq_drop]
    congr 1
    have := NativeRustcVm.ewsOf_of_ewsAt hdrop
    rwa [List.length_drop, Array.length_toList] at this
  rw [hslice, hX2] at hker
  change NativeRustcVm.EWsAt _ _ (segK (reg m0 .rdi).toNat c).toList at hker
  have hK : (segK (reg m0 .rdi).toNat c).size = 2 ^ (n - L) := by
    rw [segK, NativeVm.Math.Keccak.eqKernel_size, Array.size_extract, Nat.min_self]
  have hk2 : 2 ≤ (segK (reg m0 .rdi).toNat c).size := by
    rw [hK]
    rcases (show n - L = 1 ∨ n - L = 2 by omega) with e | e <;> rw [e] <;> decide
  unfold Changes at hch
  rw [hX2, hX1] at hch
  have hcal : ∀ q, NativeRustcVm.InRange (stackBelow st1.data eqKernelStack) eqKernelStack q →
      NativeRustcVm.InRange (stackBelow m0 slotWeightsStack) slotWeightsStack q ∧
        ¬ NativeRustcVm.InRange (stackBelow m0 160) (160 + 8) q :=
    fun q hq ↦ inRange_callee hsp1 h.st.2.1 h.st.1 (by rw [stack_eq, hek]) hq
  have hfnw := frame_noWrap h.st (F := 160) (by rw [stack_eq]; decide)
  have hlow : ∀ j, j < 48 → ¬ (NativeRustcVm.InRange (off (fbA m0) 48) (16 * 4) (off (fbA m0) j) ∨
      NativeRustcVm.InRange (stackBelow st1.data eqKernelStack) eqKernelStack (off (fbA m0) j)) := by
    rintro j hj (hq | hq)
    · rw [NativeRustcVm.Transcript.inRange_off_iff (by omega) (by omega)] at hq; omega
    · exact (hcal _ hq).2 (inRange_off_self (by omega) (by omega))
  have hhigh : ∀ j, 112 ≤ j → j < 168 → ¬ (NativeRustcVm.InRange (off (fbA m0) 48) (16 * 4)
      (off (fbA m0) j) ∨
      NativeRustcVm.InRange (stackBelow st1.data eqKernelStack) eqKernelStack (off (fbA m0) j)) := by
    rintro j hj hj' (hq | hq)
    · rw [NativeRustcVm.Transcript.inRange_off_iff (by omega) (by omega)] at hq; omega
    · exact (hcal _ hq).2 (inRange_off_self (by omega) (by omega))
  have hf2 : Frame m0 160 slots 8 st2.data :=
    Frame.call_at hf1 hsv2 hrsp2 hch
      (fun p hp i hi ↦ hhigh _ (by have := slots_ge p hp; omega) (by have := slots_le p hp; omega))
      (fun j hj ↦ hhigh _ (by omega) (by omega))
  have m16 := keep_off l16 hch fun i hi ↦ hlow _ (by
    rw [NativeRustcVm.length_wordBytes] at hi; omega)
  have m24 := keep_off l24 hch fun i hi ↦ hlow _ (by
    rw [NativeRustcVm.length_wordBytes] at hi; omega)
  have m40 := keep_off l40 hch fun i hi ↦ hlow _ (by
    rw [NativeRustcVm.length_wordBytes] at hi; omega)
  have hseg : ∀ i < 2, NativeRustcVm.EWAt st2.data.dmem (off (fbA m0) (48 + 16 * i))
      ((segK (reg m0 .rdi).toNat c).getD i 0) := fun i hi ↦ by
    rw [← off_off]; exact ewsAt_getD hker (by omega)
  have hso2 : NativeRustcVm.SameOutside m0.dmem st2.data.dmem (Out m0) := by
    intro q hq
    rw [hch q fun hc ↦ hq (by
      rcases hc with hc | hc
      · exact frame_out h (off_in (hfnw.mono (by omega)) (by decide) hc)
      · exact Or.inr (hcal q hc).1)]
    exact hs1 q fun hc ↦ hq (frame_out h hc)
  -- `b1`: `eq_kernel`'s result saved and checked.
  have hwf2 := wf_body h hf2.kept (d := st2.data) (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) exit_b1 hwf2 nofun
    (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SlotWeights.b0_next)) (match_callS hf2) fun st3 hm3 hpc3 => ?_
  obtain ⟨hmid3, hws3, hw8⟩ := ok_b1
  have hf3 : Frame m0 160 slots 8 st3.data := Frame.of_block hf2 hwf2 hm3 hmid3 slots_le
  have hs3 : NativeRustcVm.SameOutside st2.data.dmem st3.data.dmem
      (NativeRustcVm.InRange (fbA m0) 16) :=
    sameOutside_low hwf2 hm3 (r := 0) rfl (by decide) fun w hw ↦ ⟨(hws3 w hw).1, (hws3 w hw).2.2⟩
  have l8 := wordAt_write hm3 (r := 0) (o := 8) (v := .reg .rax) rfl (by decide) hw8
  rw [show UInt64.ofBitVec ((Sym.reg .rax).eval (frameEnv m0 st2.data 160 [(argA m0, 8)]
    (fun _ ↦ 0) 0)) = 1 from by show UInt64.ofBitVec (reg st2.data .rax) = 1; rw [hr0]; rfl] at l8
  have hc3 : ((SBool.cmp .eq .W64 (.reg .rax) (.lit 1)).not).eval
      (frameEnv m0 st2.data 160 [(argA m0, 8)] (fun _ ↦ 0) 0) = false := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, low_W64]
    rw [show (frameEnv m0 st2.data 160 [(argA m0, 8)] (fun _ ↦ 0) 0).regs .rax = 1#64 from hr0]
    rfl
  simp only [PcOk, hc3, Bool.false_eq_true, ite_false] at hpc3
  have hfb16 : ∀ q, NativeRustcVm.InRange (fbA m0) 16 q → NativeRustcVm.InRange (fbA m0) 160 q :=
    fun q hq ↦ inRange_mono hq (by decide)
  have hso3 : NativeRustcVm.SameOutside m0.dmem st3.data.dmem (Out m0) := fun q hq ↦ by
    rw [hs3 q fun hc ↦ hq (frame_out h (hfb16 q hc))]
    exact hso2 q hq
  have hnot16 : ∀ j, 16 ≤ j → j < 168 → ¬ NativeRustcVm.InRange (fbA m0) 16 (off (fbA m0) j) := by
    intro j hj hj' hq
    have hfb' : (stackBelow m0 160).toNat = (rspOf m0).toNat - 160 := hfb
    have e : (off (stackBelow m0 160) j).toNat = (stackBelow m0 160).toNat + j :=
      toNat_off (by have := h.st.2.1; omega)
    rw [inRange_iff' (hfnw.mono (by omega)), e] at hq
    omega
  have hloc3 : Loc m0 c st3.data.dmem :=
    ⟨l8, keep_off m16 hs3 fun i hi ↦ hnot16 _ (by omega) (by
        rw [NativeRustcVm.length_wordBytes] at hi; omega),
      keep_off m24 hs3 fun i hi ↦ hnot16 _ (by omega) (by
        rw [NativeRustcVm.length_wordBytes] at hi; omega),
      keep_off m40 hs3 fun i hi ↦ hnot16 _ (by omega) (by
        rw [NativeRustcVm.length_wordBytes] at hi; omega),
      fun i hi ↦ keep_off (hseg i hi) hs3 fun t ht ↦ hnot16 _ (by omega) (by
        rw [NativeRustcVm.length_ewBytes] at ht; omega)⟩
  -- `b2`: the zeroing loop's start.
  have hwf3 := wf_body h hf3.kept (d := st3.data) (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of b2_in_code (by simp [b2]) hp) exit_b2 hwf3 nofun
    (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SlotWeights.b1_next)) (match_callS hf3) fun st4 hm4 hpc4 => ?_
  obtain ⟨hmid4, hmem4, hx0₄, hx1₄⟩ := ok_b2
  have hf4 : Frame m0 160 slots 8 st4.data := Frame.of_block hf3 hwf3 hm4 hmid4 slots_le
  have hd4 : st4.data.dmem = st3.data.dmem := hm4.dmem_eq hwf3 hmem4
  simp only [PcOk] at hpc4
  refine .done _ ⟨hpc4.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SlotWeights.b2_next), ⟨hf4, hd4 ▸ hso3, hd4 ▸ hloc3⟩, by decide,
    ?_, ?_, fun i hi ↦ absurd hi (by omega)⟩
  · rw [show reg st4.data .rax = _ from hm4.regs .rax _ hx0₄]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
    rw [load_rows h hso3, BitVec.add_comm]
  · exact hm4.regs .rcx _ hx1₄

end

end NativeRustcVmX64.KeccakGkr.SlotWeights
