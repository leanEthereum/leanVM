module

public import NativeRustcVmX64.KeccakGkr.SlotWeights.Seg
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `slot_weights`: one bit's product (x86-64)

From the bit loop's head (`Inner`, at `NativeRustcVmX64.Vm.SlotWeights.label_8`): `b12` computes the row (below `63`: it
falls through), `b13` loads the weight and calls `EW::mul` (`bit_mul`, to `AfterMul`); `p1`, `p2`
store the product at the row's element, `b11` counts (`bit_store`).
-/

namespace NativeRustcVmX64.KeccakGkr.SlotWeights

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVmX64.Vm.SlotWeights
open NativeRustcVm (Region)
open NativeRustcVm.Transcript (off off_zero off_off toNat_off inRange_iff' not_inRange_of_apart
  Mapped.keeps bytesAt_congr inRange_off_self inRange_off_iff)
open NativeRustcVm.KeccakGkr (rowsFlat rowsBytes weightsBytes WeightsAt)

@[expose] public section

/-- The weight of bit `j`. -/
abbrev wt (c : KeccakClaimW) (j : Nat) : EW := c.weights.getD j 0

/-- The row of bit `j` of segment `s`. -/
abbrev rowOf (m0 : MachineData) (s j : Nat) : Nat := 25 * ((reg m0 .r8).toNat + s) + j / 64

/-- **After `EW::mul`**: the product in RAX, RDX, the row in R12. -/
structure AfterMul (m0 : MachineData) (c : KeccakClaimW) (s j : Nat) (st : MachineData) : Prop where
  ctx : Ctx m0 c st
  s_lt : s < (reg m0 .r9).toNat
  j_lt : j < 1600
  segw : NativeRustcVm.WordAt st.dmem (off (fbA m0) 32) (UInt64.ofNat s)
  r13 : reg st .r13 = (scale m0 c s).c0.toBitVec
  rbp : reg st .rbp = (scale m0 c s).c1.toBitVec
  r14 : reg st .r14 = BitVec.ofNat 64 (25 * ((reg m0 .r8).toNat + s))
  r15 : reg st .r15 = BitVec.ofNat 64 j
  rbx : reg st .rbx = BitVec.ofNat 64 (16 * j)
  r12 : reg st .r12 = BitVec.ofNat 64 (rowOf m0 s j)
  rax : reg st .rax = (scale m0 c s * wt c j).c0.toBitVec
  rdx : reg st .rdx = (scale m0 c s * wt c j).c1.toBitVec
  rows : ElemsAt st.dmem (rowsA m0) (prog (reg m0 .rdi).toNat c (reg m0 .r8).toNat (flat m0 s j))
    4096

end

public section

variable {c : KeccakClaimW} {m0 : MachineData}

/-- A step's frame region: the frame is within `Out`, the locals at `8` to `80` off the first
`8` bytes. -/
theorem low8_ok (h : PreOk m0 c) :
    (∀ q, NativeRustcVm.InRange (fbA m0) 8 q → Out m0 q) ∧
    (∀ j, (8 ≤ j ∧ j < 32) ∨ (40 ≤ j ∧ j < 80) →
      ¬ NativeRustcVm.InRange (fbA m0) 8 (off (fbA m0) j)) := by
  have hfnw : NativeRustcVm.NoWrap (fbA m0) (160 + 8) := frame_noWrap h.st (by rw [stack_eq]; decide)
  refine ⟨fun q hq ↦ frame_out h (inRange_mono hq (by decide)), fun j hj hq ↦ ?_⟩
  have e : (off (fbA m0) j).toNat = (fbA m0).toNat + j := toNat_off (by
    unfold NativeRustcVm.NoWrap at hfnw; omega)
  rw [inRange_iff' (hfnw.mono (by omega)), e] at hq
  omega

variable [Host] {k : Nat}

/-- **The product of bit `j`**: `b12`, `b13`, `EW::mul`. -/
theorem bit_mul (hp : Placed code k) (h : PreOk m0 c)
    (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {s j : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b12Offset)) (hI : Inner m0 c s j st.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b14Offset) ∧ AfterMul m0 c s j s'.data)
      st := by
  have hs := hI.s_lt
  have hj := hI.j_lt
  have hc2 := h.cnt2
  have hfs : (reg m0 .r8).toNat + s ≤ 1 := by omega
  have hrowlt : rowOf m0 s j < 63 := by unfold rowOf; omega
  have hfnw : NativeRustcVm.NoWrap (fbA m0) (160 + 8) := frame_noWrap h.st (by rw [stack_eq]; decide)
  -- `b12`: the row.
  have hwf := wf_body h hI.ctx.frame.kept (d := st.data) (vars := fun _ ↦ 0) (ret := 0)
  refine exec_at (infix_of b12_in_code (by simp [b12]) hp) exit_b12 hwf nofun hpc
    (match_callS hI.ctx.frame) fun st1 hm1 hpc1 ↦ ?_
  obtain ⟨hmid1, hmem1, hr12, hr13, hrbp, hr14, hr15, hrbx⟩ := ok_b12
  have hd1 : st1.data.dmem = st.data.dmem := hm1.dmem_eq hwf hmem1
  have hctx1 := hI.ctx.of_block hwf hm1 hmid1 hmem1
  have hrow : rowS.eval (frameEnv m0 st.data 160 [(argA m0, 8)] (fun _ ↦ 0) 0) =
      BitVec.ofNat 64 (rowOf m0 s j) := by
    apply BitVec.eq_of_toNat_eq
    rw [rowS_eval _ (a := 25 * ((reg m0 .r8).toNat + s)) (j := j)
      (by rw [show (frameEnv m0 st.data 160 [(argA m0, 8)] (fun _ ↦ 0) 0).regs .r14 = _ from hI.r14,
        toNat_ofNat_lt (by omega)])
      (by rw [show (frameEnv m0 st.data 160 [(argA m0, 8)] (fun _ ↦ 0) 0).regs .r15 = _ from hI.r15,
        toNat_ofNat_lt (by omega)]) (by omega) (by omega), toNat_ofNat_lt (by omega)]
  have hu : (BitVec.ofNat 64 (rowOf m0 s j)).ult (BitVec.ofNat 64 63) = true := by
    rw [BitVec.ult, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]
    exact decide_eq_true (by omega)
  simp only [PcOk, SBool.eval, CmpOp.apply, low_W64, hrow, Sym.eval, hu, Bool.not_true,
    Bool.false_and, Bool.false_eq_true, ite_false] at hpc1
  -- `b13`: the weight, `call EW::mul`.
  have hWs := weights_keep h hctx1.same
  have hwj : NativeRustcVm.EWAt st1.data.dmem (off (wA m0) (16 * j)) (wt c j) :=
    ewsAt_getD hWs.2 (by rw [hWs.1]; exact hj)
  have hwn : (wA m0).toNat + 25600 ≤ 2 ^ 64 := h.w.2
  have hfb := fbA_toNat h
  have hwS : (stackBelow m0 slotWeightsStack).toNat + (slotWeightsStack + 8) ≤ (wA m0).toNat ∨
      (wA m0).toNat + 25600 ≤ (stackBelow m0 slotWeightsStack).toNat := h.wS
  rw [sb_toNat h, stack_eq] at hwS
  have hwjn : (off (wA m0) (16 * j)).toNat = (wA m0).toNat + 16 * j := toNat_off (by omega)
  have hst := h.st.2.1
  have hwf1 : (frameEnv m0 st1.data 160 [(off (wA m0) (16 * j), 16)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b13Offset + b13.length)).toBitVec).WF :=
    frame_wf ⟨Mapped.keeps (frame_mapped h.st (by rw [stack_eq]; decide)) hctx1.frame.kept, hfnw⟩
      (fun x hx ↦ by
        rw [List.mem_singleton] at hx
        subst hx
        exact ⟨Mapped.keeps (mapped_off h.w.1 (by show 16 * j + 16 ≤ 25600; omega))
          hctx1.frame.kept, by show _ + 16 ≤ 2 ^ 64; rw [hwjn]; omega⟩)
      (List.pairwise_pair.mpr (by show _ ∨ _; rw [hwjn, hfb]; omega))
  have hld40 : (frameEnv m0 st1.data 160 [(off (wA m0) (16 * j), 16)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b13Offset + b13.length)).toBitVec).load 0 40 8 = wA m0 := by
    rw [load_of_wordAt hctx1.loc.wts]
  have hm1' : Match (frameEnv m0 st1.data 160 [(off (wA m0) (16 * j), 16)] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b13Offset + b13.length)).toBitVec) mulS st1.data :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hctx1.frame.rsp_eval, trivial⟩ trivial trivial
      ⟨by
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
        rw [hld40, show (frameEnv m0 st1.data 160 [(off (wA m0) (16 * j), 16)] (fun _ ↦ 0)
          (Host.addrOf (k + NativeRustcVmX64.Vm.SlotWeights.b13Offset + b13.length)).toBitVec).regs .rbx = _ from
            (hm1.regs .rbx _ hrbx).trans hI.rbx,
          show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
        rfl, trivial⟩
  refine exec_at (infix_of b13_in_code (by simp [b13]) hp) exit_b13 hwf1 (fun _ _ ↦ rfl)
    (hpc1.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SlotWeights.b12_next)) hm1' fun st2 hm2 hpc2 ↦ ?_
  obtain ⟨hmid2, hws2, hx7, hx6, hx2, hx1, hr12', hr13', hrbp', hr14', hr15', hrbx'⟩ := ok_b13
  have hf2 : Frame m0 160 slots 0 st2.data := Frame.of_block hctx1.frame hwf1 hm2 hmid2 slots_le
  have hs2 : NativeRustcVm.SameOutside st1.data.dmem st2.data.dmem
      (NativeRustcVm.InRange (fbA m0) 8) :=
    sameOutside_low hwf1 hm2 (r := 0) rfl (by decide) hws2
  have hsp2 : rspOf st2.data = stackBelow m0 160 := by rw [hf2.sp, off_zero]
  have hwjw := NativeRustcVm.ewAt_iff.mp hwj
  have hX7 : reg st2.data .rdi = (scale m0 c s).c0.toBitVec :=
    (hm2.regs .rdi _ hx7).trans ((hm1.regs .r13 _ hr13).trans hI.r13)
  have hX6 : reg st2.data .rsi = (scale m0 c s).c1.toBitVec :=
    (hm2.regs .rsi _ hx6).trans ((hm1.regs .rbp _ hrbp).trans hI.rbp)
  have hX2 : reg st2.data .rdx = (wt c j).c0.toBitVec :=
    (hm2.regs .rdx _ hx2).trans (load_of_wordAt (r := 1) (o := 0) (by
      show NativeRustcVm.WordAt st1.data.dmem (off (wA m0) (16 * j) + BitVec.ofNat 64 0) _
      rw [NativeRustcVm.addr_add_zero]; exact hwjw.1))
  have hX1 : reg st2.data .rcx = (wt c j).c1.toBitVec :=
    (hm2.regs .rcx _ hx1).trans (load_of_wordAt (r := 1) (o := 8) hwjw.2)
  have hmS : 160 + ewMulStack ≤ slotWeightsStack := by decide
  refine call_then hpc2 hmul (stackOk_callee h.st hf2.kept hsp2 hmS)
    fun st3 hpc3 hrsp3 ⟨hc0, hc1, hs3, hsv3⟩ ↦ ?_
  rw [hX7, hX6, hX2, hX1] at hc0 hc1
  have hcal : ∀ q, NativeRustcVm.InRange (stackBelow st2.data ewMulStack) ewMulStack q →
      NativeRustcVm.InRange (stackBelow m0 slotWeightsStack) slotWeightsStack q ∧
        ¬ NativeRustcVm.InRange (stackBelow m0 160) (160 + 8) q :=
    fun q hq ↦ inRange_callee hsp2 h.st.2.1 h.st.1 hmS hq
  have hf3 : Frame m0 160 slots 8 st3.data :=
    Frame.call_at hf2 hsv3 hrsp3 hs3
      (fun p hp' i hi hq ↦ (hcal _ hq).2 (inRange_off_self (by have := slots_le p hp'; omega)
        (by unfold NativeRustcVm.NoWrap at hfnw; omega)))
      (fun j hj hq ↦ (hcal _ hq).2 (inRange_off_self (by omega)
        (by unfold NativeRustcVm.NoWrap at hfnw; omega)))
  have hl8 := low8_ok h
  have hso : NativeRustcVm.SameOutside st1.data.dmem st3.data.dmem (fun q ↦
      NativeRustcVm.InRange (fbA m0) 8 q ∨
        NativeRustcVm.InRange (stackBelow st2.data ewMulStack) ewMulStack q) :=
    NativeRustcVm.Transcript.SameOutside.trans hs2 hs3
  have hctx3 : Ctx m0 c st3.data :=
    hctx1.step hf3 hso (fun q hq ↦ hq.elim (hl8.1 q) fun hq ↦ Or.inr (hcal q hq).1)
      (fun j hj hq ↦ hq.elim (hl8.2 j hj) fun hq ↦ (hcal _ hq).2
        (inRange_off_self (by omega) (by unfold NativeRustcVm.NoWrap at hfnw; omega)))
  have hnf : ∀ q, NativeRustcVm.InRange (fbA m0) 8 q ∨
      NativeRustcVm.InRange (stackBelow st2.data ewMulStack) ewMulStack q →
      ¬ NativeRustcVm.InRange (rowsA m0) rowsBytes q := fun q hq hr ↦
    hq.elim (fun hq ↦ rows_frame_disj h hr (inRange_mono hq (by decide)))
      fun hq ↦ not_inRange_of_apart h.rowsS h.rows.2 (noWrap_stackBelow h.st) hr
        (inRange_mono (hcal q hq).1 (by omega))
  have hfj : ∀ j, 8 ≤ j → j < 168 → ¬ (NativeRustcVm.InRange (fbA m0) 8 (off (fbA m0) j) ∨
      NativeRustcVm.InRange (stackBelow st2.data ewMulStack) ewMulStack (off (fbA m0) j)) := by
    rintro j hj1 hj2 (hq | hq)
    · have e : (off (fbA m0) j).toNat = (fbA m0).toNat + j := toNat_off (by
        unfold NativeRustcVm.NoWrap at hfnw; omega)
      rw [inRange_iff' (hfnw.mono (by omega)), e] at hq
      omega
    · exact (hcal _ hq).2 (inRange_off_self hj2 (by unfold NativeRustcVm.NoWrap at hfnw; omega))
  refine .done _ ⟨hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.SlotWeights.b13_next), ⟨hctx3, hs, hj, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hc0, hc1, ?_⟩⟩
  · exact bytesAt_congr (hd1 ▸ hI.segw) fun i hi ↦ by
      rw [NativeRustcVm.Transcript.off_add]
      exact hso _ (hfj _ (by omega) (by rw [NativeRustcVm.length_wordBytes] at hi; omega))
  · exact (hsv3.1 .r13 rfl).trans ((hm2.regs .r13 _ hr13').trans ((hm1.regs .r13 _ hr13).trans hI.r13))
  · exact (hsv3.1 .rbp rfl).trans ((hm2.regs .rbp _ hrbp').trans ((hm1.regs .rbp _ hrbp).trans hI.rbp))
  · exact (hsv3.1 .r14 rfl).trans ((hm2.regs .r14 _ hr14').trans ((hm1.regs .r14 _ hr14).trans hI.r14))
  · exact (hsv3.1 .r15 rfl).trans ((hm2.regs .r15 _ hr15').trans ((hm1.regs .r15 _ hr15).trans hI.r15))
  · exact (hsv3.1 .rbx rfl).trans ((hm2.regs .rbx _ hrbx').trans ((hm1.regs .rbx _ hrbx).trans hI.rbx))
  · exact (hsv3.1 .r12 rfl).trans ((hm2.regs .r12 _ hr12').trans ((hm1.regs .r12 _ hr12).trans hrow))
  · exact (hd1 ▸ hI.rows).keep hso (fun q hq hR ↦ hnf q hR hq) h.rows.2

end

end NativeRustcVmX64.KeccakGkr.SlotWeights
