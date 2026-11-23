module

public import NativeRustcVmArm.Code.Vm.SlotWeights.Names
public import NativeRustcVmArm.KeccakGkr.KeccakOpen.Exit
public import NativeRustcVm.Top.Phases

/-!
# `keccak_open`: the slot weights

`Some` from the plain sumcheck: `b1` falls through, `b2` loads its value and the rows' address
and calls `slot_weights(logSteps, point, len, weights, first, count, rows)`, `b3` sees it
succeed; the state is `Sw` at `b4` (`sw_run`). Memory changes on the way only in the function's
stack and the rows (`Low`).
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakOpen

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Arrays
open NativeRustcVmArm.Vm.KeccakOpen
open LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeRustcVm (Region InAny)
open NativeRustcVm.Transcript (DecArea tstateBytes TStateAt)
open NativeRustcVm.KeccakGkr (rowsFlat rowsBytes weightsBytes WeightsAt)

@[expose] public section

/-- The bytes the steps before the fold change: the function's stack, the rows. -/
def Low (m0 : MachineData) (q : BitVec 64) : Prop :=
  (spN m0 - 3104 ≤ q.toNat ∧ q.toNat < spN m0) ∨
    ((rwA m0).toNat ≤ q.toNat ∧ q.toNat < (rwA m0).toNat + 65536)

/-- The slot weights. -/
abbrev swOf (c : KeccakClaimW) (m0 : MachineData) : Array (Array EW) :=
  keccakSlotWeights m0.regs.X2.toNat c m0.regs.X6.toNat m0.regs.X7.toNat

/-- **After `slot_weights`**, at `b4`. -/
structure Sw [Labels] (a : DecArea) (c : KeccakClaimW) (m0 : MachineData) (s1 : TState)
    (sl : Array EW) (v : EW) (st : MachineData) : Prop where
  body : Body m0 st
  x19 : st.regs.X19 = m0.regs.X0
  x20 : st.regs.X20 = v.c1
  x21 : st.regs.X21 = v.c0
  x28 : st.regs.X28.toBitVec = slA m0
  x29 : st.regs.X29.toBitVec = rwA m0
  sl_size : sl.size = 6
  slot : NativeRustcVm.EWsAt st.dmem (slA m0) sl.toList
  ts : TStateAt st.dmem (tA m0) a s1
  rows : NativeRustcVm.EWsAt st.dmem (rwA m0) (rowsFlat (swOf c m0))

end

public section

variable {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 : MachineData}

theorem sw_le : slotWeightsStack ≤ 880 := by
  have := stack_eq
  unfold keccakOpenStack at this
  omega

/-- Two changes in `R`. -/
theorem same_trans {d d' d'' : DataMem} {R : BitVec 64 → Prop} (h : SameOutside d d' R)
    (h' : SameOutside d' d'' R) : SameOutside d d'' R :=
  fun p hp ↦ (h' p hp).trans (h p hp)

theorem same_mono {d d' : DataMem} {R R' : BitVec 64 → Prop} (h : SameOutside d d' R)
    (hR : ∀ q, R q → R' q) : SameOutside d d' R' :=
  fun p hp ↦ h p fun h' ↦ hp (hR p h')

/-- The slot point is not `Low`. -/
theorem not_low_slot (hn : Nums a m0) {i : Nat} (hi : i < 96) :
    ¬Low m0 (slA m0 + BitVec.ofNat 64 i) := fun h ↦ by
  have := hn.sW; have := hn.sS; have := hn.s_r
  rw [Low, toNat_add_ofNat' (by omega)] at h
  omega

variable [Host] {k : Nat}

/-- **`Some` from the plain sumcheck, the slot weights**: from `b1` to `b4`. -/
theorem sw_run (hp : Placed code k) (h : KeccakOpenPre a s c m0)
    (hsw : ∀ c, Spec (label NativeRustcVmArm.Vm.SlotWeights.entryLabel) (SlotWeightsPre c) (SlotWeightsPost c))
    {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b1Offset)) (hsc : Sc a s m0 st.data)
    {s1 : TState} {sl : Array EW} {v : EW} (hrun : scRun s m0 = some ((sl, v), s1)) :
    Eventually (step1 Host.exe)
      (fun st' ↦ st'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b4Offset) ∧ Sw a c m0 s1 sl v st'.data) st := by
  have ok := ok_of h
  have hn := ok.nums
  have hS := h.1
  have hA := pre_areas h
  have hN := hn.hN
  have hlt : spN m0 < 2 ^ 64 := m0.regs.SP.toBitVec.isLt
  have hws := wsOff h
  have hout := hsc.out.1
  rw [hrun] at hout
  obtain ⟨htag, hval⟩ := hout
  have hval' := NativeRustcVm.ewAt_iff.mp hval
  rw [NativeRustcVm.Transcript.off, NativeRustcVm.addr_add_add,
    NativeRustcVm.addr_add_add] at hval'
  have hsl0 := hsc.out.2.1 sl v s1 hrun
  have hts0 := hsc.out.2.2 _ s1 hrun
  have hsize : sl.size = 6 := by
    have := (NativeRustcVm.Top.sumcheck_size (openValue m0) 3
      (Array.replicate qkeccakSlotBits none)).gives s _ s1 hrun
    simpa [slotBits_eq] using this
  -- `b1`: `Some`
  obtain ⟨hwf, hm⟩ := argS_match h hsc.body
  refine exec_at (b1_in_code.trans hp.1 (by simp [b1])) run_b1 hwf hpc hm fun s1' hm1 hpc1 ↦ ?_
  have hl := Sumcheck.load_word (env := Env.ofMachine st.data [(fbA m0, 2256)]) (r := 0)
    (off := 56) htag
  have hpc1' := pc_false hpc1 (by
    show CmpOp.apply .eq .W64 ((Env.ofMachine st.data [(fbA m0, 2256)]).load 0 56 8) _ = false
    rw [hl]
    rfl)
  have hb1 : Body m0 s1'.data := hsc.body.of_block hm hm1 hwf rfl all_slots (by decide)
  have hd1 : s1'.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have k1 : ∀ r, calleeSaved r = true → s1'.data.regs.getXReg r = st.data.regs.getXReg r :=
    fun r hr ↦ regEq hm1 (by cases r <;> first | rfl | exact absurd hr (by decide))
  -- `b2`: the call of `slot_weights`
  obtain ⟨hwf2, hm2⟩ := argS_match h hb1
  refine exec_at (b2_in_code.trans hp.1 (by simp [b2])) run_b2 hwf2 hpc1' hm2
    fun s2 hm2' hpc2 ↦ ?_
  have hb2 : Body m0 s2.data := hb1.of_block hm2 hm2' hwf2 rfl all_slots (by decide)
  have hd2 : s2.data.dmem = st.data.dmem := (hm2'.dmem_eq hwf2 rfl).trans hd1
  have w24 : NativeRustcVm.WordAt s1'.data.dmem (fbA m0 + BitVec.ofNat 64 2248)
      (UInt64.ofBitVec (rwA m0)) := arg_word h hb1 (o := 24) (by decide)
  have y0 : s2.data.regs.X0 = m0.regs.X2 :=
    (regEq (r := .X0) (r' := .X27) hm2' rfl).trans ((k1 .X27 rfl).trans hsc.x27)
  have y1 : s2.data.regs.X1 = m0.regs.X3 :=
    (regEq (r := .X1) (r' := .X26) hm2' rfl).trans ((k1 .X26 rfl).trans hsc.x26)
  have y2 : s2.data.regs.X2 = m0.regs.X4 :=
    (regEq (r := .X2) (r' := .X25) hm2' rfl).trans ((k1 .X25 rfl).trans hsc.x25)
  have y3 : s2.data.regs.X3 = m0.regs.X5 :=
    (regEq (r := .X3) (r' := .X24) hm2' rfl).trans ((k1 .X24 rfl).trans hsc.x24)
  have y4 : s2.data.regs.X4 = m0.regs.X6 :=
    (regEq (r := .X4) (r' := .X23) hm2' rfl).trans ((k1 .X23 rfl).trans hsc.x23)
  have y5 : s2.data.regs.X5 = m0.regs.X7 :=
    (regEq (r := .X5) (r' := .X22) hm2' rfl).trans ((k1 .X22 rfl).trans hsc.x22)
  have y6 : s2.data.regs.X6.toBitVec = rwA m0 :=
    (hm2'.regs .X6 _ rfl).trans (Sumcheck.load_word w24)
  have y29 : s2.data.regs.X29.toBitVec = rwA m0 :=
    (hm2'.regs .X29 _ rfl).trans (Sumcheck.load_word w24)
  have w64 : NativeRustcVm.WordAt s1'.data.dmem (fbA m0 + BitVec.ofNat 64 64) v.c0 := by
    rw [hd1]; exact hval'.1
  have w72 : NativeRustcVm.WordAt s1'.data.dmem (fbA m0 + BitVec.ofNat 64 72) v.c1 := by
    rw [hd1]; exact hval'.2
  have y20 : s2.data.regs.X20 = v.c1 := UInt64.toBitVec_inj.mp ((hm2'.regs .X20 _ rfl).trans
    (Sumcheck.load_word w72))
  have y21 : s2.data.regs.X21 = v.c0 := UInt64.toBitVec_inj.mp ((hm2'.regs .X21 _ rfl).trans
    (Sumcheck.load_word w64))
  have y19 : s2.data.regs.X19 = m0.regs.X0 :=
    (regEq (r := .X19) (r' := .X19) hm2' rfl).trans ((k1 .X19 rfl).trans hsc.x19)
  have y28 : s2.data.regs.X28.toBitVec = slA m0 := by
    rw [← hsc.x28]
    exact congrArg UInt64.toBitVec ((regEq (r := .X28) (r' := .X28) hm2' rfl).trans
      (k1 .X28 rfl))
  -- `slot_weights`'s precondition
  have hswN := sw_le
  have hcs := callee_toNat ok hb2 hswN
  have hpt : ewsRegion m0.regs.X3.toBitVec c.point.size ∈ rsOf a c m0 :=
    List.mem_cons_of_mem _ List.mem_cons_self
  have hwt : (⟨m0.regs.X5.toBitVec, weightsBytes⟩ : Region) ∈ rsOf a c m0 :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hptO := Areas.ok hA (.inr hpt)
  have hwtO := Areas.ok hA (.inr hwt)
  have hrO := Areas.ok hA (.inl (mem_rows (m0 := m0)))
  have sptN := Areas.stack_rs hA hpt
  have swtN := Areas.stack_rs hA hwt
  have rpt := Areas.apart_rs hA (mem_rows (m0 := m0)) hpt
  have rwt := Areas.apart_rs hA (mem_rows (m0 := m0)) hwt
  unfold Apart at sptN swtN
  rw [stackBelow_nat hN, stack_eq] at sptN swtN
  have := hn.rW; have := hn.rS
  have er : rowsBytes = 65536 := rfl
  have ptA : NativeRustcVm.EWsAt s2.data.dmem m0.regs.X3.toBitVec c.point.toList := by
    have h0 := h.2.2.2.2.1
    rw [← NativeRustcVm.addr_add_zero m0.regs.X3.toBitVec] at h0
    have := hb2.bytesAt hA hS hpt (o := 0)
      (by show 0 + _ ≤ 16 * c.point.size
          rw [NativeRustcVm.length_ewsBytes, Array.length_toList]; omega) h0
    rwa [NativeRustcVm.addr_add_zero] at this
  have wtA : WeightsAt s2.data.dmem m0.regs.X5.toBitVec c := by
    obtain ⟨hw1, hw2⟩ := h.2.2.2.2.2.1
    refine ⟨hw1, ?_⟩
    rw [← NativeRustcVm.addr_add_zero m0.regs.X5.toBitVec] at hw2
    have := hb2.bytesAt hA hS hwt (o := 0)
      (by show 0 + _ ≤ 25600
          rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hw1]; decide) hw2
    rwa [NativeRustcVm.addr_add_zero] at this
  refine call_then hpc2 (hsw c) ⟨hb2.stackOk hS (by decide) (by rw [stack_eq]; omega),
    by rw [y2]; exact h.2.2.2.1, by rw [y1]; exact ptA, by rw [y3]; exact wtA,
    by rw [y0]; exact h.2.2.2.2.2.2.1, by rw [y5]; exact h.2.2.2.2.2.2.2.1,
    by rw [y4, y5]; exact h.2.2.2.2.2.2.2.2.1, ⟨?_, ?_, ?_⟩⟩ fun s3 hpc3 hpost3 ↦ ?_
  · intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [y6]; exact ⟨Mapped.kept' hrO.1 hb2.kept, hrO.2⟩
    · rw [y1]; exact ⟨Mapped.kept' hptO.1 hb2.kept, hptO.2⟩
    · rw [y3]; exact ⟨Mapped.kept' hwtO.1 hb2.kept, hwtO.2⟩
  · refine NativeRustcVm.disjoint_cons_iff.mpr ⟨fun r hr ↦ ?_, List.pairwise_singleton _ _⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    show Apart (stackBelow s2.data slotWeightsStack) slotWeightsStack
      s2.data.regs.X6.toBitVec rowsBytes
    unfold Apart
    rw [hcs, y6, er]
    omega
  · intro w hw r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw hr
    rw [y1, y3] at hr
    rcases hw with rfl | rfl <;> rcases hr with rfl | rfl
    · show Apart (stackBelow s2.data slotWeightsStack) slotWeightsStack _ _
      unfold Apart; rw [hcs]; omega
    · show Apart (stackBelow s2.data slotWeightsStack) slotWeightsStack _ _
      unfold Apart; rw [hcs]; omega
    · rw [y6]; exact rpt
    · rw [y6]; exact rwt
  obtain ⟨hx0, hrows, hsame3, hsv3⟩ := hpost3
  rw [y6, y0, y4, y5] at hrows
  have hR3 : ∀ q, InAny (stackRegion s2.data slotWeightsStack ::
      [⟨s2.data.regs.X6.toBitVec, rowsBytes⟩]) q →
      InRange (stackBelow s2.data slotWeightsStack) slotWeightsStack q ∨ InAny (wsOf m0) q := by
    rintro q ⟨r, hr, hq⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl hq
    · rw [y6] at hq; exact .inr ⟨_, mem_rows, hq⟩
  have hb3 : Body m0 s3.data :=
    hb2.call (n := slotWeightsStack) hS (by rw [stack_eq]; omega) slots_le' hws hsame3 hR3 hsv3
  have hlow3 : SameOutside s2.data.dmem s3.data.dmem (Low m0) := same_mono hsame3 fun q hq ↦ by
    obtain ⟨r, hr, hq⟩ := hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have hq' : InRange (stackBelow s2.data slotWeightsStack) slotWeightsStack q := hq
      rw [inRange_nat (by rw [hcs]; omega), hcs] at hq'
      exact .inl ⟨by omega, by omega⟩
    · have hq' : InRange s2.data.regs.X6.toBitVec rowsBytes q := hq
      rw [y6, er] at hq'
      exact .inr ((inRange_nat (by omega)).mp hq')
  have hk3 : Kept st.data.dmem s3.data.dmem := fun p hp ↦ hsv3.2.2 p (by rw [hd2]; exact hp)
  have hlow : SameOutside st.data.dmem s3.data.dmem (Low m0) := by rw [← hd2]; exact hlow3
  -- `b3`: `slot_weights` succeeded
  refine exec_at (b3_in_code.trans hp.1 (by simp [b3])) run_b3 (Env.wf_nil _) hpc3
    (match_nil _) fun s4 hm4 hpc4 ↦ .done _ ⟨?_, ?_⟩
  · refine pc_false hpc4 ?_
    show (!(Sym.low .W32 (s3.data.regs.getXReg .X0).toBitVec).getLsbD 0) = false
    rw [show s3.data.regs.getXReg .X0 = 1 from hx0]
    rfl
  have hd4 : s4.data.dmem = s3.data.dmem := hm4.dmem_eq (Env.wf_nil _) rfl
  have k4 : ∀ r, calleeSaved r = true → s4.data.regs.getXReg r = s2.data.regs.getXReg r :=
    fun r hr ↦ (regEq hm4 (by cases r <;> rfl)).trans (hsv3.1 r hr)
  refine ⟨hb3.of_block (match_nil _) hm4 (Env.wf_nil _) rfl all_slots (by decide),
    (k4 .X19 rfl).trans y19, (k4 .X20 rfl).trans y20, (k4 .X21 rfl).trans y21,
    by rw [← y28]; exact congrArg UInt64.toBitVec (k4 .X28 rfl),
    by rw [← y29]; exact congrArg UInt64.toBitVec (k4 .X29 rfl), hsize, ?_, ?_, ?_⟩
  · rw [hd4]
    refine NativeRustcVm.BytesAt.of_sameOutside hsl0 hlow fun i hi ↦ ?_
    rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hsize] at hi
    exact not_low_slot hn hi
  · rw [hd4]
    exact ts_keep hn hts0 hk3 hlow fun q hq ↦ by
      rcases hq with hq | hq
      · exact .inl hq
      · exact .inr (.inr (.inr hq))
  · rw [hd4]; exact hrows

end

end NativeRustcVmArm.KeccakGkr.KeccakOpen
