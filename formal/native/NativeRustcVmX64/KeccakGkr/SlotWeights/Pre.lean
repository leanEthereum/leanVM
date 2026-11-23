module

public import NativeRustcVmX64.KeccakGkr.SlotWeights.Defs
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVm.Transcript.Loop

/-!
# `slot_weights`: the precondition's regions (x86-64)

What `SlotWeightsPre` gives the proofs (`PreOk`): the rows, the point, the bit weights and the
stack argument data memory, not wrapping, the rows apart from the stack and the read regions, the
read regions apart from the stack. Then: the frame and the stack argument as a block's regions
(`wf_body`, `match_callS`), the rows' address loaded from the stack argument (`load_rows`), the
weights kept (`weights_keep`).
-/

namespace NativeRustcVmX64.KeccakGkr.SlotWeights

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm (Region)
open NativeRustcVm.Transcript (off inRange_iff' not_inRange_of_apart Mapped.keeps toNat_off
  inRange_off_self)
open NativeRustcVm.KeccakGkr (rowsFlat rowsBytes weightsBytes WeightsAt)

public section

variable {c : KeccakClaimW} {m0 d : MachineData}

/-- **The precondition's regions.** -/
structure PreOk (m0 : MachineData) (c : KeccakClaimW) : Prop where
  st : StackOk m0 slotWeightsStack
  args : NativeRustcVm.Mapped m0.dmem (argA m0) 8 ∧ (rspOf m0).toNat + 8 + 8 ≤ 2 ^ 64
  rows : Region.Ok m0.dmem ⟨rowsA m0, rowsBytes⟩
  pt : Region.Ok m0.dmem (ewsRegion (ptA m0) c.point.size)
  w : Region.Ok m0.dmem ⟨wA m0, weightsBytes⟩
  rowsS : NativeRustcVm.Apart (rowsA m0) rowsBytes (stackBelow m0 slotWeightsStack)
    (slotWeightsStack + 8)
  rowsPt : NativeRustcVm.Apart (rowsA m0) rowsBytes (ptA m0) (16 * c.point.size)
  rowsW : NativeRustcVm.Apart (rowsA m0) rowsBytes (wA m0) weightsBytes
  rowsArg : NativeRustcVm.Apart (rowsA m0) rowsBytes (argA m0) 8
  ptS : NativeRustcVm.Apart (stackBelow m0 slotWeightsStack) (slotWeightsStack + 8) (ptA m0)
    (16 * c.point.size)
  wS : NativeRustcVm.Apart (stackBelow m0 slotWeightsStack) (slotWeightsStack + 8) (wA m0)
    weightsBytes
  sz : c.point.size = (reg m0 .rdx).toNat
  ptAt : NativeRustcVm.EWsAt m0.dmem (ptA m0) c.point.toList
  wAt : WeightsAt m0.dmem (wA m0) c
  fit : SegmentsFit (reg m0 .rdi).toNat c
  cnt1 : 1 ≤ (reg m0 .r9).toNat
  cnt2 : (reg m0 .r8).toNat + (reg m0 .r9).toNat ≤ 2

theorem preOk (h : SlotWeightsPre c m0) : PreOk m0 c := by
  have hst := h.1
  have hargs := h.2.1
  have hA := h.2.2.2.2.2.2.2.2
  have hw : (⟨rowsA m0, rowsBytes⟩ : Region) ∈ [⟨slotRows m0, rowsBytes⟩] := List.mem_singleton.mpr rfl
  have hp : ewsRegion (ptA m0) c.point.size ∈ [ewsRegion (reg m0 .rsi) c.point.size,
      ⟨reg m0 .rcx, weightsBytes⟩, argsRegion m0 1] := List.mem_cons_self
  have hq : (⟨wA m0, weightsBytes⟩ : Region) ∈ [ewsRegion (reg m0 .rsi) c.point.size,
      ⟨reg m0 .rcx, weightsBytes⟩, argsRegion m0 1] := List.mem_cons_of_mem _ List.mem_cons_self
  have ha : argsRegion m0 1 ∈ [ewsRegion (reg m0 .rsi) c.point.size,
      ⟨reg m0 .rcx, weightsBytes⟩, argsRegion m0 1] :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have f1 : NativeRustcVm.Mapped m0.dmem (argA m0) 8 := hargs.1
  have f2 : (rspOf m0).toNat + 8 + 8 ≤ 2 ^ 64 := hargs.2
  have f3 : Region.Ok m0.dmem ⟨rowsA m0, rowsBytes⟩ := Areas.ok hA (List.mem_append_left _ hw)
  have f4 : Region.Ok m0.dmem (ewsRegion (ptA m0) c.point.size) :=
    Areas.ok hA (List.mem_append_right _ hp)
  have f5 : Region.Ok m0.dmem ⟨wA m0, weightsBytes⟩ := Areas.ok hA (List.mem_append_right _ hq)
  have f6 := Areas.apart_stack hA hw
  have f7 := Areas.apart_read hA hw hp
  have f8 := Areas.apart_read hA hw hq
  have f9 := Areas.apart_read hA hw ha
  have f10 := Areas.stack_read hA hp
  have f11 := Areas.stack_read hA hq
  have g1 := h.2.2.1
  have g2 := h.2.2.2.1
  have g3 := h.2.2.2.2.1
  have g4 := h.2.2.2.2.2.1
  have g5 := h.2.2.2.2.2.2.1
  have g6 := h.2.2.2.2.2.2.2.1
  exact ⟨hst, ⟨f1, f2⟩, f3, f4, f5, f6, f7, f8, f9, f10, f11, g1, g2, g3, g4, g5, g6⟩

theorem keccakSegments_eq : LeanVM.Protocol.Verifier.keccakSegments = 2 := rfl

theorem argA_toNat (h : PreOk m0 c) : (argA m0).toNat = (rspOf m0).toNat + 8 := by
  have := h.args.2
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The frame's base as a number. -/
theorem fbA_toNat (h : PreOk m0 c) : (fbA m0).toNat = (rspOf m0).toNat - 160 :=
  stackBelow_toNat (by have := h.st.1; unfold slotWeightsStack eqKernelStack ewMulStack at this; omega)

/-- The frame's region and the stack argument's are a block's regions. -/
theorem wf_body (h : PreOk m0 c) (hk : Kept m0.dmem d.dmem) {vars : Nat → BitVec 64}
    {ret : BitVec 64} : (frameEnv m0 d 160 [(argA m0, 8)] vars ret).WF := by
  have h1 := argA_toNat h
  have h2 := fbA_toNat h
  have hs := h.st.1
  unfold slotWeightsStack eqKernelStack ewMulStack at hs
  refine frame_wf ⟨Mapped.keeps (frame_mapped h.st (by decide)) hk, frame_noWrap h.st (by decide)⟩
    (fun x hx ↦ ?_) (List.pairwise_pair.mpr ?_)
  · rw [List.mem_singleton] at hx
    subst hx
    exact ⟨Mapped.keeps h.args.1 hk, by show (argA m0).toNat + 8 ≤ 2 ^ 64; have := h.args.2; omega⟩
  · show (fbA m0).toNat + (160 + 8) ≤ (argA m0).toNat ∨ _
    omega

/-- The stack argument's region: the frame's offset `168`. -/
theorem arg_alias [Labels] {vars : Nat → BitVec 64} {ret : BitVec 64} :
    (Sym.ptr 0 168).eval (frameEnv m0 d 160 [(argA m0, 8)] vars ret) =
      (frameEnv m0 d 160 [(argA m0, 8)] vars ret).base 1 + BitVec.ofInt 64 0 := by
  rw [show (Sym.ptr 0 168) = Sym.ptr 0 ((168 : Nat) : Int) from rfl, eval_ptr0,
    show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
  exact frame_add 160 8

/-- The body's start in a frame. -/
theorem match_callS [Labels] (hf : Frame m0 160 slots 8 d) {vars : Nat → BitVec 64}
    {ret : BitVec 64} : Match (frameEnv m0 d 160 [(argA m0, 8)] vars ret) callS d :=
  match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf.rsp_eval, trivial⟩ trivial trivial ⟨arg_alias, trivial⟩

/-- The stack argument's bytes are the entry's in a state changed only in `Out`. -/
theorem arg_keep (h : PreOk m0 c) (hs : NativeRustcVm.SameOutside m0.dmem d.dmem (Out m0)) :
    ∀ i < 8, d.dmem.get? (argA m0 + BitVec.ofNat 64 i) = m0.dmem.get? (argA m0 + BitVec.ofNat 64 i) := by
  intro i hi
  have hA : (argA m0).toNat + 8 ≤ 2 ^ 64 := by
    have e := argA_toNat h
    have := h.args.2
    omega
  have hq : NativeRustcVm.InRange (argA m0) 8 (off (argA m0) i) :=
    NativeRustcVm.Transcript.inRange_off_self hi (by omega)
  refine hs _ fun hO ↦ ?_
  rcases hO with hO | hO
  · exact not_inRange_of_apart h.rowsArg h.rows.2 hA hO hq
  · have hS := noWrap_stackBelow h.st
    have hsb := stackBelow_toNat (m := m0) (n := slotWeightsStack) h.st.1
    have e := argA_toNat h
    rw [inRange_iff' (hS.mono (by omega))] at hO
    have e2 : (argA m0 + BitVec.ofNat 64 i).toNat = (argA m0).toNat + i :=
      NativeRustcVm.Transcript.toNat_off (by omega)
    have hs1 := h.st.1
    rw [e2, hsb] at hO
    omega

/-- The stack's bottom as a number. -/
theorem sb_toNat (h : PreOk m0 c) :
    (stackBelow m0 slotWeightsStack).toNat = (rspOf m0).toNat - slotWeightsStack :=
  stackBelow_toNat h.st.1

/-- A byte of the frame or the return address is not in the rows. -/
theorem rows_not_frame (h : PreOk m0 c) {o n j : Nat} (hn : 0 < n) (hon : o + n ≤ rowsBytes)
    (hj : j < 168) :
    ¬ NativeRustcVm.InRange (off (rowsA m0) o) n (off (fbA m0) j) := by
  intro hq
  have hS := h.rowsS
  have hr := h.rows.2
  have hsb := sb_toNat h
  have hfb := fbA_toNat h
  have hst := h.st.1
  have h8 := h.st.2.1
  unfold NativeRustcVm.Apart at hS
  unfold NativeRustcVm.NoWrap at hr
  simp only [rowsBytes, slotWeightsStack, eqKernelStack, ewMulStack] at hS hr hon hsb hst
  have e1 : (off (rowsA m0) o).toNat = (rowsA m0).toNat + o := toNat_off (by omega)
  have e2 : (off (fbA m0) j).toNat = (fbA m0).toNat + j := toNat_off (by omega)
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), e1, e2] at hq
  omega

/-- The rows and the frame with the return address share no byte. -/
theorem rows_frame_disj (h : PreOk m0 c) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (rowsA m0) rowsBytes q) :
    ¬ NativeRustcVm.InRange (fbA m0) (160 + 8) q := fun hq' ↦
  not_inRange_of_apart (apart_frame h.rowsS h.st.1 (by decide)) h.rows.2
    (frame_noWrap h.st (by decide)) hq hq'

/-- **The bit weights kept** in a state changed only in `Out`. -/
theorem weights_keep (h : PreOk m0 c) (hs : NativeRustcVm.SameOutside m0.dmem d.dmem (Out m0)) :
    WeightsAt d.dmem (wA m0) c := by
  refine ⟨h.wAt.1, NativeRustcVm.Transcript.bytesAt_congr h.wAt.2 fun i hi ↦ hs _ ?_⟩
  have hl : (c.weights.toList.flatMap NativeRustcVm.ewBytes).length = 25600 := by
    rw [NativeRustcVm.Transcript.length_flatMap_ewBytes, Array.length_toList, h.wAt.1]; rfl
  rw [hl] at hi
  have hw : (wA m0).toNat + 25600 ≤ 2 ^ 64 := h.w.2
  have hq : NativeRustcVm.InRange (wA m0) weightsBytes (wA m0 + BitVec.ofNat 64 i) :=
    inRange_off_self (N := 25600) hi (by omega)
  rintro (hO | hO)
  · exact not_inRange_of_apart (Apart.symm' h.rowsW) h.w.2 h.rows.2 hq hO
  · exact not_inRange_of_apart (Apart.symm' h.wS) h.w.2 (noWrap_stackBelow h.st) hq
      (inRange_mono hO (by omega))

/-- **The rows' address**, loaded from the stack argument. -/
theorem load_rows [Labels] (h : PreOk m0 c) (hs : NativeRustcVm.SameOutside m0.dmem d.dmem (Out m0))
    {vars : Nat → BitVec 64} {ret : BitVec 64} :
    (frameEnv m0 d 160 [(argA m0, 8)] vars ret).load 1 0 8 = rowsA m0 := by
  have hw : NativeRustcVm.WordAt m0.dmem (argA m0) (UInt64.ofBitVec (rowsA m0)) := by
    have e : UInt64.ofBitVec (rowsA m0) = NativeRustcVm.wordOf m0.dmem (argA m0) :=
      UInt64.ofBitVec_toBitVec _
    rw [e]
    exact NativeRustcVm.wordAt_of_mapped h.args.1
  have hw' : NativeRustcVm.WordAt d.dmem (argA m0) (UInt64.ofBitVec (rowsA m0)) :=
    NativeRustcVm.Transcript.bytesAt_congr hw fun i hi ↦ arg_keep h hs i
      (by rw [NativeRustcVm.length_wordBytes] at hi; exact hi)
  have := load_of_wordAt (env := frameEnv m0 d 160 [(argA m0, 8)] vars ret) (r := 1) (o := 0)
    (w := UInt64.ofBitVec (rowsA m0))
    (by
      show NativeRustcVm.WordAt d.dmem (argA m0 + BitVec.ofNat 64 0) _
      rw [NativeRustcVm.addr_add_zero]
      exact hw')
  rw [this]

end

end NativeRustcVmX64.KeccakGkr.SlotWeights
