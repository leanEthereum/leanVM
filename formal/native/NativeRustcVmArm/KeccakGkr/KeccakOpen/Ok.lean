module

public import NativeRustcVmArm.KeccakGkr.KeccakOpen.Known

/-!
# `keccak_open`: what the precondition gives

`Ok` (`ok_of`); the round constants as numbers (`RcN`, `rcN_of`); the stack arguments' words
(`arg_word`); the callees' stacks below the frame (`callee_toNat`); a `TState` kept by a change
in the function's stack and the other outputs (`Free`, `ts_keep`); a register a block copied
(`regEq`).
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakOpen

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Arrays
open LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeRustcVm (Region InAny)
open NativeRustcVm.Transcript (DecArea tstateBytes TStateAt)
open NativeRustcVm.KeccakGkr (rowsBytes weightsBytes)

@[expose] public section

/-- The round constants as numbers: not wrapping, apart from the stack, the `TState` and the
slot point. -/
structure RcN [Labels] (m0 : MachineData) : Prop where
  w : rcAddr.toNat + 192 ≤ 2 ^ 64
  st : rcAddr.toNat + 192 ≤ spN m0 - 3104 ∨ spN m0 ≤ rcAddr.toNat
  t : (tA m0).toNat + 760 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ (tA m0).toNat
  s : (slA m0).toNat + 96 ≤ rcAddr.toNat ∨ rcAddr.toNat + 192 ≤ (slA m0).toNat

/-- The bytes a change keeping the `TState` may touch: the function's stack, the result, the
slot point, the rows. -/
def Free (m0 : MachineData) (q : BitVec 64) : Prop :=
  (spN m0 - 3104 ≤ q.toNat ∧ q.toNat < spN m0) ∨
    ((oA m0).toNat ≤ q.toNat ∧ q.toNat < (oA m0).toNat + 24) ∨
    ((slA m0).toNat ≤ q.toNat ∧ q.toNat < (slA m0).toNat + 96) ∨
    ((rwA m0).toNat ≤ q.toNat ∧ q.toNat < (rwA m0).toNat + 65536)

end

public section

variable [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 st st' : MachineData}

omit [Labels] in
theorem mem_slot : ewsRegion (openSlot m0) qkeccakSlotBits ∈ wsOf m0 :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

omit [Labels] in
theorem mem_rows : (⟨openRows m0, rowsBytes⟩ : Region) ∈ wsOf m0 :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

omit [Labels] in
theorem mem_ts : (⟨tA m0, tstateBytes⟩ : Region) ∈ wsOf m0 :=
  List.mem_cons_of_mem _ List.mem_cons_self

omit [Labels] in
theorem mem_out : (⟨oA m0, 24⟩ : Region) ∈ wsOf m0 := List.mem_cons_self

theorem mem_args : (⟨m0.regs.SP.toBitVec, 32⟩ : Region) ∈ rsOf a c m0 :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self)))

theorem mem_rc : rcRegion ∈ rsOf a c m0 :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

/-- **What the precondition gives every step.** -/
theorem ok_of (h : KeccakOpenPre a s c m0) : Ok a m0 := by
  have hA := pre_areas h
  have h2 := (Areas.ok hA (.inl (mem_slot (m0 := m0)))).1
  have h3 := (Areas.ok hA (.inl (mem_rows (m0 := m0)))).1
  exact ⟨nums_of h, h.1, h2, h3, wsOff h⟩

/-- **The round constants as numbers.** -/
theorem rcN_of (h : KeccakOpenPre a s c m0) : RcN m0 := by
  have hA := pre_areas h
  have hN : 3104 ≤ spN m0 := (nums_of h).hN
  obtain ⟨-, hw, hs⟩ := h.2.1
  have ht := Areas.apart_rs hA (mem_ts (m0 := m0)) (mem_rc (a := a) (c := c))
  have hsl := Areas.apart_rs hA (mem_slot (m0 := m0)) (mem_rc (a := a) (c := c))
  unfold Apart at hs ht hsl
  rw [stackBelow_nat hN, stack_eq] at hs
  have es : (ewsRegion (openSlot m0) qkeccakSlotBits).size = 96 := by
    show 16 * qkeccakSlotBits = 96
    rw [slotBits_eq]
  rw [es] at hsl
  exact ⟨hw, by omega, ht, hsl⟩

/-- **A word of the stack arguments**, kept in a body. -/
theorem arg_word (h : KeccakOpenPre a s c m0) (hb : Body m0 st) {o : Nat} (ho : o + 8 ≤ 32) :
    NativeRustcVm.WordAt st.dmem (fbA m0 + BitVec.ofNat 64 (2224 + o))
      (NativeRustcVm.wordOf m0.dmem (m0.regs.SP.toBitVec + BitVec.ofNat 64 o)) := by
  have hA := pre_areas h
  have hr := mem_args (a := a) (c := c) (m0 := m0)
  have hm := NativeRustcVm.Mapped.sub (Areas.ok hA (.inr hr)).1 (o := o) (m := 8) ho
  have h1 := hb.bytesAt hA h.1 hr (o := o) (by rw [NativeRustcVm.length_wordBytes]; exact ho)
    (NativeRustcVm.wordAt_of_mapped hm)
  rwa [← NativeRustcVm.addr_add_add,
    show fbA m0 + BitVec.ofNat 64 2224 = m0.regs.SP.toBitVec from BitVec.sub_add_cancel _ _]

/-- The stack arguments' 32 bytes and the frame: data memory, not wrapping. -/
theorem arg_ok (h : KeccakOpenPre a s c m0) (hb : Body m0 st) :
    Mapped st.dmem (fbA m0) 2256 ∧ NoWrap (fbA m0) 2256 := by
  have hA := pre_areas h
  have hn := nums_of h
  obtain ⟨hmap, -, hfb⟩ := frame_ok h.1 (show 2224 ≤ keccakOpenStack by rw [stack_eq]; omega)
  have ha := (Areas.ok hA (.inr (mem_args (a := a) (c := c) (m0 := m0)))).1
  refine ⟨NativeRustcVm.mapped_append_iff (n := 2224) (m := 32).mpr
    ⟨Mapped.kept' hmap hb.kept, ?_⟩, ?_⟩
  · rw [show fbA m0 + BitVec.ofNat 64 2224 = m0.regs.SP.toBitVec from BitVec.sub_add_cancel _ _]
    exact Mapped.kept' ha hb.kept
  · have := hn.argW; have := hn.hN
    show (fbA m0).toNat + 2256 ≤ 2 ^ 64
    rw [hfb]
    unfold spN at *
    omega

/-- **A callee's stack** below a body's SP, as a number. -/
theorem callee_toNat (ok : Ok a m0) (hb : Body m0 st) {n : Nat} (hn : n ≤ 880) :
    (stackBelow st n).toNat = spN m0 - 2224 - n := by
  have hN := ok.nums.hN
  have e : st.regs.SP.toNat = spN m0 - 2224 :=
    hb.sp_toNat ok.stack (by rw [stack_eq]; omega)
  rw [Sumcheck.toNat_stackBelow (by rw [e]; omega), e]

omit [Labels] in
/-- **The `TState` kept** by a change in `Free` bytes. -/
theorem ts_keep (hn : Nums a m0) {s' : TState} (h : TStateAt st.dmem (tA m0) a s')
    (hk : Kept st.dmem st'.dmem) {R : BitVec 64 → Prop} (hs : SameOutside st.dmem st'.dmem R)
    (hR : ∀ q, R q → Free m0 q) : TStateAt st'.dmem (tA m0) a s' := by
  refine h.frame hk (fun q hq ↦ ?_) hs
  have hq' := hR q hq
  unfold Free at hq'
  have := hn.tW; have := hn.tS; have := hn.o_t; have := hn.t_s; have := hn.t_r
  have := hn.wW; have := hn.wS; have := hn.o_w; have := hn.s_w; have := hn.r_w
  have et : tstateBytes = 760 := rfl
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [NativeRustcVm.Transcript.inRange_iff' (show NativeRustcVm.NoWrap (tA m0) tstateBytes
      by unfold NativeRustcVm.NoWrap; rw [et]; omega), et] at h
    omega
  · rw [NativeRustcVm.Transcript.inRange_iff' (show NativeRustcVm.NoWrap a.words (8 * a.len)
      from hn.wW)] at h
    omega

/-- A register a block copied from another. -/
theorem regEq {rs : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64} {S : SState} {r r' : XReg}
    (hm : Match (Env.ofMachine st rs vars) S st') (h : S.reg r = some (.reg r')) :
    st'.regs.getXReg r = st.regs.getXReg r' :=
  UInt64.toBitVec_inj.mp (hm.regs r _ h)

omit [Labels] in
/-- A byte of the frame is `Free`. -/
theorem free_frame (hn : Nums a m0) {q : BitVec 64} (h : InRange (fbA m0) 2224 q) :
    Free m0 q := by
  have hN := hn.hN
  have hlt := m0.regs.SP.toBitVec.isLt
  have hf := fb_toNat (m0 := m0) (by omega)
  unfold spN at hN hf
  rw [inRange_nat (by rw [hf]; omega), hf] at h
  unfold Free spN
  exact .inl ⟨by omega, by omega⟩

end

end NativeRustcVmArm.KeccakGkr.KeccakOpen
