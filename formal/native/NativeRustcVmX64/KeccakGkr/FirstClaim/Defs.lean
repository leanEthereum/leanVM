module

public import NativeRustcVmX64.KeccakGkr.Common
public import NativeRustcVmX64.KeccakGkr.FirstClaim.Exec
public import NativeRustcVm.Arrays.ReadLemmas
public import NativeRustcVm.Transcript.Loop
public import NativeVm.Math.Keccak.FirstClaim

/-!
# `first_claim`: the body's context (x86-64)

The arguments (`outA` the result, `wA` the bit weights, the stack argument words at `argA`), the
frame's base `fbA` (1376 bytes below the entry's RSP), what the function may change (`Out`: the
result, the bit weights, its stack), the stack below the frame its callees use (`Low`), the body
(`Body`: the frame, memory changed only in `Out`). The precondition's facts (`PreOk`) and its
addresses as numbers (`Nums`). Then: the regions of a block (`wf_body`, `match_callS`), the stack
argument words loaded (`load_arg`), a call from the body (`call_body`), bytes kept across a block
or a call (`keep_loc`, `keep_ext`).
-/

namespace NativeRustcVmX64.KeccakGkr.FirstClaim

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open NativeRustcVm (Region)
open NativeRustcVm.Transcript (off off_zero off_off toNat_off inRange_iff' Mapped.keeps
  bytesAt_congr inRange_off_self Touch)
open NativeRustcVm.KeccakGkr (claimBytes weightsBytes)

@[expose] public section

/-- The result. -/
abbrev outA (m0 : MachineData) : BitVec 64 := reg m0 .rdi
/-- The bit weights. -/
abbrev wA (m0 : MachineData) : BitVec 64 := firstWeights m0
/-- The frame's base. -/
abbrev fbA (m0 : MachineData) : BitVec 64 := stackBelow m0 1376
/-- The stack argument words. -/
abbrev argA (m0 : MachineData) : BitVec 64 := rspOf m0 + 8#64

/-- What the function may change: the result, the bit weights and its stack. -/
def Out (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange (outA m0) 776 q ∨ NativeRustcVm.InRange (wA m0) 25600 q ∨
    NativeRustcVm.InRange (stackBelow m0 firstClaimStack) firstClaimStack q

/-- A byte of the stack the function uses, or its return address. -/
def Stk (m0 : MachineData) (q : BitVec 64) : Prop :=
  (rspOf m0).toNat - 1632 ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat + 8

/-- The stack below the frame (the callees'). -/
def Low (m0 : MachineData) (q : BitVec 64) : Prop :=
  NativeRustcVm.InRange (stackBelow m0 firstClaimStack) 256 q

/-- **The body**: the frame, memory changed only in `Out`. -/
structure Body (m0 st : MachineData) : Prop where
  frame : Frame m0 1376 slots 8 st
  same : NativeRustcVm.SameOutside m0.dmem st.dmem (Out m0)

/-- The regions `first_claim` writes. -/
abbrev wsOf (m0 : MachineData) : List Region := [⟨outA m0, 8 + claimBytes⟩, ⟨wA m0, weightsBytes⟩]

/-- The regions `first_claim` reads. -/
abbrev rsOf (m0 : MachineData) (n : Nat) : List Region :=
  [ewsRegion (reg m0 .rsi) n, ewsRegion (reg m0 .rcx) 1, ewsRegion (reg m0 .r8) 5,
    ewsRegion (reg m0 .r9) 25, argsRegion m0 3]

/-- **The precondition's facts.** -/
structure PreOk (inst segment lanePoint output : Array EW) (m0 : MachineData) : Prop where
  st : StackOk m0 firstClaimStack
  args : NativeRustcVm.Mapped m0.dmem (argA m0) 24 ∧ (rspOf m0).toNat + 8 + 24 ≤ 2 ^ 64
  sz : inst.size = (reg m0 .rdx).toNat
  le30 : inst.size ≤ 30
  instAt : NativeRustcVm.EWsAt m0.dmem (reg m0 .rsi) inst.toList
  segSz : segment.size = 1
  segAt : NativeRustcVm.EWsAt m0.dmem (reg m0 .rcx) segment.toList
  lpSz : lanePoint.size = 5
  lpAt : NativeRustcVm.EWsAt m0.dmem (reg m0 .r8) lanePoint.toList
  opSz : output.size = 25
  opAt : NativeRustcVm.EWsAt m0.dmem (reg m0 .r9) output.toList
  areas : Areas m0 firstClaimStack (wsOf m0) (rsOf m0 inst.size)

/-- **The addresses as numbers**: the stack (`R` RSP), the result, the weights, `inst`, the
segment, the lane point, the output lanes; their bounds and the apartness of the written from
the rest. -/
structure Nums (R O W I G L U n : Nat) : Prop where
  r1 : 1632 ≤ R
  r2 : R + 32 ≤ 2 ^ 64
  o : O + 776 ≤ 2 ^ 64
  w : W + 25600 ≤ 2 ^ 64
  i : I + 16 * n ≤ 2 ^ 64
  g : G + 16 ≤ 2 ^ 64
  l : L + 80 ≤ 2 ^ 64
  u : U + 400 ≤ 2 ^ 64
  n30 : n ≤ 30
  os : O + 776 ≤ R - 1632 ∨ R + 8 ≤ O
  ws : W + 25600 ≤ R - 1632 ∨ R + 8 ≤ W
  ow : O + 776 ≤ W ∨ W + 25600 ≤ O
  si : R + 8 ≤ I ∨ I + 16 * n ≤ R - 1632
  sg : R + 8 ≤ G ∨ G + 16 ≤ R - 1632
  sl : R + 8 ≤ L ∨ L + 80 ≤ R - 1632
  su : R + 8 ≤ U ∨ U + 400 ≤ R - 1632
  oi : O + 776 ≤ I ∨ I + 16 * n ≤ O
  og : O + 776 ≤ G ∨ G + 16 ≤ O
  ol : O + 776 ≤ L ∨ L + 80 ≤ O
  ou : O + 776 ≤ U ∨ U + 400 ≤ O
  oa : O + 776 ≤ R + 8 ∨ R + 32 ≤ O
  wi : W + 25600 ≤ I ∨ I + 16 * n ≤ W
  wg : W + 25600 ≤ G ∨ G + 16 ≤ W
  wl : W + 25600 ≤ L ∨ L + 80 ≤ W
  wu : W + 25600 ≤ U ∨ U + 400 ≤ W
  wa : W + 25600 ≤ R + 8 ∨ R + 32 ≤ W

end

public section

variable {inst segment lanePoint output : Array EW} {m0 d : MachineData}

theorem stack_eq : firstClaimStack = 1632 := by decide

theorem slots_le : ∀ p ∈ slots, 1328 ≤ p.1 ∧ p.1 + 8 ≤ 1376 := by decide

theorem slots_le' : ∀ p ∈ slots, p.1 + 8 ≤ 1376 := fun p hp ↦ (slots_le p hp).2

theorem preOk [Labels] (h : FirstClaimPre inst segment lanePoint output m0) :
    PreOk inst segment lanePoint output m0 :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- **The addresses as numbers.** -/
theorem nums (h : PreOk inst segment lanePoint output m0) :
    Nums (rspOf m0).toNat (outA m0).toNat (wA m0).toNat (reg m0 .rsi).toNat (reg m0 .rcx).toNat
      (reg m0 .r8).toNat (reg m0 .r9).toNat inst.size := by
  have hA := h.areas
  have hs := stackBelow_toNat (m := m0) h.st.1
  have h8 := h.st.2.1
  have hst := h.st.1
  rw [stack_eq] at hs hst
  have ho : (⟨outA m0, 8 + claimBytes⟩ : Region) ∈ wsOf m0 := List.mem_cons_self
  have hw : (⟨wA m0, weightsBytes⟩ : Region) ∈ wsOf m0 := List.mem_cons_of_mem _ List.mem_cons_self
  have ri : ewsRegion (reg m0 .rsi) inst.size ∈ rsOf m0 inst.size := List.mem_cons_self
  have rg : ewsRegion (reg m0 .rcx) 1 ∈ rsOf m0 inst.size :=
    List.mem_cons_of_mem _ List.mem_cons_self
  have rl : ewsRegion (reg m0 .r8) 5 ∈ rsOf m0 inst.size :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have ru : ewsRegion (reg m0 .r9) 25 ∈ rsOf m0 inst.size :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have ra : argsRegion m0 3 ∈ rsOf m0 inst.size :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))
  have ea : (rspOf m0 + 8#64).toNat = (rspOf m0).toNat + 8 := by
    have := h.args.2
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have f1 : (outA m0).toNat + 776 ≤ 2 ^ 64 := (Areas.ok hA (List.mem_append_left _ ho)).2
  have f2 : (wA m0).toNat + 25600 ≤ 2 ^ 64 := (Areas.ok hA (List.mem_append_left _ hw)).2
  have f3 : (reg m0 .rsi).toNat + 16 * inst.size ≤ 2 ^ 64 :=
    (Areas.ok hA (List.mem_append_right _ ri)).2
  have f4 : (reg m0 .rcx).toNat + 16 * 1 ≤ 2 ^ 64 := (Areas.ok hA (List.mem_append_right _ rg)).2
  have f5 : (reg m0 .r8).toNat + 16 * 5 ≤ 2 ^ 64 := (Areas.ok hA (List.mem_append_right _ rl)).2
  have f6 : (reg m0 .r9).toNat + 16 * 25 ≤ 2 ^ 64 := (Areas.ok hA (List.mem_append_right _ ru)).2
  have s1 := Areas.apart_stack hA ho
  have s2 := Areas.apart_stack hA hw
  have s3 := Areas.stack_read hA ri
  have s4 := Areas.stack_read hA rg
  have s5 := Areas.stack_read hA rl
  have s6 := Areas.stack_read hA ru
  have p1 := Areas.apart_read hA ho ri
  have p2 := Areas.apart_read hA ho rg
  have p3 := Areas.apart_read hA ho rl
  have p4 := Areas.apart_read hA ho ru
  have p5 := Areas.apart_read hA ho ra
  have q1 := Areas.apart_read hA hw ri
  have q2 := Areas.apart_read hA hw rg
  have q3 := Areas.apart_read hA hw rl
  have q4 := Areas.apart_read hA hw ru
  have q5 := Areas.apart_read hA hw ra
  have hd : List.Pairwise (fun r r' : Region ↦ NativeRustcVm.Apart r.addr r.size r'.addr r'.size)
      (wsOf m0) := List.Pairwise.of_cons hA.2.1
  have ow := List.rel_of_pairwise_cons hd (List.mem_singleton_self _)
  unfold NativeRustcVm.Apart at s1 s2 s3 s4 s5 s6 p1 p2 p3 p4 p5 q1 q2 q3 q4 q5 ow
  dsimp only [ewsRegion, argsRegion] at s1 s2 s3 s4 s5 s6 p1 p2 p3 p4 p5 q1 q2 q3 q4 q5 ow
  have ec : claimBytes = 768 := rfl
  have ew : weightsBytes = 25600 := rfl
  rw [ea] at p5 q5
  rw [stack_eq, hs] at s1 s2 s3 s4 s5 s6
  have hn := h.le30
  have ha2 := h.args.2
  rw [ec] at ow p1 p2 p3 p4 p5
  rw [ew] at s2 ow q1 q2 q3 q4 q5
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (clear s1 s2 ow s3 s4 s5 s6 p1 p2 p3 p4 p5 q1 q2 q3 q4 q5; omega)
    | (clear s2 ow s3 s4 s5 s6 p1 p2 p3 p4 p5 q1 q2 q3 q4 q5; rcases s1 with x | x <;> omega)
    | (clear s1 ow s3 s4 s5 s6 p1 p2 p3 p4 p5 q1 q2 q3 q4 q5; rcases s2 with x | x <;> omega)
    | (clear s1 s2 s3 s4 s5 s6 p1 p2 p3 p4 p5 q1 q2 q3 q4 q5; rcases ow with x | x <;> omega)
    | (clear s1 s2 ow s4 s5 s6 p1 p2 p3 p4 p5 q1 q2 q3 q4 q5; rcases s3 with x | x <;> omega)
    | (clear s1 s2 ow s3 s5 s6 p1 p2 p3 p4 p5 q1 q2 q3 q4 q5; rcases s4 with x | x <;> omega)
    | (clear s1 s2 ow s3 s4 s6 p1 p2 p3 p4 p5 q1 q2 q3 q4 q5; rcases s5 with x | x <;> omega)
    | (clear s1 s2 ow s3 s4 s5 p1 p2 p3 p4 p5 q1 q2 q3 q4 q5; rcases s6 with x | x <;> omega)
    | (clear s1 s2 ow s3 s4 s5 s6 p2 p3 p4 p5 q1 q2 q3 q4 q5; rcases p1 with x | x <;> omega)
    | (clear s1 s2 ow s3 s4 s5 s6 p1 p3 p4 p5 q1 q2 q3 q4 q5; rcases p2 with x | x <;> omega)
    | (clear s1 s2 ow s3 s4 s5 s6 p1 p2 p4 p5 q1 q2 q3 q4 q5; rcases p3 with x | x <;> omega)
    | (clear s1 s2 ow s3 s4 s5 s6 p1 p2 p3 p5 q1 q2 q3 q4 q5; rcases p4 with x | x <;> omega)
    | (clear s1 s2 ow s3 s4 s5 s6 p1 p2 p3 p4 q1 q2 q3 q4 q5; rcases p5 with x | x <;> omega)
    | (clear s1 s2 ow s3 s4 s5 s6 p1 p2 p3 p4 p5 q2 q3 q4 q5; rcases q1 with x | x <;> omega)
    | (clear s1 s2 ow s3 s4 s5 s6 p1 p2 p3 p4 p5 q1 q3 q4 q5; rcases q2 with x | x <;> omega)
    | (clear s1 s2 ow s3 s4 s5 s6 p1 p2 p3 p4 p5 q1 q2 q4 q5; rcases q3 with x | x <;> omega)
    | (clear s1 s2 ow s3 s4 s5 s6 p1 p2 p3 p4 p5 q1 q2 q3 q5; rcases q4 with x | x <;> omega)
    | (clear s1 s2 ow s3 s4 s5 s6 p1 p2 p3 p4 p5 q1 q2 q3 q4; rcases q5 with x | x <;> omega)

theorem fbA_toNat (h : PreOk inst segment lanePoint output m0) :
    (fbA m0).toNat = (rspOf m0).toNat - 1376 :=
  stackBelow_toNat (by have := (nums h).r1; omega)

theorem sb_toNat (h : PreOk inst segment lanePoint output m0) :
    (stackBelow m0 firstClaimStack).toNat = (rspOf m0).toNat - 1632 := by
  rw [stack_eq]; exact stackBelow_toNat (by have := (nums h).r1; omega)

theorem argA_toNat (h : PreOk inst segment lanePoint output m0) :
    (argA m0).toNat = (rspOf m0).toNat + 8 := by
  have := (nums h).r2
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- A frame offset as a number. -/
theorem fb_off (h : PreOk inst segment lanePoint output m0) {j : Nat} (hj : j ≤ 1384) :
    (off (fbA m0) j).toNat = (rspOf m0).toNat - 1376 + j := by
  have := (nums h).r1; have := (nums h).r2
  rw [toNat_off (by rw [fbA_toNat h]; omega), fbA_toNat h]

/-- `InRange` as numbers. -/
theorem inR {a q : BitVec 64} {n : Nat} (hn : a.toNat + n ≤ 2 ^ 64)
    (h : NativeRustcVm.InRange a n q) : a.toNat ≤ q.toNat ∧ q.toNat < a.toNat + n :=
  (inRange_iff' hn).mp h

theorem inR' {a q : BitVec 64} {n : Nat} (hn : a.toNat + n ≤ 2 ^ 64)
    (h : a.toNat ≤ q.toNat ∧ q.toNat < a.toNat + n) : NativeRustcVm.InRange a n q :=
  (inRange_iff' hn).mpr h

/-- `Low` as numbers. -/
theorem low_iff (h : PreOk inst segment lanePoint output m0) {q : BitVec 64} :
    Low m0 q ↔ (rspOf m0).toNat - 1632 ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat - 1376 := by
  have := (nums h).r1; have := (nums h).r2
  unfold Low
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [sb_toNat h]; omega), sb_toNat h]
  omega

/-- `Out` as numbers. -/
theorem out_iff (h : PreOk inst segment lanePoint output m0) {q : BitVec 64} :
    Out m0 q ↔ ((outA m0).toNat ≤ q.toNat ∧ q.toNat < (outA m0).toNat + 776) ∨
      ((wA m0).toNat ≤ q.toNat ∧ q.toNat < (wA m0).toNat + 25600) ∨
      ((rspOf m0).toNat - 1632 ≤ q.toNat ∧ q.toNat < (rspOf m0).toNat) := by
  have hn := nums h
  have := hn.r1; have := hn.r2; have := hn.o; have := hn.w
  unfold Out
  rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega),
    inRange_iff' (by unfold NativeRustcVm.NoWrap; omega),
    inRange_iff' (by unfold NativeRustcVm.NoWrap; rw [sb_toNat h, stack_eq]; omega), sb_toNat h,
    stack_eq]
  omega

/-- A callee's stack from RSP at the frame's base is `Low`. -/
theorem callee_low (h : PreOk inst segment lanePoint output m0) {st : MachineData}
    (hsp : rspOf st = fbA m0) {s : Nat} (hs : s ≤ 256) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (stackBelow st s) s q) : Low m0 q := by
  have := (nums h).r1; have := (nums h).r2
  have e : (stackBelow st s).toNat = (rspOf m0).toNat - 1376 - s := by
    rw [stackBelow_toNat (by rw [hsp, fbA_toNat h]; omega), hsp, fbA_toNat h]
  have := inR (by rw [e]; omega) hq
  rw [e] at this
  exact (low_iff h).mpr (by omega)

/-- The regions of a block in the body: the frame, the stack argument words. -/
theorem wf_body (h : PreOk inst segment lanePoint output m0) (hk : Kept m0.dmem d.dmem)
    {vars : Nat → BitVec 64} {ret : BitVec 64} :
    (frameEnv m0 d 1376 [(argA m0, 24)] vars ret).WF := by
  have := (nums h).r1; have := (nums h).r2
  have h1 := argA_toNat h
  have h2 := fbA_toNat h
  refine frame_wf ⟨Mapped.keeps (frame_mapped h.st (by rw [stack_eq]; decide)) hk,
    frame_noWrap h.st (by rw [stack_eq]; decide)⟩ (fun x hx ↦ ?_) (List.pairwise_pair.mpr ?_)
  · rw [List.mem_singleton] at hx
    subst hx
    exact ⟨Mapped.keeps h.args.1 hk, by show (argA m0).toNat + 24 ≤ 2 ^ 64; omega⟩
  · show (fbA m0).toNat + (1376 + 8) ≤ (argA m0).toNat ∨ _
    omega

/-- A stack argument word's region: the frame's offset `1384 + 8 i`. -/
theorem arg_alias [Labels] {vars : Nat → BitVec 64} {ret : BitVec 64} (i : Nat) :
    (Sym.ptr 0 ((1384 + 8 * i : Nat) : Int)).eval (frameEnv m0 d 1376 [(argA m0, 24)] vars ret) =
      (frameEnv m0 d 1376 [(argA m0, 24)] vars ret).base 1 + BitVec.ofInt 64 ((8 * i : Nat) : Int) := by
  rw [eval_ptr0, show 1384 + 8 * i = 1376 + (8 + 8 * i) by omega, frame_add]
  show _ = rspOf m0 + 8#64 + _
  rw [BitVec.add_assoc, show BitVec.ofInt 64 ((8 * i : Nat) : Int) = BitVec.ofNat 64 (8 * i) from
    BitVec.ofInt_natCast .., ← BitVec.ofNat_add]

/-- The body's start in a frame at RSP offset `o`. -/
theorem match_callS [Labels] (hf : Frame m0 1376 slots 8 d) {vars : Nat → BitVec 64}
    {ret : BitVec 64} : Match (frameEnv m0 d 1376 [(argA m0, 24)] vars ret) callS d :=
  match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hf.rsp_eval, trivial⟩ trivial trivial
    ⟨arg_alias 0, arg_alias 1, arg_alias 2, trivial⟩

/-- The stack argument words are the entry's in a state changed only in `Out`. -/
theorem arg_keep (h : PreOk inst segment lanePoint output m0)
    (hs : NativeRustcVm.SameOutside m0.dmem d.dmem (Out m0)) :
    ∀ i < 24, d.dmem.get? (argA m0 + BitVec.ofNat 64 i) = m0.dmem.get? (argA m0 + BitVec.ofNat 64 i) := by
  intro i hi
  have hn := nums h
  have := hn.r1; have := hn.r2; have := hn.oa; have := hn.wa
  have e := argA_toNat h
  have e2 : (argA m0 + BitVec.ofNat 64 i).toNat = (rspOf m0).toNat + 8 + i := by
    rw [show argA m0 + BitVec.ofNat 64 i = off (argA m0) i from rfl, toNat_off (by omega), e]
  refine hs _ fun hO ↦ ?_
  rw [out_iff h, e2] at hO
  omega

/-- **A stack argument word**, loaded. -/
theorem load_arg [Labels] (h : PreOk inst segment lanePoint output m0)
    (hs : NativeRustcVm.SameOutside m0.dmem d.dmem (Out m0)) {vars : Nat → BitVec 64}
    {ret : BitVec 64} {i : Nat} (hi : i < 3) (extra : List (BitVec 64 × Nat) := []) :
    (frameEnv m0 d 1376 ((argA m0, 24) :: extra) vars ret).load 1 (8 * i) 8 = stackArg m0 i := by
  have hm : NativeRustcVm.Mapped m0.dmem (off (argA m0) (8 * i)) 8 :=
    mapped_off h.args.1 (by omega)
  have hw : NativeRustcVm.WordAt m0.dmem (off (argA m0) (8 * i))
      (NativeRustcVm.wordOf m0.dmem (off (argA m0) (8 * i))) :=
    NativeRustcVm.wordAt_of_mapped hm
  have hw' : NativeRustcVm.WordAt d.dmem (off (argA m0) (8 * i))
      (NativeRustcVm.wordOf m0.dmem (off (argA m0) (8 * i))) :=
    bytesAt_congr hw fun j hj ↦ by
      rw [NativeRustcVm.length_wordBytes] at hj
      rw [NativeRustcVm.Transcript.off_add]
      exact arg_keep h hs _ (by omega)
  rw [load_of_wordAt (w := NativeRustcVm.wordOf m0.dmem (off (argA m0) (8 * i))) hw']
  unfold stackArg
  congr 2
  show rspOf m0 + 8#64 + BitVec.ofNat 64 (8 * i) = _
  rw [BitVec.add_assoc, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]

/-- **Bytes of the frame kept** where memory changed only at untouched frame offsets and off the
frame. -/
theorem keep_loc {d₁ d₂ : DataMem}
    {D : BitVec 64 → Prop} {o : Nat} {bs : List UInt8}
    (hs : NativeRustcVm.SameOutside d₁ d₂ D)
    (hD : ∀ i < bs.length, ¬ D (off (fbA m0) (o + i)))
    (hb : NativeRustcVm.BytesAt d₁ (off (fbA m0) o) bs) : NativeRustcVm.BytesAt d₂ (off (fbA m0) o) bs :=
  bytesAt_congr hb fun i hi ↦ by
    rw [NativeRustcVm.Transcript.off_add]; exact hs _ (hD i hi)

/-- **A call from the body**, RSP at the frame's base: the body after it; memory changed only in
the callee's region `D` (in `Out`, off the slots and the return address) and `Low`. -/
theorem call_body (h : PreOk inst segment lanePoint output m0) {st1 st2 : MachineData}
    (hf : Frame m0 1376 slots 0 st1) (hso : NativeRustcVm.SameOutside m0.dmem st1.dmem (Out m0))
    (hsv : Saved st1 st2) (hrsp : rspOf st2 = rspOf st1 + 8#64) {s : Nat} (hs : s ≤ 256)
    {D : BitVec 64 → Prop}
    (hch : NativeRustcVm.SameOutside st1.dmem st2.dmem
      (fun q ↦ D q ∨ NativeRustcVm.InRange (stackBelow st1 s) s q))
    (hD : ∀ q, D q → Out m0 q ∧ ∀ j, 1328 ≤ j → j < 1384 → q ≠ off (fbA m0) j) :
    Body m0 st2 ∧ NativeRustcVm.SameOutside st1.dmem st2.dmem (fun q ↦ D q ∨ Low m0 q) := by
  have hsp : rspOf st1 = fbA m0 := by rw [hf.sp, off_zero]
  have hn := nums h
  have := hn.r1; have := hn.r2
  have hL : ∀ j, j < 1384 → ¬ Low m0 (off (fbA m0) j) := fun j hj hq ↦ by
    rw [low_iff h, fb_off h hj.le] at hq; omega
  have hch' : NativeRustcVm.SameOutside st1.dmem st2.dmem (fun q ↦ D q ∨ Low m0 q) :=
    fun q hq ↦ hch q fun hc ↦ hq (hc.imp_right (callee_low h hsp hs))
  refine ⟨⟨Frame.call_at hf hsv hrsp hch' (fun p hp i hi ↦ ?_) (fun j hj ↦ ?_), fun q hq ↦ ?_⟩, hch'⟩
  · have := slots_le p hp
    rintro (hq | hq)
    · exact (hD _ hq).2 (p.1 + i) (by omega) (by omega) rfl
    · exact hL _ (by omega) hq
  · rintro (hq | hq)
    · exact (hD _ hq).2 (1376 + j) (by omega) (by omega) rfl
    · exact hL _ (by omega) hq
  · rw [hch' q fun hc ↦ hq (hc.elim (fun hd ↦ (hD q hd).1) fun hl ↦ by
      rw [out_iff h]; rw [low_iff h] at hl; omega)]
    exact hso q hq

/-- A frame offset below `1376` is in `Out` (the stack). -/
theorem frame_out (h : PreOk inst segment lanePoint output m0) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (fbA m0) 1376 q) : Out m0 q := by
  have hn := nums h
  have := hn.r1; have := hn.r2
  have := inR (by rw [fbA_toNat h]; omega) hq
  rw [fbA_toNat h] at this
  rw [out_iff h]; omega

/-- A frame region `[o, o + n)` below the slots as a callee's region. -/
theorem frame_D (h : PreOk inst segment lanePoint output m0) {o n : Nat} (hon : o + n ≤ 1328) :
    ∀ q, NativeRustcVm.InRange (off (fbA m0) o) n q →
      Out m0 q ∧ ∀ j, 1328 ≤ j → j < 1384 → q ≠ off (fbA m0) j := by
  intro q hq
  have hn := nums h
  have := hn.r1; have := hn.r2
  have e := fb_off h (j := o) (by omega)
  have := inR (by rw [e]; omega) hq
  rw [e] at this
  refine ⟨by rw [out_iff h]; omega, fun j hj hj' he ↦ ?_⟩
  rw [he, fb_off h (by omega)] at this
  omega

/-- A frame block's writes (frame offsets `[lo, hi)`, below the slots) keep the body. -/
theorem block_body (h : PreOk inst segment lanePoint output m0) {st1 st2 : MachineData}
    (hb : Body m0 st1) (hf : Frame m0 1376 slots 8 st2) {lo hi : Nat} (hhi : hi ≤ 1376)
    (hs : NativeRustcVm.SameOutside st1.dmem st2.dmem
      (fun q ↦ Touch (fbA m0) (1376 + 8) (fun j ↦ lo ≤ j ∧ j < hi) q)) : Body m0 st2 :=
  ⟨hf, fun q hq ↦ by
    rw [hs q fun ⟨j, hj, hj', e⟩ ↦ hq (e ▸ frame_out h (inRange_off_self (by omega) (by omega)))]
    exact hb.same q hq⟩

/-- Frame bytes kept by a frame block's writes elsewhere. -/
theorem keep_touch (h : PreOk inst segment lanePoint output m0) {d₁ d₂ : DataMem} {lo hi o : Nat}
    {bs : List UInt8}
    (hs : NativeRustcVm.SameOutside d₁ d₂
      (fun q ↦ Touch (fbA m0) (1376 + 8) (fun j ↦ lo ≤ j ∧ j < hi) q))
    (hle : o + bs.length ≤ 1384) (hd : o + bs.length ≤ lo ∨ hi ≤ o)
    (hb : NativeRustcVm.BytesAt d₁ (off (fbA m0) o) bs) : NativeRustcVm.BytesAt d₂ (off (fbA m0) o) bs :=
  keep_loc hs (fun i hi' ⟨j, hj, hj', e⟩ ↦ by
    have := NativeRustcVm.Transcript.off_inj (frame_noWrap h.st (by rw [stack_eq]; decide)) hj
      (show o + i < 1376 + 8 by omega) e
    omega) hb

/-- Bytes off the frame and `Low` kept where memory changed only in the frame, `Low` and `D`. -/
theorem keep_ext (h : PreOk inst segment lanePoint output m0) {d₁ d₂ : DataMem}
    {D : BitVec 64 → Prop} {a : BitVec 64} {bs : List UInt8}
    (hs : NativeRustcVm.SameOutside d₁ d₂ (fun q ↦ D q ∨ Low m0 q))
    (ha : a.toNat + bs.length ≤ 2 ^ 64)
    (hap : a.toNat + bs.length ≤ (rspOf m0).toNat - 1632 ∨ (rspOf m0).toNat - 1376 ≤ a.toNat)
    (hD : ∀ i < bs.length, ¬ D (a + BitVec.ofNat 64 i))
    (hb : NativeRustcVm.BytesAt d₁ a bs) : NativeRustcVm.BytesAt d₂ a bs :=
  bytesAt_congr hb fun i hi ↦ hs _ fun hq ↦ hq.elim (hD i hi) fun hl ↦ by
    rw [low_iff h, show a + BitVec.ofNat 64 i = off a i from rfl, toNat_off (by omega)] at hl
    omega

/-- Every write of a block in region 0 within `[lo, hi)`. -/
theorem within_spec {S : SState} {lo hi : Nat} (h : within S lo hi = true) :
    ∀ w ∈ S.mem, w.r = 0 ∧ lo ≤ w.off ∧ w.off + w.n ≤ hi := by
  intro w hw
  unfold within at h
  have := List.all_eq_true.mp h w hw
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- A register the block left as its atom. -/
theorem atoms_eq [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    {rs : List Reg64} (h : atoms S rs = true) {r : Reg64} (hr : r ∈ rs) :
    reg m r = env.regs r := by
  unfold atoms at h
  have := List.all_eq_true.mp h r hr
  rw [beq_iff_eq] at this
  exact hm.regs r _ this

/-- A frame byte is the stack's. -/
theorem frame_stk (h : PreOk inst segment lanePoint output m0) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (fbA m0) 1376 q) : Stk m0 q := by
  have hn := nums h
  have h1 := hn.r1
  have h2 := hn.r2
  have e := fbA_toNat h
  have hq' := inR (by rw [e]; omega) hq
  rw [e] at hq'
  exact ⟨by omega, by omega⟩

/-- A byte of `Low` is the stack's. -/
theorem low_stk (h : PreOk inst segment lanePoint output m0) {q : BitVec 64} (hq : Low m0 q) :
    Stk m0 q := by
  rw [low_iff h] at hq
  exact ⟨by omega, by omega⟩

/-- **Bytes off the stack kept** where memory changed only in the stack. -/
theorem keep_stk {d₁ d₂ : DataMem} {R : BitVec 64 → Prop} {a : BitVec 64} {bs : List UInt8}
    (hs : NativeRustcVm.SameOutside d₁ d₂ R) (hR : ∀ q, R q → Stk m0 q)
    (ha : a.toNat + bs.length ≤ 2 ^ 64)
    (hap : a.toNat + bs.length ≤ (rspOf m0).toNat - 1632 ∨ (rspOf m0).toNat + 8 ≤ a.toNat)
    (hb : NativeRustcVm.BytesAt d₁ a bs) : NativeRustcVm.BytesAt d₂ a bs :=
  bytesAt_congr hb fun i hi ↦ hs _ fun hq ↦ by
    obtain ⟨h1, h2⟩ := hR _ hq
    rw [show a + BitVec.ofNat 64 i = off a i from rfl, toNat_off (by omega)] at h1 h2
    omega

/-- A body kept by a block not writing memory. -/
theorem Body.of_mem (hb : Body m0 d) {d' : MachineData} (hf : Frame m0 1376 slots 8 d')
    (hd : d'.dmem = d.dmem) : Body m0 d' :=
  ⟨hf, hd ▸ hb.same⟩

/-- A frame byte a block touched is the stack's. -/
theorem touch_stk (h : PreOk inst segment lanePoint output m0) {W : Nat → Prop}
    (hW : ∀ j, W j → j < 1376) {q : BitVec 64} (hq : Touch (fbA m0) (1376 + 8) W q) :
    Stk m0 q := by
  obtain ⟨j, -, hj, rfl⟩ := hq
  exact frame_stk h (inRange_off_self (hW j hj) (by decide))

/-- A frame byte a block touched is in `Out`. -/
theorem touch_out (h : PreOk inst segment lanePoint output m0) {W : Nat → Prop}
    (hW : ∀ j, W j → j < 1376) {q : BitVec 64} (hq : Touch (fbA m0) (1376 + 8) W q) :
    Out m0 q := by
  obtain ⟨j, -, hj, rfl⟩ := hq
  exact frame_out h (inRange_off_self (hW j hj) (by decide))

/-- The bit weights' bytes are not the stack's. -/
theorem w_not_stk (h : PreOk inst segment lanePoint output m0) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (wA m0) 25600 q) : ¬ Stk m0 q := by
  have hn := nums h
  have h1 := hn.w
  have h2 := hn.ws
  have := inR h1 hq
  rintro ⟨_, _⟩
  omega

/-- The result's bytes are not the stack's. -/
theorem out_not_stk (h : PreOk inst segment lanePoint output m0) {q : BitVec 64}
    (hq : NativeRustcVm.InRange (outA m0) 776 q) : ¬ Stk m0 q := by
  have hn := nums h
  have h1 := hn.o
  have h2 := hn.os
  have := inR h1 hq
  rintro ⟨_, _⟩
  omega

/-- **Stack bytes kept** where memory changed only in the bit weights. -/
theorem keep_off_w (h : PreOk inst segment lanePoint output m0) {d₁ d₂ : DataMem} {o n : Nat}
    (hon : o + n ≤ 25600) {a : BitVec 64} {bs : List UInt8}
    (hs : NativeRustcVm.SameOutside d₁ d₂ (NativeRustcVm.InRange (off (wA m0) o) n))
    (ha : (rspOf m0).toNat - 1632 ≤ a.toNat ∧ a.toNat + bs.length ≤ (rspOf m0).toNat + 8)
    (hb : NativeRustcVm.BytesAt d₁ a bs) : NativeRustcVm.BytesAt d₂ a bs :=
  bytesAt_congr hb fun i hi ↦ hs _ fun hq ↦ by
    have hw := (nums h).w
    have hr := (nums h).r2
    refine w_not_stk h (off_in (by unfold NativeRustcVm.NoWrap; omega) hon hq) ⟨?_, ?_⟩ <;>
      rw [show a + BitVec.ofNat 64 i = off a i from rfl, toNat_off (by omega)] <;> omega

theorem ews_len (xs : List EW) : (xs.flatMap NativeRustcVm.ewBytes).length = 16 * xs.length :=
  NativeRustcVm.Transcript.length_flatMap_ewBytes xs

end

end NativeRustcVmX64.KeccakGkr.FirstClaim
