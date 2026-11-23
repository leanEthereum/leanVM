module

public import NativeRustcVmX64.KeccakGkr.Common
public import NativeRustcVmX64.KeccakGkr.KeccakOpen.States
public import NativeRustcVmX64.KeccakGkr.KeccakOpen.Model
public import NativeRustcVm.Transcript.Update
public import NativeRustcVm.Arrays.ReadLemmas

/-!
# `keccak_open`: the context (x86-64)

The entry's regions (`fbA` the frame's base, 2208 bytes below RSP, `oA` the result, `tA` the
`TState`, `slA` the slot point, `rwA` the rows, `argA` the stack arguments), the regions it may
change (`Out`, as `Writes` states them), the precondition's facts (`PreOk`) and its addresses as
numbers (`Nums`). The bytes a step of the fold may change (`Safe`: the stack below the frame's
word `64`, the row buffers, the rows); the state around the fold (`Mid`) and what keeps it
(`Mid.keep`).
-/

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVmX64.Transcript
open LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeRustcVm (Region InAny)
open NativeRustcVm.Transcript (off off_zero off_off off_add toNat_off inRange_iff' Mapped.keeps
  bytesAt_congr inRange_off_self DecArea tstateBytes TStateAt)
open NativeRustcVm.KeccakGkr (rowsBytes weightsBytes)

@[expose] public section

/-- The frame's base. -/
abbrev fbA (m0 : MachineData) : BitVec 64 := stackBelow m0 2208
/-- The result. -/
abbrev oA (m0 : MachineData) : BitVec 64 := reg m0 .rdi
/-- The `TState`. -/
abbrev tA (m0 : MachineData) : BitVec 64 := reg m0 .rsi
/-- The slot point. -/
abbrev slA (m0 : MachineData) : BitVec 64 := openSlot m0
/-- The rows. -/
abbrev rwA (m0 : MachineData) : BitVec 64 := openRows m0
/-- The stack argument words. -/
abbrev argA (m0 : MachineData) : BitVec 64 := rspOf m0 + 8#64

/-- The fold's regions besides the frame: the slot point, the rows, the stack arguments. -/
def RF [Labels] (m0 : MachineData) : List (BitVec 64 × Nat) :=
  [(slA m0, 96), (rwA m0, 65536), (argA m0, 48), (gotAddr "memcpy", 8)]

/-- The fold's environment. -/
abbrev E [Labels] (m0 st : MachineData) (vars : Nat → BitVec 64) (ret : BitVec 64) : Env :=
  frameEnv m0 st 2208 (RF m0) vars ret

/-- The environment known values are evaluated in. -/
abbrev envK [Labels] (m0 : MachineData) (vars : Nat → BitVec 64) : Env := E m0 m0 vars 0

/-- The regions `keccak_open` writes. -/
abbrev wsOf (m0 : MachineData) : List Region :=
  [⟨oA m0, 24⟩, ⟨tA m0, tstateBytes⟩, ewsRegion (slA m0) qkeccakSlotBits, ⟨rwA m0, rowsBytes⟩]

/-- The regions `keccak_open` reads. -/
abbrev rsOf [Labels] (a : DecArea) (c : KeccakClaimW) (m0 : MachineData) : List Region :=
  [a.region, ewsRegion (reg m0 .rcx) c.point.size, ⟨reg m0 .r9, weightsBytes⟩, rcRegion,
    argsRegion m0 6]

/-- What `keccak_open` may change. -/
def Out (m0 : MachineData) (q : BitVec 64) : Prop :=
  InAny (⟨stackBelow m0 keccakOpenStack, keccakOpenStack⟩ :: wsOf m0) q

/-- **The precondition's facts.** -/
structure PreOk [Labels] (a : DecArea) (s : TState) (c : KeccakClaimW) (m0 : MachineData) :
    Prop where
  st : StackOk m0 keccakOpenStack
  args : ArgsOk m0 6
  rc : RcAt m0 keccakOpenStack
  ts : TStateAt m0.dmem (tA m0) a s
  psz : c.point.size = (reg m0 .r8).toNat
  pt : NativeRustcVm.EWsAt m0.dmem (reg m0 .rcx) c.point.toList
  wt : NativeRustcVm.KeccakGkr.WeightsAt m0.dmem (reg m0 .r9) c
  seg : SegmentsFit (reg m0 .rdx).toNat c
  cnt : 1 ≤ (openCount m0).toNat
  fc : (openFirst m0).toNat + (openCount m0).toNat ≤ keccakSegments
  areas : Areas m0 keccakOpenStack (wsOf m0) (rsOf a c m0)
  got : GotAt m0 keccakOpenStack
    [(oA m0, 24), (tA m0, tstateBytes), (slA m0, 96), (rwA m0, rowsBytes),
      (a.region.addr, a.region.size), (reg m0 .rcx, 16 * c.point.size), (reg m0 .r9, weightsBytes),
      (rcAddr, 192), (argA m0, 48)] ["memcpy"]

/-- **The addresses as numbers**: RSP `R`, the result `O`, the `TState` `T`, the slot point `S`,
the rows `W`, the decoded words `A` (`L` bytes), the point `Q` (`K` bytes), the bit weights `B`,
the round constants `C`; the stack is the 3200 bytes below `R` and the return address. -/
structure Nums (R O T S W A L Q K B C : Nat) : Prop where
  r1 : 3200 ≤ R
  r2 : R + 56 ≤ 2 ^ 64
  o : O + 24 ≤ 2 ^ 64
  t : T + 760 ≤ 2 ^ 64
  s : S + 96 ≤ 2 ^ 64
  w : W + 65536 ≤ 2 ^ 64
  a : A + L ≤ 2 ^ 64
  q : Q + K ≤ 2 ^ 64
  b : B + 25600 ≤ 2 ^ 64
  c : C + 192 ≤ 2 ^ 64
  so : O + 24 ≤ R - 3200 ∨ R + 8 ≤ O
  st : T + 760 ≤ R - 3200 ∨ R + 8 ≤ T
  ss : S + 96 ≤ R - 3200 ∨ R + 8 ≤ S
  sw : W + 65536 ≤ R - 3200 ∨ R + 8 ≤ W
  sa : A + L ≤ R - 3200 ∨ R + 8 ≤ A
  sq : Q + K ≤ R - 3200 ∨ R + 8 ≤ Q
  sb : B + 25600 ≤ R - 3200 ∨ R + 8 ≤ B
  sc : C + 192 ≤ R - 3200 ∨ R + 8 ≤ C
  ot : O + 24 ≤ T ∨ T + 760 ≤ O
  os : O + 24 ≤ S ∨ S + 96 ≤ O
  ow : O + 24 ≤ W ∨ W + 65536 ≤ O
  ts : T + 760 ≤ S ∨ S + 96 ≤ T
  tw : T + 760 ≤ W ∨ W + 65536 ≤ T
  sw' : S + 96 ≤ W ∨ W + 65536 ≤ S
  oa : O + 24 ≤ A ∨ A + L ≤ O
  ta : T + 760 ≤ A ∨ A + L ≤ T
  wa : W + 65536 ≤ A ∨ A + L ≤ W
  sa' : S + 96 ≤ A ∨ A + L ≤ S
  oarg : O + 24 ≤ R + 8 ∨ R + 56 ≤ O
  targ : T + 760 ≤ R + 8 ∨ R + 56 ≤ T
  sarg : S + 96 ≤ R + 8 ∨ R + 56 ≤ S
  warg : W + 65536 ≤ R + 8 ∨ R + 56 ≤ W
  wq : W + 65536 ≤ Q ∨ Q + K ≤ W
  wb : W + 65536 ≤ B ∨ B + 25600 ≤ W
  tc : T + 760 ≤ C ∨ C + 192 ≤ T
  sc' : S + 96 ≤ C ∨ C + 192 ≤ S
  oc : O + 24 ≤ C ∨ C + 192 ≤ O

/-- The numbers of an entry state. -/
abbrev NumsOf [Labels] (a : DecArea) (c : KeccakClaimW) (m0 : MachineData) : Prop :=
  Nums (rspOf m0).toNat (oA m0).toNat (tA m0).toNat (slA m0).toNat (rwA m0).toNat a.words.toNat
    (8 * a.len) (reg m0 .rcx).toNat (16 * c.point.size) (reg m0 .r9).toNat rcAddr.toNat

/-- The bytes a step of the fold may change, as a number: the stack below the frame's word
`64`, the row buffers, the rows. -/
def SafeN (m0 : MachineData) (x : Nat) : Prop :=
  ((rspOf m0).toNat - 3200 ≤ x ∧ x < (rspOf m0).toNat - 2208 + 64) ∨
    ((rspOf m0).toNat - 2208 + 112 ≤ x ∧ x < (rspOf m0).toNat - 2208 + 2160) ∨
    ((rwA m0).toNat ≤ x ∧ x < (rwA m0).toNat + 65536)

/-- The bytes a step of the fold may change. -/
abbrev Safe (m0 : MachineData) (q : BitVec 64) : Prop := SafeN m0 q.toNat

/-- What the fold works with: the decoded area, the `TState` after the sumcheck, the slot point,
the sumcheck's value. -/
structure Cx where
  a : DecArea
  s1 : TState
  sl : Array EW
  v : EW

/-- **The state around the fold**: the frame (RSP at its offset `o`), memory changed only in
`Out`, the value at the frame's `80`, `72`, the result's address at `64`, the slot point, the
`TState`. -/
structure Mid [Labels] (c : Cx) (m0 : MachineData) (o : Nat) (st : MachineData) : Prop where
  fr : Frame m0 2208 slots o st
  same : NativeRustcVm.SameOutside m0.dmem st.dmem (Out m0)
  v0 : NativeRustcVm.WordAt st.dmem (off (fbA m0) 80) c.v.c0
  v1 : NativeRustcVm.WordAt st.dmem (off (fbA m0) 72) c.v.c1
  out : NativeRustcVm.WordAt st.dmem (off (fbA m0) 64) (UInt64.ofBitVec (oA m0))
  sl_size : c.sl.size = 6
  slot : NativeRustcVm.EWsAt st.dmem (slA m0) c.sl.toList
  ts : TStateAt st.dmem (tA m0) c.a c.s1

end

public section

variable [Labels] {a : DecArea} {s : TState} {c : KeccakClaimW} {m0 d d' : MachineData}

omit [Labels] in
theorem stack_eq : keccakOpenStack = 3200 := by decide

omit [Labels] in
theorem slots_le : ∀ p ∈ slots, 2160 ≤ p.1 ∧ p.1 + 8 ≤ 2208 := by decide

omit [Labels] in
theorem slots_le' : ∀ p ∈ slots, p.1 + 8 ≤ 2208 := fun p hp ↦ (slots_le p hp).2

theorem preOk (h : KeccakOpenPre a s c m0) : PreOk a s c m0 :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2⟩

omit [Labels] in
theorem apart_n {a1 a2 : BitVec 64} {n1 n2 : Nat} (h : NativeRustcVm.Apart a1 n1 a2 n2) :
    a1.toNat + n1 ≤ a2.toNat ∨ a2.toNat + n2 ≤ a1.toNat := h

omit [Labels] in
theorem fixS {x n y : Nat} (h : x + n ≤ y - 3200 ∨ y - 3200 + (3200 + 8) ≤ x) (hy : 3200 ≤ y) :
    x + n ≤ y - 3200 ∨ y + 8 ≤ x := by
  omega

omit [Labels] in
theorem fixS' {x n y : Nat} (h : y - 3200 + (3200 + 8) ≤ x ∨ x + n ≤ y - 3200) (hy : 3200 ≤ y) :
    x + n ≤ y - 3200 ∨ y + 8 ≤ x := by
  omega

omit [Labels] in
theorem argA_toNat' (h : (rspOf m0).toNat + 56 ≤ 2 ^ 64) : (argA m0).toNat = (rspOf m0).toNat + 8 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- **The addresses as numbers.** -/
theorem nums (h : PreOk a s c m0) : NumsOf a c m0 := by
  have hA := h.areas
  have hR := h.st.1
  have hR56 : (rspOf m0).toNat + 56 ≤ 2 ^ 64 := by have := h.args.2; omega
  rw [stack_eq] at hR
  have hs : (stackBelow m0 3200).toNat = (rspOf m0).toNat - 3200 := stackBelow_toNat hR
  have ea : (rspOf m0 + 8#64).toNat = (rspOf m0).toNat + 8 := argA_toNat' hR56
  have mo : (⟨oA m0, 24⟩ : Region) ∈ wsOf m0 := .head _
  have mt : (⟨tA m0, tstateBytes⟩ : Region) ∈ wsOf m0 := .tail _ (.head _)
  have ms : ewsRegion (slA m0) qkeccakSlotBits ∈ wsOf m0 := .tail _ (.tail _ (.head _))
  have mw : (⟨rwA m0, rowsBytes⟩ : Region) ∈ wsOf m0 := .tail _ (.tail _ (.tail _ (.head _)))
  have ra : a.region ∈ rsOf a c m0 := .head _
  have rq : ewsRegion (reg m0 .rcx) c.point.size ∈ rsOf a c m0 := .tail _ (.head _)
  have rb : (⟨reg m0 .r9, weightsBytes⟩ : Region) ∈ rsOf a c m0 := .tail _ (.tail _ (.head _))
  have rc : rcRegion ∈ rsOf a c m0 := .tail _ (.tail _ (.tail _ (.head _)))
  have rg : argsRegion m0 6 ∈ rsOf a c m0 := .tail _ (.tail _ (.tail _ (.tail _ (.head _))))
  have eq6 : qkeccakSlotBits = 6 := NativeVm.Math.Keccak.qkeccakSlotBits_eq
  have et : tstateBytes = 760 := rfl
  have er : rowsBytes = 65536 := rfl
  have eb : weightsBytes = 25600 := rfl
  have ok : ∀ r ∈ wsOf m0 ++ rsOf a c m0, r.addr.toNat + r.size ≤ 2 ^ 64 :=
    fun r hr ↦ (Areas.ok hA hr).2
  have dW : List.Pairwise (fun r r' : Region ↦ NativeRustcVm.Apart r.addr r.size r'.addr r'.size)
      (wsOf m0) := List.Pairwise.of_cons hA.2.1
  obtain ⟨dO, dW1⟩ := List.pairwise_cons.mp dW
  obtain ⟨dT, dW2⟩ := List.pairwise_cons.mp dW1
  obtain ⟨dS, -⟩ := List.pairwise_cons.mp dW2
  have o1 := ok _ (List.mem_append_left _ mo)
  have o2 := ok _ (List.mem_append_left _ mt)
  have o3 := ok _ (List.mem_append_left _ ms)
  have o4 := ok _ (List.mem_append_left _ mw)
  have o5 := ok _ (List.mem_append_right _ ra)
  have o6 := ok _ (List.mem_append_right _ rq)
  have o7 := ok _ (List.mem_append_right _ rb)
  have o8 := ok _ (List.mem_append_right _ rc)
  have s1 := apart_n (Areas.apart_stack hA mo)
  have s2 := apart_n (Areas.apart_stack hA mt)
  have s3 := apart_n (Areas.apart_stack hA ms)
  have s4 := apart_n (Areas.apart_stack hA mw)
  have s5 := apart_n (Areas.stack_read hA ra)
  have s6 := apart_n (Areas.stack_read hA rq)
  have s7 := apart_n (Areas.stack_read hA rb)
  have s8 := apart_n (Areas.stack_read hA rc)
  have p1 := apart_n (dO _ (.head _))
  have p2 := apart_n (dO _ (.tail _ (.head _)))
  have p3 := apart_n (dO _ (.tail _ (.tail _ (.head _))))
  have p4 := apart_n (dT _ (.head _))
  have p5 := apart_n (dT _ (.tail _ (.head _)))
  have p6 := apart_n (dS _ (.head _))
  have q1 := apart_n (Areas.apart_read hA mo ra)
  have q2 := apart_n (Areas.apart_read hA mt ra)
  have q3 := apart_n (Areas.apart_read hA mw ra)
  have q4 := apart_n (Areas.apart_read hA ms ra)
  have q5 := apart_n (Areas.apart_read hA mo rg)
  have q6 := apart_n (Areas.apart_read hA mt rg)
  have q7 := apart_n (Areas.apart_read hA ms rg)
  have q8 := apart_n (Areas.apart_read hA mw rg)
  have q9 := apart_n (Areas.apart_read hA mw rq)
  have q10 := apart_n (Areas.apart_read hA mw rb)
  have q11 := apart_n (Areas.apart_read hA mt rc)
  have q12 := apart_n (Areas.apart_read hA ms rc)
  have q13 := apart_n (Areas.apart_read hA mo rc)
  dsimp only [ewsRegion, argsRegion, DecArea.region, rcRegion, stackRegion] at *
  rw [stack_eq] at s1 s2 s3 s4 s5 s6 s7 s8
  rw [hs] at s1 s2 s3 s4 s5 s6 s7 s8
  rw [ea] at q5 q6 q7 q8
  rw [eq6] at o3 s3 p2 p4 p6 q4 q7 q12
  rw [et] at o2 s2 p1 p4 p5 q2 q6 q11
  rw [er] at o4 s4 p3 p5 p6 q3 q8 q9 q10
  rw [eb] at o7 s7 q10
  refine ⟨hR, hR56, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact o1
  · exact o2
  · exact o3
  · exact o4
  · exact o5
  · exact o6
  · exact o7
  · exact o8
  · exact fixS s1 hR
  · exact fixS s2 hR
  · exact fixS s3 hR
  · exact fixS s4 hR
  · exact fixS' s5 hR
  · exact fixS' s6 hR
  · exact fixS' s7 hR
  · exact fixS' s8 hR
  · exact p1
  · exact p2
  · exact p3
  · exact p4
  · exact p5
  · exact p6
  · exact q1
  · exact q2
  · exact q3
  · exact q4
  · exact q5
  · exact q6
  · exact q7
  · exact q8
  · exact q9
  · exact q10
  · exact q11
  · exact q12
  · exact q13

theorem fbA_toNat (h : PreOk a s c m0) : (fbA m0).toNat = (rspOf m0).toNat - 2208 :=
  stackBelow_toNat (by have := (nums h).r1; omega)

theorem argA_toNat (h : PreOk a s c m0) : (argA m0).toNat = (rspOf m0).toNat + 8 :=
  argA_toNat' (nums h).r2

/-- A frame offset as a number. -/
theorem fb_off (h : PreOk a s c m0) {j : Nat} (hj : j ≤ 2256) :
    (off (fbA m0) j).toNat = (rspOf m0).toNat - 2208 + j := by
  have := (nums h).r1; have := (nums h).r2
  rw [toNat_off (by rw [fbA_toNat h]; omega), fbA_toNat h]

/-- `Safe` bytes are `Out`'s. -/
theorem safe_out (h : PreOk a s c m0) {q : BitVec 64} (hq : Safe m0 q) : Out m0 q := by
  have hn := nums h
  have := hn.r1; have := hn.r2; have := hn.w
  have hsb : (stackBelow m0 3200).toNat = (rspOf m0).toNat - 3200 := stackBelow_toNat (by omega)
  have hst : (rspOf m0).toNat - 3200 ≤ q.toNat → q.toNat < (rspOf m0).toNat →
      NativeRustcVm.InRange (stackBelow m0 keccakOpenStack) keccakOpenStack q := fun hs' hlt ↦ by
    rw [stack_eq, inRange_iff' (by unfold NativeRustcVm.NoWrap; omega), hsb]
    omega
  unfold Safe SafeN at hq
  rcases hq with hq | hq | hq
  · exact ⟨_, List.mem_cons_self, hst hq.1 (by omega)⟩
  · exact ⟨_, List.mem_cons_self, hst (by omega) (by omega)⟩
  · refine ⟨⟨rwA m0, rowsBytes⟩, .tail _ (.tail _ (.tail _ (.tail _ (.head _)))), ?_⟩
    show NativeRustcVm.InRange (rwA m0) rowsBytes q
    rw [show rowsBytes = 65536 from rfl, inRange_iff' (show (rwA m0).toNat + 65536 ≤ 2 ^ 64 by omega)]
    exact hq

omit [Labels] in
/-- **Bytes kept** where memory changed only in `Safe` bytes, none of them in `[x, x + n)`. -/
theorem bytes_keep {d₁ d₂ : DataMem} {R : BitVec 64 → Prop} (hs : NativeRustcVm.SameOutside d₁ d₂ R)
    (hR : ∀ q, R q → Safe m0 q) {p : BitVec 64} {bs : List UInt8}
    (hp : p.toNat + bs.length ≤ 2 ^ 64)
    (hd : ∀ y, p.toNat ≤ y → y < p.toNat + bs.length → ¬ SafeN m0 y)
    (hb : NativeRustcVm.BytesAt d₁ p bs) : NativeRustcVm.BytesAt d₂ p bs :=
  bytesAt_congr hb fun i hi ↦ hs _ fun hq ↦ by
    have h1 : SafeN m0 (p + BitVec.ofNat 64 i).toNat := hR _ hq
    rw [show p + BitVec.ofNat 64 i = off p i from rfl, toNat_off (by omega)] at h1
    exact hd _ (by omega) (by omega) h1

/-- **The state around the fold kept** where memory changed only in `Safe` bytes. -/
theorem Mid.keep {cx : Cx} {o o' : Nat} (h : PreOk a s c m0) (hm : Mid cx m0 o d)
    (hf : Frame m0 2208 slots o' d') (hk : Kept d.dmem d'.dmem) {R : BitVec 64 → Prop}
    (hs : NativeRustcVm.SameOutside d.dmem d'.dmem R) (hR : ∀ q, R q → Safe m0 q)
    (hA : cx.a = a) : Mid cx m0 o' d' := by
  have hn := nums h
  have := hn.r1; have := hn.r2; have := hn.o; have := hn.t; have := hn.s; have := hn.w
  have := hn.a
  have hfb := fbA_toNat h
  have fw : ∀ {j : Nat} {w : UInt64}, 64 ≤ j → j + 8 ≤ 112 →
      NativeRustcVm.WordAt d.dmem (off (fbA m0) j) w → NativeRustcVm.WordAt d'.dmem (off (fbA m0) j) w :=
    fun hj hj' hw ↦ bytes_keep hs hR (by rw [fb_off h (by omega), NativeRustcVm.length_wordBytes]; omega)
      (fun y h1 h2 hy ↦ by
        rw [fb_off h (by omega)] at h1 h2
        rw [NativeRustcVm.length_wordBytes] at h2
        unfold SafeN at hy
        have := hn.sw
        omega) hw
  have hsl : NativeRustcVm.EWsAt d'.dmem (slA m0) cx.sl.toList := by
    refine bytes_keep hs hR ?_ ?_ hm.slot
    · rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hm.sl_size]; omega
    · intro y h1 h2 hy
      rw [NativeRustcVm.length_ewsBytes, Array.length_toList, hm.sl_size] at h2
      unfold SafeN at hy
      have := hn.ss; have := hn.sw'
      omega
  refine ⟨hf, fun q hq ↦ ?_, fw (by decide) (by decide) hm.v0, fw (by decide) (by decide) hm.v1,
    fw (by decide) (by decide) hm.out, hm.sl_size, hsl, ?_⟩
  · rw [hs q fun hr ↦ hq (safe_out h (hR q hr))]
    exact hm.same q hq
  · refine hm.ts.frame hk (fun q hq ↦ ?_) hs
    have hsq := hR q hq
    unfold Safe SafeN at hsq
    rw [hA]
    constructor
    · rw [show tstateBytes = 760 from rfl, inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)]
      have := hn.st; have := hn.tw
      omega
    · rw [inRange_iff' (by unfold NativeRustcVm.NoWrap; omega)]
      have := hn.sa; have := hn.wa
      omega

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
