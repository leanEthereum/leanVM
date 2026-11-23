module

public import NativeRustcVmArm.Whir.InducedWeight.Exec
public import NativeRustcVm.Whir.MathInduced
public import NativeRustcVm.Whir.MathSubspace

/-!
# `induced_weight`'s states

From the entry `m0` (`μ ≤ 30`): the frame's spills (`Spills`: the output at 16, the point's
pointer plus 8, `what`'s items, the table's slice, the turns' bound, the queries, the weights, the
point's count, then the table's copy, a `Buf<(u64, u64), 31>` at 88), all in the frame's bytes
16 to 592 (`Spills.mono`);
- `OInv j` at the queries' loop head (`b6`): `j` queries summed (`indTot`);
- `IInv j i` at the product's loop head (`b9`): `i` factors of query `j` (`indProd`);
- `Acc j` at the sum (`b5`): query `j`'s product done;
- `Done` at the store (`b15`): the sum over every query.
-/

namespace NativeRustcVmArm.Whir.InducedWeight

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVm (Region wordOf ewOf ewsOf)

@[expose] public section

/-- The frame's base. -/
def fbOf (m0 : MachineData) : BitVec 64 := m0.regs.SP.toBitVec - BitVec.ofNat 64 1200
/-- The output. -/
def outsOf (m0 : MachineData) : List Region := [⟨m0.regs.X0.toBitVec, 24⟩]
/-- `μ`. -/
def muOf (m0 : MachineData) : Nat := m0.regs.X1.toNat
/-- The table. -/
def tbOf (m0 : MachineData) : Array (UInt64 × UInt64) := subspaceTable (muOf m0)
/-- The queries. -/
def qsOf (m0 : MachineData) : Array UInt64 := wordSlice m0 m0.regs.X2.toBitVec m0.regs.X3.toNat
/-- The weights. -/
def wsOf (m0 : MachineData) : Array EW := slice m0 m0.regs.X4 m0.regs.X5
/-- The point. -/
def ptOf (m0 : MachineData) : Array EW := slice m0 m0.regs.X6 m0.regs.X7
/-- The queries' count the loop runs. -/
def cntOf (m0 : MachineData) : Nat := min m0.regs.X5.toNat m0.regs.X3.toNat
/-- Query `j`'s `What`s. -/
def whatOf (m0 : MachineData) (j : Nat) : Array UInt64 := subspaceAt (muOf m0) ((qsOf m0).getD j 0)
/-- Query `j`'s factors' count. -/
def lenOf (m0 : MachineData) (j : Nat) : Nat := min (ptOf m0).size (whatOf m0 j).size
/-- The sum over the first `j` queries. -/
def totOf (m0 : MachineData) (j : Nat) : EW := indTot (muOf m0) (qsOf m0) (wsOf m0) (ptOf m0) j
/-- Query `j`'s product after `i` factors. -/
def prodOf (m0 : MachineData) (j i : Nat) : EW :=
  indProd (ptOf m0) (whatOf m0 j) ((wsOf m0).getD j 0) i

/-- The body's frame. -/
abbrev Fr (m0 st : MachineData) : Prop := Frame m0 1200 inducedWeightStack slots [] st

/-- The spills and the table's copy. -/
structure Spills (m0 st : MachineData) : Prop where
  out : NativeRustcVm.WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 16) m0.regs.X0
  ptrs : NativeRustcVm.WordsAt st.dmem (fbOf m0 + BitVec.ofNat 64 24)
    [m0.regs.X6 + 8, UInt64.ofBitVec (fbOf m0 + BitVec.ofNat 64 600), (tbOf m0).size.toUInt64,
      UInt64.ofBitVec (fbOf m0 + BitVec.ofNat 64 96)]
  cnt : NativeRustcVm.WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 56) (cntOf m0).toUInt64
  args : NativeRustcVm.WordsAt st.dmem (fbOf m0 + BitVec.ofNat 64 64)
    [m0.regs.X2, m0.regs.X4, m0.regs.X7]
  table : BufPairsAt st.dmem (fbOf m0 + BitVec.ofNat 64 88) rootCap (tbOf m0).toList

/-- The queries' loop head after `j` queries. -/
structure OInv (m0 : MachineData) (j : Nat) (st : MachineData) : Prop where
  fr : Fr m0 st
  sp : Spills m0 st
  x22 : st.regs.X22.toNat = j
  x19 : st.regs.X19 = (totOf m0 j).c0
  x29 : st.regs.X29 = (totOf m0 j).c1
  hj : j < cntOf m0

/-- The product's loop head: `i` factors of query `j`. -/
structure IInv (m0 : MachineData) (j i : Nat) (st : MachineData) : Prop where
  fr : Fr m0 st
  sp : Spills m0 st
  what : NativeRustcVm.BufWordsAt st.dmem (fbOf m0 + BitVec.ofNat 64 592) rootCap (whatOf m0 j).toList
  x22 : st.regs.X22.toNat = j
  x19 : st.regs.X19 = (totOf m0 j).c0
  x29 : st.regs.X29 = (totOf m0 j).c1
  hj : j < cntOf m0
  x25 : st.regs.X25 = (prodOf m0 j i).c0
  x26 : st.regs.X26 = (prodOf m0 j i).c1
  x21 : st.regs.X21.toNat = lenOf m0 j - i
  x23 : st.regs.X23.toBitVec = m0.regs.X6.toBitVec + BitVec.ofNat 64 (16 * i + 8)
  x24 : st.regs.X24.toBitVec = fbOf m0 + BitVec.ofNat 64 (600 + 8 * i)
  hi : i < lenOf m0 j

/-- Query `j`'s product done. -/
structure Acc (m0 : MachineData) (j : Nat) (st : MachineData) : Prop where
  fr : Fr m0 st
  sp : Spills m0 st
  x22 : st.regs.X22.toNat = j
  x19 : st.regs.X19 = (totOf m0 j).c0
  x29 : st.regs.X29 = (totOf m0 j).c1
  hj : j < cntOf m0
  x25 : st.regs.X25 = (prodOf m0 j (lenOf m0 j)).c0
  x26 : st.regs.X26 = (prodOf m0 j (lenOf m0 j)).c1

/-- Every query summed. -/
structure Done (m0 : MachineData) (st : MachineData) : Prop where
  fr : Fr m0 st
  out : NativeRustcVm.WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 16) m0.regs.X0
  x19 : st.regs.X19 = (totOf m0 (cntOf m0)).c0
  x29 : st.regs.X29 = (totOf m0 (cntOf m0)).c1

end

public section

theorem stack_eq : inducedWeightStack = 2224 := by decide

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 1200 := by decide

theorem slots_ge : ∀ p ∈ slots, 1104 ≤ p.1 := by decide

theorem x30_mem : XReg.X30 ∈ slots.map (·.2) :=
  List.mem_map.mpr ⟨(1112, .X30), by simp [slots], rfl⟩

theorem whatOf_size (m0 : MachineData) (j : Nat) : (whatOf m0 j).size = (tbOf m0).size :=
  subspaceAtTable_size _ _

theorem qsOf_size (m0 : MachineData) : (qsOf m0).size = m0.regs.X3.toNat := by
  simp [qsOf, wordSlice]

theorem wsOf_size (m0 : MachineData) : (wsOf m0).size = m0.regs.X5.toNat := by
  simp [wsOf, slice]

theorem ptOf_size (m0 : MachineData) : (ptOf m0).size = m0.regs.X7.toNat := by
  simp [ptOf, slice]

/-- The result: the sum over every query. -/
theorem totOf_cnt (m0 : MachineData) :
    totOf m0 (cntOf m0) = inducedWeight (muOf m0) (qsOf m0) (wsOf m0) (ptOf m0) := by
  rw [inducedWeight_eq, wsOf_size, qsOf_size]
  rfl

/-- Bytes of the frame from 16 to 592, kept. -/
theorem bytes_mono {m0 : MachineData} {d d' : DataMem} {o : Nat} {bs : List UInt8}
    (h : NativeRustcVm.BytesAt d (fbOf m0 + BitVec.ofNat 64 o) bs) (ho : 16 ≤ o)
    (hl : o + bs.length ≤ 592)
    (hk : ∀ i, 16 ≤ i → i < 592 →
      d'.get? (fbOf m0 + BitVec.ofNat 64 i) = d.get? (fbOf m0 + BitVec.ofNat 64 i)) :
    NativeRustcVm.BytesAt d' (fbOf m0 + BitVec.ofNat 64 o) bs := fun i hi ↦ by
  rw [addr_add, hk _ (by omega) (by omega), ← addr_add]
  exact h i hi

/-- **The spills kept** where the frame's bytes 16 to 592 are. -/
theorem Spills.mono {m0 st st' : MachineData} (h : Spills m0 st)
    (hk : ∀ i, 16 ≤ i → i < 592 →
      st'.dmem.get? (fbOf m0 + BitVec.ofNat 64 i) = st.dmem.get? (fbOf m0 + BitVec.ofNat 64 i)) :
    Spills m0 st' := by
  obtain ⟨h1, h2, h3, h4, ⟨hl, h5, h6⟩⟩ := h
  have hl' : (tbOf m0).toList.length ≤ 31 := hl
  refine ⟨bytes_mono h1 (by omega) (by simp [NativeRustcVm.length_wordBytes]) hk,
    bytes_mono h2 (by omega) (by rw [NativeRustcVm.length_wordsBytes]; simp) hk,
    bytes_mono h3 (by omega) (by simp [NativeRustcVm.length_wordBytes]) hk,
    bytes_mono h4 (by omega) (by rw [NativeRustcVm.length_wordsBytes]; simp) hk,
    hl, bytes_mono h5 (by omega) (by simp [NativeRustcVm.length_wordBytes]) hk, ?_⟩
  have h6' : NativeRustcVm.BytesAt st.dmem (fbOf m0 + BitVec.ofNat 64 96)
      ((pairWords (tbOf m0).toList).flatMap NativeRustcVm.wordBytes) := by
    have := h6; unfold PairsAt NativeRustcVm.Transcript.off at this; rwa [addr_add] at this
  have hlen : ((pairWords (tbOf m0).toList).flatMap NativeRustcVm.wordBytes).length =
      16 * (tbOf m0).toList.length := by
    rw [NativeRustcVm.length_wordsBytes]
    simp [pairWords]
    omega
  have := bytes_mono h6' (by omega) (by omega) hk
  unfold PairsAt NativeRustcVm.Transcript.off
  rwa [addr_add]

theorem Spills.of_dmem {m0 st st' : MachineData} (h : Spills m0 st) (hd : st'.dmem = st.dmem) :
    Spills m0 st' := h.mono fun i _ _ ↦ by rw [hd]

/-- Bytes of the frame kept. -/
theorem bytes_keep {m0 : MachineData} {d d' : DataMem} {o lo hi : Nat} {bs : List UInt8}
    (h : NativeRustcVm.BytesAt d (fbOf m0 + BitVec.ofNat 64 o) bs) (ho : lo ≤ o)
    (hl : o + bs.length ≤ hi)
    (hk : ∀ i, lo ≤ i → i < hi →
      d'.get? (fbOf m0 + BitVec.ofNat 64 i) = d.get? (fbOf m0 + BitVec.ofNat 64 i)) :
    NativeRustcVm.BytesAt d' (fbOf m0 + BitVec.ofNat 64 o) bs := fun i hi' ↦ by
  rw [addr_add, hk _ (by omega) (by omega), ← addr_add]
  exact h i hi'

/-- A `Buf<u64, 31>` of the frame kept. -/
theorem bufWords_keep {m0 : MachineData} {d d' : DataMem} {o lo hi : Nat} {xs : List UInt64}
    (h : NativeRustcVm.BufWordsAt d (fbOf m0 + BitVec.ofNat 64 o) 31 xs) (ho : lo ≤ o)
    (hl : o + 256 ≤ hi)
    (hk : ∀ i, lo ≤ i → i < hi →
      d'.get? (fbOf m0 + BitVec.ofNat 64 i) = d.get? (fbOf m0 + BitVec.ofNat 64 i)) :
    NativeRustcVm.BufWordsAt d' (fbOf m0 + BitVec.ofNat 64 o) 31 xs := by
  obtain ⟨hl', h1, h2⟩ := h
  refine ⟨hl', bytes_keep h1 ho (by rw [NativeRustcVm.length_wordBytes]; omega) hk, ?_⟩
  rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, addr_add] at h2 ⊢
  exact bytes_keep h2 (by omega) (by rw [NativeRustcVm.length_wordsBytes]; omega) hk

/-- A call keeps the frame's bytes. -/
theorem keep_call {m0 st st' : MachineData} (hfr : Fr m0 st) {N : Nat}
    (hle : 1200 + N ≤ inducedWeightStack) (hS : StackOk m0 inducedWeightStack)
    (hsame : SameOutside st.dmem st'.dmem (InRange (stackBelow st N) N)) :
    ∀ i, 0 ≤ i → i < 1200 →
      st'.dmem.get? (fbOf m0 + BitVec.ofNat 64 i) = st.dmem.get? (fbOf m0 + BitVec.ofNat 64 i) :=
  fun i _ hi ↦ hsame _ (by
    unfold stackBelow
    rw [hfr.sp]
    have := m0.regs.SP.toNat_lt
    have hS' : inducedWeightStack ≤ m0.regs.SP.toNat := hS.2.1
    exact not_inRange_below (by omega))

/-- A call writing the frame from 592 keeps its bytes 16 to 592. -/
theorem keep_call_out {m0 st st' : MachineData} (hfr : Fr m0 st) {N n : Nat}
    (hle : 1200 + N ≤ inducedWeightStack) (hS : StackOk m0 inducedWeightStack) (hn : 592 + n ≤ 1200)
    (hsame : SameOutside st.dmem st'.dmem (fun p ↦
      NativeRustcVm.InAny [⟨fbOf m0 + BitVec.ofNat 64 592, n⟩] p ∨ InRange (stackBelow st N) N p)) :
    ∀ i, 16 ≤ i → i < 592 →
      st'.dmem.get? (fbOf m0 + BitVec.ofNat 64 i) = st.dmem.get? (fbOf m0 + BitVec.ofNat 64 i) := by
  intro i h1 h2
  refine hsame _ fun hp ↦ ?_
  obtain ⟨-, hnw, -⟩ := frame_ok hS (show 1200 ≤ inducedWeightStack by decide)
  have hfb : (fbOf m0).toNat + 1200 ≤ 2 ^ 64 := hnw
  rcases hp with ⟨r, hr, hp⟩ | hp
  · simp only [List.mem_singleton] at hr
    subst hr
    revert hp
    show ¬InRange _ n _
    by_cases hn0 : n = 0
    · subst hn0; unfold InRange; omega
    rw [Sym.inRange_iff (show NativeRustcVm.NoWrap _ _ from NativeRustcVm.NoWrap.sub
      (show NativeRustcVm.NoWrap (fbOf m0) 1200 from hfb) hn),
      toNat_add_ofNat' (by omega), toNat_add_ofNat' (by omega)]
    omega
  · revert hp
    unfold stackBelow
    rw [hfr.sp]
    have := m0.regs.SP.toNat_lt
    have hS' : inducedWeightStack ≤ m0.regs.SP.toNat := hS.2.1
    exact not_inRange_below (by omega)

end

end NativeRustcVmArm.Whir.InducedWeight
