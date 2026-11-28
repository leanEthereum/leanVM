module

public import NativeRustcVmArm.Whir.SubspaceTable.Exec
public import NativeRustcVm.Whir.MathSubspaceRoots

/-!
# `subspace_table`'s states

From the entry `m0` (`μ` X1, `μ ≤ 31`), in the 864-byte frame at `fb` (`fbOf`): the spilled
output at `fb + 8`, the layer's 31 words from `fb + 16`, the table's pairs from `fb + 272`.
- `Init i`: the layer's first `i` words set (`initL i`); `VInv j` at the unrolled loop's head
  (`b7`, four words a turn), `TInv i` at the word loop's head (`b10`); `Init μ` at `b11`;
- `Turn t` (every turn's facts: `t` roots and their inverses in the table), with `OInv t` at
  the turns' head (`b14`, the layer `layerAt μ t`, the last root in X21) and `IInv t j` at the
  layer's loop head (`b15`, words `t` to `j − 1` updated, `innerL`), `Turned t` after it;
- `Done` at the copy (`b21`): the whole table.
`wordsAt_update` changes some of the words of a `WordsAt` (a block's stores).
-/

namespace NativeRustcVmArm.Whir.SubspaceTable

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVm (Region WordAt WordsAt)

@[expose] public section

/-- The frame's base. -/
def fbOf (m0 : MachineData) : BitVec 64 := m0.regs.SP.toBitVec - BitVec.ofNat 64 864
/-- The output: the `Option<Buf<(u64, u64), 31>>`. -/
def outsOf (m0 : MachineData) : List Region := [⟨m0.regs.X0.toBitVec, 8 + tableBytes⟩]
/-- `μ`. -/
def muOf (m0 : MachineData) : Nat := m0.regs.X1.toNat
/-- The words the unrolled initialization sets. -/
def n4Of (m0 : MachineData) : Nat := muOf m0 / 4 * 4

/-- The body's frame. -/
abbrev Fr (m0 st : MachineData) : Prop := Frame m0 864 subspaceTableStack slots (outsOf m0) st

/-- The layer's first `i` words set. -/
structure Init (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  fr : Fr m0 st
  out : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 8) m0.regs.X0
  layer : WordsAt st.dmem (fbOf m0 + BitVec.ofNat 64 16) (initL i)
  x20 : st.regs.X20 = m0.regs.X1
  x21 : st.regs.X21.toBitVec = fbOf m0 + BitVec.ofNat 64 16
  x24 : st.regs.X24.toNat = 8 * muOf m0
  hmu : muOf m0 ≤ 31

/-- The unrolled loop's head after `j` turns. -/
structure VInv (m0 : MachineData) (j : Nat) (st : MachineData) : Prop where
  init : Init m0 (4 * j) st
  x8 : st.regs.X8.toNat = n4Of m0
  x9 : st.regs.X9.toBitVec = fbOf m0 + BitVec.ofNat 64 (16 + 8 * n4Of m0)
  x10 : st.regs.X10.toNat = muOf m0
  x11 : st.regs.X11.toBitVec = fbOf m0 + BitVec.ofNat 64 (32 + 32 * j)
  x12 : st.regs.X12.toNat = 4 * j + 1
  x13 : st.regs.X13 = 2
  x14 : st.regs.X14 = 4
  x15 : st.regs.X15 = 8
  x16 : st.regs.X16 = 16
  x17 : st.regs.X17.toNat = n4Of m0 - 4 * j
  hj : 4 * j < n4Of m0

/-- After the unrolled loop. -/
structure VDone (m0 : MachineData) (st : MachineData) : Prop where
  init : Init m0 (n4Of m0) st
  x8 : st.regs.X8.toNat = n4Of m0
  x9 : st.regs.X9.toBitVec = fbOf m0 + BitVec.ofNat 64 (16 + 8 * n4Of m0)
  x10 : st.regs.X10.toNat = muOf m0

/-- The word loop's head at word `i`. -/
structure TInv (m0 : MachineData) (i : Nat) (st : MachineData) : Prop where
  init : Init m0 i st
  x8 : st.regs.X8.toNat = i
  x9 : st.regs.X9.toBitVec = fbOf m0 + BitVec.ofNat 64 (16 + 8 * i)
  x10 : st.regs.X10.toBitVec = fbOf m0 + BitVec.ofNat 64 (16 + 8 * muOf m0)
  x11 : st.regs.X11 = 2
  hi : i < muOf m0

/-- Every turn's facts after `t` turns. -/
structure Turn (m0 : MachineData) (t : Nat) (st : MachineData) : Prop where
  fr : Fr m0 st
  out : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 8) m0.regs.X0
  table : WordsAt st.dmem (fbOf m0 + BitVec.ofNat 64 272) (pairWords (tableAt (muOf m0) t))
  x20 : st.regs.X20 = m0.regs.X1
  x24 : st.regs.X24.toNat = 8 * muOf m0
  x25 : st.regs.X25.toNat = t + 1
  x26 : st.regs.X26.toNat = t
  x27 : st.regs.X27.toBitVec = fbOf m0 + BitVec.ofNat 64 272
  x28 : st.regs.X28.toBitVec = fbOf m0 + BitVec.ofNat 64 16
  ht : t < muOf m0
  hmu : muOf m0 ≤ 31

/-- The turns' head after `t` turns. -/
structure OInv (m0 : MachineData) (t : Nat) (st : MachineData) : Prop where
  turn : Turn m0 t st
  x21 : st.regs.X21 = lastAt (layerAt (muOf m0) t) t
  layer : WordsAt st.dmem (fbOf m0 + BitVec.ofNat 64 16) (layerAt (muOf m0) t)

/-- Turn `t`'s loop head at word `j`. -/
structure IInv (m0 : MachineData) (t j : Nat) (st : MachineData) : Prop where
  turn : Turn m0 t st
  x21 : st.regs.X21 = lastAt (layerAt (muOf m0) t) t
  layer : WordsAt st.dmem (fbOf m0 + BitVec.ofNat 64 16)
    (innerL (layerAt (muOf m0) t) t j)
  x19 : st.regs.X19.toBitVec = fbOf m0 + BitVec.ofNat 64 (16 + 8 * j)
  x29 : st.regs.X29.toNat = 8 * (muOf m0 - j)
  htj : t ≤ j
  hj : j < muOf m0

/-- Turn `t`'s layer loop done: the layer `layerAt μ (t + 1)`. -/
structure Turned (m0 : MachineData) (t : Nat) (st : MachineData) : Prop where
  turn : Turn m0 t st
  layer : WordsAt st.dmem (fbOf m0 + BitVec.ofNat 64 16) (layerAt (muOf m0) (t + 1))
  x21 : st.regs.X21 = lastAt (layerAt (muOf m0) t) t

/-- Every turn done. -/
structure Done (m0 : MachineData) (st : MachineData) : Prop where
  fr : Fr m0 st
  out : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 8) m0.regs.X0
  table : WordsAt st.dmem (fbOf m0 + BitVec.ofNat 64 272)
    (pairWords (tableAt (muOf m0) (muOf m0)))
  x25 : st.regs.X25.toNat = muOf m0 + 1
  hmu : muOf m0 ≤ 30

end

public section

theorem stack_eq : subspaceTableStack = 1024 := by decide

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 864 := by decide

theorem slots_ge : ∀ p ∈ slots, 768 ≤ p.1 := by decide

theorem x30_mem : XReg.X30 ∈ slots.map (·.2) :=
  List.mem_map.mpr ⟨(776, .X30), by simp [slots], rfl⟩

theorem n4Of_le (m0 : MachineData) : n4Of m0 ≤ muOf m0 := by unfold n4Of; omega

/-- Bytes kept by a block whose writes in region `r` are apart from them. -/
theorem bytesAt_keep [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m)
    (hwf : env.WF) {r : Nat} {b : BitVec 64} {sz : Nat} (hb : env.regions[r]? = some (b, sz))
    {o : Nat} {bs : List UInt8} (hle : o + bs.length ≤ sz)
    (hall : ∀ w ∈ S.mem, w.r = r ∧ (w.off + w.n ≤ o ∨ o + bs.length ≤ w.off))
    (h : NativeRustcVm.BytesAt env.mem0 (b + BitVec.ofNat 64 o) bs) :
    NativeRustcVm.BytesAt m.dmem (b + BitVec.ofNat 64 o) bs := fun i hi ↦ by
  rw [addr_add, Match.keep hm hwf hb hle hall i hi, ← addr_add]
  exact h i hi

theorem table_len {m0 : MachineData} {t : Nat} (ht : t ≤ muOf m0) :
    ((pairWords (tableAt (muOf m0) t)).flatMap NativeRustcVm.wordBytes).length = 16 * (t + 1) := by
  rw [NativeRustcVm.length_wordsBytes, pairWords_length', tableAt_length ht]
  omega

section
variable {m0 st st' : MachineData} {t : Nat}

/-- **A call** keeps a turn's facts. -/
theorem Turn.call {N : Nat} (h : Turn m0 t st) (hS : StackOk m0 subspaceTableStack)
    (hN : 864 + N ≤ subspaceTableStack)
    (hsame : SameOutside st.dmem st'.dmem (InRange (stackBelow st N) N)) (hsv : Saved st st') :
    Turn m0 t st' where
  fr := h.fr.call hS hN slots_le hsame hsv
  out := h.fr.bytes_call hS hN hsame (o := 8) (bs := NativeRustcVm.wordBytes m0.regs.X0)
    (by rw [NativeRustcVm.length_wordBytes]; omega) h.out
  table := h.fr.bytes_call hS hN hsame (o := 272)
    (by rw [table_len (by have := h.ht; omega)]; have := h.ht; have := h.hmu; omega) h.table
  x20 := (hsv.1 .X20 rfl).trans h.x20
  x24 := by rw [show st'.regs.X24 = st.regs.X24 from hsv.1 .X24 rfl]; exact h.x24
  x25 := by rw [show st'.regs.X25 = st.regs.X25 from hsv.1 .X25 rfl]; exact h.x25
  x26 := by rw [show st'.regs.X26 = st.regs.X26 from hsv.1 .X26 rfl]; exact h.x26
  x27 := by rw [show st'.regs.X27 = st.regs.X27 from hsv.1 .X27 rfl]; exact h.x27
  x28 := by rw [show st'.regs.X28 = st.regs.X28 from hsv.1 .X28 rfl]; exact h.x28
  ht := h.ht
  hmu := h.hmu

/-- **A change of the frame's bytes `o` to `o + n − 1`**, inside the layer, keeps a turn's
facts. -/
theorem Turn.store {o n : Nat} (h : Turn m0 t st) (hS : StackOk m0 subspaceTableStack)
    (hfr : Fr m0 st')
    (hregs : ∀ r ∈ [XReg.X20, .X24, .X25, .X26, .X27, .X28],
      st'.regs.getXReg r = st.regs.getXReg r)
    (hsame : NativeRustcVm.SameOutside st.dmem st'.dmem
      (NativeRustcVm.InRange (fbOf m0 + BitVec.ofNat 64 o) n))
    (ho : 16 ≤ o) (hon : o + n ≤ 272) : Turn m0 t st' := by
  obtain ⟨-, hfnw, hfe⟩ := frame_ok hS (show 864 ≤ subspaceTableStack by decide)
  have hfb : (fbOf m0).toNat + 864 ≤ 2 ^ 64 := hfnw
  have ht := h.ht
  have hmu := h.hmu
  have hlen := table_len (m0 := m0) (t := t) (by omega)
  have hnw : NativeRustcVm.NoWrap (fbOf m0 + BitVec.ofNat 64 o) n :=
    NativeRustcVm.NoWrap.sub hfnw (by omega)
  have hap : ∀ o' len, (o' + len ≤ o ∨ o + n ≤ o') → o' + len < 864 →
      NativeRustcVm.Apart (fbOf m0 + BitVec.ofNat 64 o') len (fbOf m0 + BitVec.ofNat 64 o) n := by
    intro o' len h1 h2
    unfold NativeRustcVm.Apart
    rw [toNat_add_ofNat' (by omega), toNat_add_ofNat' (by omega)]
    omega
  have hw8 : (NativeRustcVm.wordBytes m0.regs.X0).length = 8 := NativeRustcVm.length_wordBytes _
  have hap8 := hap 8 8 (.inl (by omega)) (by omega)
  have hap2 := hap 272 (16 * (t + 1)) (.inr (by omega)) (by omega)
  rw [← hw8] at hap8
  rw [← hlen] at hap2
  refine ⟨hfr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.ht, h.hmu⟩
  · exact NativeRustcVm.BytesAt.of_sameOutside_apart h.out hsame hap8
      (NativeRustcVm.NoWrap.sub hfnw (by omega)) hnw
  · exact NativeRustcVm.BytesAt.of_sameOutside_apart h.table hsame hap2
      (NativeRustcVm.NoWrap.sub hfnw (by omega)) hnw
  · exact (hregs .X20 (.head _)).trans h.x20
  · rw [show st'.regs.X24 = st.regs.X24 from hregs .X24 (.tail _ (.head _))]
    exact h.x24
  · rw [show st'.regs.X25 = st.regs.X25 from hregs .X25 (.tail _ (.tail _ (.head _)))]
    exact h.x25
  · rw [show st'.regs.X26 = st.regs.X26 from hregs .X26 (.tail _ (.tail _ (.tail _ (.head _))))]
    exact h.x26
  · rw [show st'.regs.X27 = st.regs.X27 from
      hregs .X27 (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))]
    exact h.x27
  · rw [show st'.regs.X28 = st.regs.X28 from
      hregs .X28 (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))]
    exact h.x28

end

/-- **Some words stored** over words `lo` to `lo + n − 1`. -/
theorem wordsAt_update {d d' : DataMem} {a : BitVec 64} {L L' : List UInt64}
    {lo n : Nat} (h : WordsAt d a L)
    (hs : NativeRustcVm.SameOutside d d'
      (NativeRustcVm.InRange (a + BitVec.ofNat 64 (8 * lo)) (8 * n)))
    (hnw : NativeRustcVm.NoWrap a (8 * L.length)) (hle : lo + n ≤ L.length)
    (hlen : L'.length = L.length)
    (hout : ∀ i (hi : i < L.length), (i < lo ∨ lo + n ≤ i) → L'[i]'(hlen ▸ hi) = L[i])
    (hin : ∀ i (hi : i < L.length), lo ≤ i → i < lo + n →
      WordAt d' (a + BitVec.ofNat 64 (8 * i)) (L'[i]'(hlen ▸ hi))) :
    WordsAt d' a L' := by
  rw [NativeRustcVm.wordsAt_iff]
  intro i hi
  have hi' : i < L.length := hlen ▸ hi
  by_cases hr : lo ≤ i ∧ i < lo + n
  · exact hin i hi' hr.1 hr.2
  · rw [hout i hi' (by omega)]
    refine NativeRustcVm.BytesAt.of_sameOutside (h.getElem hi') hs fun j hj hp ↦ ?_
    simp only [NativeRustcVm.length_wordBytes] at hj
    unfold NativeRustcVm.NoWrap at hnw
    by_cases hn : n = 0
    · subst hn; unfold NativeRustcVm.InRange at hp; omega
    rw [NativeRustcVm.inRange_iff (NativeRustcVm.NoWrap.sub hnw (by omega)), addr_add,
      toNat_add_ofNat' (by omega), toNat_add_ofNat' (by omega)] at hp
    omega

end

end NativeRustcVmArm.Whir.SubspaceTable
