import Rv64Verifier.Proofs.Bus.VbbTail58

/-!
# `verify_bus_balance`'s side loop: what the sums read

Past the block loop, at `0x80007b24`, the side's sums read the framework selectors from `S - 1304`,
their count at `S - 1288`, the tables' count at `S - 1296`, `known` at `S - 320` (`Ex`), the tables'
selectors from `s4`, the block loop's sum and memory invariant (`Tl`). `Blk.tl` gives it past the
last block; `EW` is what the stretch from `Front` to the block loop's entry writes.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript

/-- What the stretch from `Front` at `u` to the block loop's entry writes: `DotW` and the slots of
the blocks at `0x800077b0` and `0x800077c8`. -/
def EW (s u e : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 1304) 8 ∨ Within a (s.getReg .x2 - 1272) 8 ∨
    Within a (s.getReg .x2 - 1216) 24 ∨ Within a (s.getReg .x2 - 1184) 16 ∨ DotW s u e a

/-- What the sums past the block loop read of the frame, at `e`. -/
structure Ex (s h e : MachineState) (i : Nat)
    (sd : List BusBlock × BusLayoutRust × List E × List E × E) (point : List E) : Prop where
  fw : eListAt e (e.getMem (s.getReg .x2 - 1304)) sd.2.1.framework.length =
    sd.2.1.framework.map (·.eqAbove point)
  fwBuf : NewBuf h e (e.getMem (s.getReg .x2 - 1304)) (24 * sd.2.1.framework.length) 8
  m1288 : e.getMem (s.getReg .x2 - 1288) = BitVec.ofNat 64 sd.2.1.framework.length
  m1296 : e.getMem (s.getReg .x2 - 1296) = BitVec.ofNat 64 sd.2.1.tables.length
  known : eAt e (s.getReg .x2 - 320) =
    dotRust (sd.2.1.framework.map (·.eqAbove point)) (sd.2.2.1.map (sd.2.2.2.2 + ·))
  x25 : e.getReg .x25 = h.getReg .x25

/-- At `0x80007b24`, past the block loop entered at `e`. -/
structure Tl (s z h e t : MachineState) (i : Nat)
    (sd : List BusBlock × BusLayoutRust × List E × List E × E) (point : List E) (P : Word)
    (n : Nat) (forms : List (List Form)) (tot : List E) : Prop where
  mm : Mm s z h e t P n (blkFold point i sd forms (min sd.2.1.tables.length sd.1.length)).1 tot
  ex : Ex s h t i sd point
  acc : eOf3 (t.getReg .x17) (t.getReg .x16) (t.getReg .x15) =
    (blkFold point i sd forms (min sd.2.1.tables.length sd.1.length)).2
  tb : eListAt t (t.getReg .x20) sd.2.1.tables.length = tbSel sd point
  tbBuf : NewBuf h t (t.getReg .x20) (24 * sd.2.1.tables.length) 8
  x22 : t.getReg .x22 = BitVec.ofNat 64 i
  m1176 : t.getMem (s.getReg .x2 - 1176) = BitVec.ofNat 64 (8 * i)
  m1184 : t.getMem (s.getReg .x2 - 1184) = BitVec.ofNat 64 (16 * i)

theorem EW.mono {s u e e' : MachineState} (h : heapNext e ≤ heapNext e') {a : Word}
    (ha : EW s u e a) : EW s u e' a := by
  rcases ha with ha | ha | ha | ha | ha | ha | ha | ⟨a1, a2⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a1, by omega⟩))))))

theorem EW.frW {s h u e : MachineState} (hpre : BusBalancePre s) (hh : heapNext h ≤ heapNext u)
    {a : Word} (ha : EW s u e a) : FrW s h e a := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  rcases ha with ha | ha | ha | ha | ha | ha | ha | ⟨a1, a2⟩
  · exact Or.inl (by addr_omega [ha, hb1])
  · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1]))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1]))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, a2⟩))))))

/-- A heap address below `u`'s `NEXT` misses `EW`. -/
theorem EW.low {s u e : MachineState} (hpre : BusBalancePre s) (hu : HeapOk u) {a : Word}
    (h1 : heapStart ≤ a.toNat) (h2 : a.toNat < heapNext u) : ¬ EW s u e a := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hE := hu.hi
  simp only [heapNext, heapEnd, heapStart] at hE h1 h2
  rintro (hw | hw | hw | hw | hw | hw | hw | ⟨hw, -⟩)
  · addr_omega [hw, h1, h2, hE, hb1]
  · addr_omega [hw, h1, h2, hE, hb1]
  · addr_omega [hw, h1, h2, hE, hb1]
  · addr_omega [hw, h1, h2, hE, hb1]
  · addr_omega [hw, h1, h2, hE, hb1]
  · addr_omega [hw, h1, h2, hE, hb1]
  · simp only [nextAddr] at hw; addr_omega [hw, h1, h2, hE]
  · simp only [heapNext] at hw; omega

/-- A buffer allocated from `b` on, below `t`'s `NEXT`, keeps its elements under a frame that misses
it. -/
theorem DFrame.eListNew {b t t' : MachineState} {w : Word → Prop} (fr : DFrame t t' w) {p : Word}
    {m k : Nat} (hb : NewBuf b t p m 8) (hm : 24 * k ≤ m) (hlo : heapStart ≤ heapNext b)
    (ht : heapNext t ≤ heapEnd)
    (hw : ∀ a, heapStart ≤ a.toNat → a.toNat < heapNext t → ¬ w a) :
    eListAt t' p k = eListAt t p k :=
  fr.eListAt fun q hq hw' ↦ by
    rcases hb.2 with h0 | ⟨b1, b2⟩
    · omega
    simp only [heapStart, heapNext, heapEnd] at hlo ht b1 b2
    exact hw _ (by simp only [heapStart]; addr_omega [b1, b2, hq, hm, hlo, ht])
      (by simp only [heapNext]; addr_omega [b1, b2, hq, hm, hlo, ht]) hw'

/-- `Ex` past a block writing `S - 1272` and `S - [1216, 1192)`. -/
theorem Ex.keep {s h t e : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E}
    (hpre : BusBalancePre s) (X : Ex s h t i sd point) (Ih : Inv s h) (ht : HeapOk t)
    (fr : DFrame t e fun a ↦ Within a (s.getReg .x2 - 1272) 8 ∨ Within a (s.getReg .x2 - 1216) 24)
    (hm : heapNext t ≤ heapNext e) (x25 : e.getReg .x25 = t.getReg .x25) :
    Ex s h e i sd point := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hE := ht.hi
  have hlo := Ih.heap.lo
  have slot (j : Nat) (hj : 8 ≤ j) (hj2 : j ≤ 1344) (h1 : j ≠ 1272) (h2 : j ≤ 1192 ∨ 1224 ≤ j)
      (h8 : j % 8 = 0) :
      e.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = t.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    fr _ fun q hq hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hq, hb1, hj, hj2, h1, h2, h8]
  have e1304 : e.getMem (s.getReg .x2 - 1304) = t.getMem (s.getReg .x2 - 1304) :=
    slot 1304 (by omega) (by omega) (by omega) (by omega) rfl
  have hfb := X.fwBuf
  refine ⟨?_, ?_, (slot 1288 (by omega) (by omega) (by omega) (by omega) rfl).trans X.m1288,
    (slot 1296 (by omega) (by omega) (by omega) (by omega) rfl).trans X.m1296, ?_, x25.trans X.x25⟩
  · rw [e1304, DFrame.eListNew fr hfb (le_refl _) hlo hE fun a h1 h2 hw ↦ by
      simp only [heapStart, heapNext, heapEnd] at h1 h2 hE
      rcases hw with hw | hw <;> addr_omega [hw, h1, h2, hE, hb1]]
    exact X.fw
  · rw [e1304]
    refine ⟨hfb.1, hfb.2.imp_right fun h ↦ ⟨h.1, le_trans h.2 hm⟩⟩
  · rw [← X.known]
    have e8 : s.getReg .x2 - 320 + 8 = s.getReg .x2 - BitVec.ofNat 64 312 :=
      slot_add (S := s.getReg .x2) (j := 320) (k := 8) (by addr_omega [hb1]) (by omega)
    have e16 : s.getReg .x2 - 320 + 16 = s.getReg .x2 - BitVec.ofNat 64 304 :=
      slot_add (S := s.getReg .x2) (j := 320) (k := 16) (by addr_omega [hb1]) (by omega)
    refine eAt_congr (slot 320 (by omega) (by omega) (by omega) (by omega) rfl) ?_ ?_
    · rw [e8]; exact slot 312 (by omega) (by omega) (by omega) (by omega) rfl
    · rw [e16]; exact slot 304 (by omega) (by omega) (by omega) (by omega) rfl

/-- `Tl` past the last block. -/
theorem Blk.tl {s z h e t : MachineState} {i : Nat}
    {sd : List BusBlock × BusLayoutRust × List E × List E × E} {point : List E} {P : Word}
    {n : Nat} {forms : List (List Form)} {tot : List E} (hpre : BusBalancePre s) (Ih : Inv s h)
    (En : Entry s z h e i sd point P n) (X : Ex s h e i sd point)
    (B : Blk s z h e t i sd point P n forms tot (min sd.2.1.tables.length sd.1.length)) :
    Tl s z h e t i sd point P n forms tot := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have Ie := B.cur.inv
  have hE := Ie.heap.hi
  have hm := B.mono
  have hlo := Ih.heap.lo
  have slot (j : Nat) (hj : 8 ≤ j) (hj2 : j ≤ 1344) (h1 : j ≤ 1104 ∨ 1144 ≤ j)
      (h2 : j ≤ 104 ∨ 304 ≤ j) :
      t.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = e.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    B.slots j hj hj2 (blkW_miss hpre hj hj2 h1 h2)
  have e1304 := slot 1304 (by omega) (by omega) (by omega) (by omega)
  have heE : heapNext e ≤ heapEnd := le_trans hm hE
  have hfb := X.fwBuf
  have htb := En.tbBuf
  have x20 : t.getReg .x20 = e.getReg .x20 := B.regs .x20 (by decide)
  refine ⟨B.mm, ⟨?_, ?_, (slot 1288 (by omega) (by omega) (by omega) (by omega)).trans X.m1288,
    (slot 1296 (by omega) (by omega) (by omega) (by omega)).trans X.m1296, ?_,
    (B.regs .x25 (by decide)).trans X.x25⟩, B.acc, ?_, ?_,
    (B.regs .x22 (by decide)).trans En.x22,
    (slot 1176 (by omega) (by omega) (by omega) (by omega)).trans En.i1176,
    (slot 1184 (by omega) (by omega) (by omega) (by omega)).trans En.i1184⟩
  · rw [show t.getMem (s.getReg .x2 - 1304) = e.getMem (s.getReg .x2 - 1304) from e1304,
      eListAt_heapKept B.hk heE (le_refl _) hfb (le_refl _)]
    exact X.fw
  · rw [show t.getMem (s.getReg .x2 - 1304) = e.getMem (s.getReg .x2 - 1304) from e1304]
    exact ⟨hfb.1, hfb.2.imp_right fun h ↦ ⟨h.1, le_trans h.2 hm⟩⟩
  · rw [← X.known]
    have e8 : s.getReg .x2 - 320 + 8 = s.getReg .x2 - BitVec.ofNat 64 312 :=
      slot_add (S := s.getReg .x2) (j := 320) (k := 8) (by addr_omega [hb1]) (by omega)
    have e16 : s.getReg .x2 - 320 + 16 = s.getReg .x2 - BitVec.ofNat 64 304 :=
      slot_add (S := s.getReg .x2) (j := 320) (k := 16) (by addr_omega [hb1]) (by omega)
    refine eAt_congr (slot 320 (by omega) (by omega) (by omega) (by omega)) ?_ ?_
    · rw [e8]; exact slot 312 (by omega) (by omega) (by omega) (by omega)
    · rw [e16]; exact slot 304 (by omega) (by omega) (by omega) (by omega)
  · rw [x20, eListAt_heapKept B.hk heE (le_refl _) htb (le_refl _)]
    exact En.tb
  · rw [x20]
    exact ⟨htb.1, htb.2.imp_right fun h ↦ ⟨h.1, le_trans h.2 hm⟩⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
