import Rv64Verifier.Proofs.Bus.VbbBase
import Rv64Verifier.Blocks.F26

/-!
# `verify_bus_balance`: steps, and the calls of `bus_layout`

A `Step s v w lo n` writes only the `n` bytes from `lo` in the frame, the stack below the frame,
`NEXT` and the heap it allocates: what every block and call past the prologue does. It keeps `Inv`
and whatever lies apart from `[lo, lo + n)`. `layoutCall` is a call of `bus_layout` from any of the
three sites (`0x800064a4`, `0x800064c8`, `0x800064ec`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Model
  Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem outside_mono {s u : MachineState} {a : Word} {n : Nat} (h : Outside s a n)
    (hm : heapNext s ≤ heapNext u) : Outside u a n := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, h2⟩
  rcases h1 with h1 | h1
  · exact Or.inl (by omega)
  · exact Or.inr h1

/-- What a step past the prologue may write: `n` bytes from `lo`, the stack below the frame,
`NEXT`, the heap it allocates. -/
def Below (s v w : MachineState) (lo : Word) (n : Nat) (a : Word) : Prop :=
  Within a lo n ∨ Within a (s.getReg .x2 - 4544) 3200 ∨ Within a nextAddr 8 ∨ Fresh v w a

/-- A step from `v` to `w` writing `Below`, keeping `sp`. -/
structure Step (s v w : MachineState) (lo : Word) (n : Nat) : Prop where
  frame : DFrame v w (Below s v w lo n)
  heap : HeapOk w
  mono : heapNext v ≤ heapNext w
  sp : w.getReg .x2 = v.getReg .x2

/-- The `n` bytes from `lo` lie in the frame, below the saved registers. -/
def InFrame (s : MachineState) (lo : Word) (n : Nat) : Prop :=
  (s.getReg .x2 - 1344).toNat ≤ lo.toNat ∧ lo.toNat + n ≤ (s.getReg .x2 - 104).toNat

theorem Below.loc {s v w : MachineState} (hpre : BusBalancePre s) {lo : Word} {n : Nat}
    (hl : InFrame s lo n) {a : Word} (ha : Below s v w lo n a) : Loc s v w a := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  simp only [InFrame] at hl
  rcases ha with ha | ha | ha | ha
  · exact Or.inl (by addr_omega [ha, hl, hb1])
  · exact Or.inl (by addr_omega [ha, hb1])
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr ha)

theorem Inv.after {s v w : MachineState} (hpre : BusBalancePre s) (h : Inv s v) {lo : Word}
    {n : Nat} (hl : InFrame s lo n) (st : Step s v w lo n) : Inv s w :=
  h.loc hpre (st.frame.mono fun _ ha ↦ Below.loc hpre hl ha) st.heap st.mono st.sp

theorem Step.trans {s u v w : MachineState} {lo : Word} {n : Nat} (h₁ : Step s u v lo n)
    (h₂ : Step s v w lo n) : Step s u w lo n where
  frame := (h₁.frame.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ⟨f1, f2⟩
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ⟨f1, by have := h₂.mono; omega⟩))).trans h₂.frame
    fun a ha ↦ by
      rcases ha with ha | ha | ha | ⟨f1, f2⟩
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ⟨by have := h₁.mono; omega, f2⟩))
  heap := h₂.heap
  mono := h₁.mono.trans h₂.mono
  sp := h₂.sp.trans h₁.sp

/-- A word apart from what a step writes, and below `NEXT`'s old value or in the frame, keeps
its value. -/
theorem Step.word {s v w : MachineState} (hpre : BusBalancePre s) {lo : Word} {n : Nat}
    (st : Step s v w lo n) {x : Word} (hx : Apart x 8 lo n)
    (hy : (s.getReg .x2 - 1344).toNat ≤ x.toNat ∧ x.toNat + 8 ≤ (s.getReg .x2).toNat ∨
      heapStart ≤ x.toNat ∧ x.toNat + 8 ≤ heapNext v) : w.getMem x = v.getMem x := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hh := st.heap.hi
  have hm := st.mono
  refine st.frame x fun i hi hw ↦ ?_
  simp only [Below, Fresh, heapNext] at hw hy hh hm
  simp only [heapStart] at hy
  rcases hy with hy | hy <;> rcases hw with hw | hw | hw | hw <;>
    addr_omega [hx, hy, hw, hi, hb1, hb2, hh, hm]

theorem inFrame {s : MachineState} (hpre : BusBalancePre s) {k n : Nat} (hk1 : 104 + n ≤ k)
    (hk2 : k ≤ 1344) : InFrame s (s.getReg .x2 - BitVec.ofNat 64 k) n := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  simp only [InFrame]
  constructor <;> addr_omega [hb1, hk1, hk2]

/-- The `n` bytes at `S - k` in the frame: a region, outside the free heap, apart from the stack
below `S - 1344`. -/
theorem frameSlot {s u : MachineState} (hpre : BusBalancePre s) (h : Inv s u) {k n m : Nat}
    (hk1 : 104 + n ≤ k) (hk2 : k ≤ 1344) (hk8 : k % 8 = 0) (hm : 1344 + m ≤ 4544) :
    Region (s.getReg .x2 - BitVec.ofNat 64 k) n ∧
      Outside u (s.getReg .x2 - BitVec.ofNat 64 k) n ∧
      Apart (s.getReg .x2 - BitVec.ofNat 64 k) n (stackLo u m) m := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have ha := hpre.stack.above
  rw [stackLo_eq] at ha
  have hh := h.heap.hi
  simp only [Region, Mapped, Outside, stackLo, h.sp, heapEnd, heapNext] at ha hh ⊢
  refine ⟨⟨Or.inr ⟨?_, ?_⟩, ?_⟩, ⟨Or.inr ?_, ?_⟩, ?_⟩ <;>
    addr_omega [hb1, hb2, hb3, hk1, hk2, hk8, ha, hm]

/-- A call of `bus_layout`, its result at `S - k`. -/
theorem layoutCall (hBL : BusLayoutSpec) {s u₀ u : MachineState} (hpre : BusBalancePre s)
    (h : Inv s u) (hr : Reaches Image.code u₀ u) (hpc : u.pc = 0x80010acc) {k : Nat}
    (hout : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 k) (hk1 : 160 ≤ k) (hk2 : k ≤ 1344)
    (hk8 : k % 8 = 0)
    (hrows : LayoutRead u (u.getReg .x10) (u.getReg .x11) (8 * (u.getReg .x12).toNat))
    (hblocks : RO s busBalanceStack [(s.getReg .x10, 120)] (s.getReg .x12) (u.getReg .x13)
      (48 * (u.getReg .x14).toNat)) :
    ∃ v, Reaches Image.code u₀ v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧
      BusLayoutPost u v ∧
      Step s u v (s.getReg .x2 - BitVec.ofNat 64 k) 56) ∨ Dead Image.code v) := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  obtain ⟨o1, o2, o3⟩ := frameSlot (m := busLayoutStack) hpre h (n := 56) (by omega) hk2 hk8
    (by decide)
  have hsl : stackLo u busLayoutStack = s.getReg .x2 - 1616 := by
    show u.getReg .x2 - BitVec.ofNat 64 272 = _
    rw [h.sp]; addr_omega [hb1]
  have pre : BusLayoutPre u := {
    heap := h.heap
    stack := hpre.stack.sub 1344 h.sp (by decide) (by decide) (by decide) (by decide) (by decide)
    out := hout ▸ o1
    outFree := hout ▸ o2
    outStack := hout ▸ o3
    rows := hrows
    blocks := by
      have hs := hblocks.stack
      rw [stackLo_eq] at hs
      refine ⟨hblocks.region, outside_mono hblocks.free h.mono, ?_, ?_⟩
      · rw [hsl]; addr_omega [hs, hb1]
      · rw [hout]; addr_omega [hs, hb1, hk1, hk2] }
  obtain ⟨v, hrv, ⟨hpcv, hp, post⟩ | hd⟩ := hBL.call hr hpc pre
  · refine ⟨v, hrv, Or.inl ⟨hpcv, hp, post, post.frame.mono fun a ha ↦ ?_, post.heap,
      post.mono, hp.reg .x2⟩⟩
    rw [hsl, hout] at ha
    rcases ha with ha | ha | ha | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr ha))
  · exact ⟨v, hrv, Or.inr hd⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
