import Rv64Verifier.Proofs.Layout.VecLemmas
import Rv64Verifier.Proofs.Layout.Grow

/-!
# Room for one more element

`Flushes::pair` makes room on each side the same way: if the `Vec` is full, a three-step block calls
`grow_one` on it, which returns where the code goes on when there is room. `room` gives the state
there: the `Vec`'s length unchanged, room for one more, its buffer the old one or a fresh one that
starts with the old elements (`Room`).
-/

namespace Rv64Verifier.Layout
open RiscvZkvm.Rv64 Rv64Verifier.Runtime

/-- Two ranges no byte of which is in both are apart. -/
theorem apart_of_forall {a b : Word} {n m : Nat} (h : ∀ x, Within x a n → ¬ Within x b m) :
    Apart a n b m := by
  refine Classical.byContradiction fun hn ↦ ?_
  simp only [Apart, not_or] at hn
  have hlt : max a.toNat b.toNat < 2 ^ 64 := by have := a.isLt; have := b.isLt; omega
  refine h (BitVec.ofNat 64 (max a.toNat b.toNat)) ?_ ?_ <;>
    simp only [Within, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] <;> omega

/-- From `x` to `u`, the `Vec` at `v` (24-byte elements) got room for one more. -/
structure Room (x u : MachineState) (v : Word) : Prop where
  heap : HeapOk u
  mono : heapNext x ≤ heapNext u
  room : (vecLen x v).toNat < (vecCap u v).toNat
  len : vecLen u v = vecLen x v
  raw : RawVecOk u v 24 8
  ptr : (vecPtr u v = vecPtr x v ∧ vecCap u v = vecCap x v) ∨ heapNext x ≤ (vecPtr u v).toNat
  copy : ∀ j, j % 8 = 0 → j + 8 ≤ 24 * (vecLen x v).toNat →
    u.getMem (vecPtr u v + BitVec.ofNat 64 j) = x.getMem (vecPtr x v + BitVec.ofNat 64 j)
  frame : DFrame x u fun y ↦ Within y v 16 ∨ Within y (stackLo x growOneStack) growOneStack ∨
    Within y nextAddr 8 ∨ Fresh x u y

/-- No growth. -/
theorem Room.refl {x : MachineState} {v : Word} (hheap : HeapOk x) (hv : VecOk x v 24 8)
    (hne : vecLen x v ≠ vecCap x v) : Room x x v where
  heap := hheap
  mono := Nat.le_refl _
  room := by
    have := hv.len
    have : (vecLen x v).toNat ≠ (vecCap x v).toNat := fun h ↦ hne (BitVec.eq_of_toNat_eq h)
    omega
  len := rfl
  raw := hv.raw
  ptr := Or.inl ⟨rfl, rfl⟩
  copy := fun _ _ _ ↦ rfl
  frame := DFrame.refl _ _

/-- `grow_one`, then. -/
theorem room (hG : GrowOneFreshSpec 0x80011c78 24 8) {x : MachineState} {v c : Word}
    (hv : VecOk x v 24 8) (hheap : HeapOk x) (hself : ValidMemRange v 2)
    (hstack : RtStack x growOneStack) (hfree : Outside x v 24)
    (hvs : Apart v 24 (stackLo x growOneStack) growOneStack)
    (hfull : vecLen x v = vecCap x v)
    (hcall : ∃ z, Reaches Image.code x z ∧ z.pc = 0x80011c78 ∧ z.getReg .x10 = v ∧
      z.getReg .x1 = c ∧ (∀ r ∈ calleeSaved, z.getReg r = x.getReg r) ∧
      ∀ a, z.getMem a = x.getMem a)
    (hc : c &&& 0xfffffffffffffffe = c) :
    ∃ u, Reaches Image.code x u ∧ ((u.pc = c ∧ (∀ r ∈ calleeSaved, u.getReg r = x.getReg r) ∧
      Room x u v) ∨ Dead Image.code u) := by
  obtain ⟨z, hrz, hpcz, hz10, hz1, hzr, hzm⟩ := hcall
  have hnz : heapNext z = heapNext x := by simp only [heapNext, hzm]
  have hsp : z.getReg .x2 = x.getReg .x2 := hzr .x2 (by decide)
  have hlo : stackLo z growOneStack = stackLo x growOneStack := by simp only [stackLo, hsp]
  have hvb := ValidMemRange.bounds hself (by decide)
  have hpre : GrowOnePre 24 8 z := {
    heap := ⟨hnz ▸ hheap.lo, hnz ▸ hheap.hi⟩
    self := by rw [hz10]; exact hself
    raw := by
      rw [hz10]
      have := hv.raw
      simp only [RawVecOk, Buf, vecPtr, vecCap, hzm, hnz] at this ⊢
      exact this
    stack := by
      have hb := hstack
      exact ⟨⟨by rw [hlo]; exact hb.valid, by rw [hsp]; exact hb.aligned⟩, by rw [hlo]; exact hb.above,
        by rw [hlo]; exact hb.next, by rw [hlo]; exact hb.rodata⟩
    selfFree := by
      rw [hz10]; simp only [Outside, hnz] at hfree ⊢
      exact ⟨by omega, by addr_omega [hfree.2, hvb]⟩
    selfStack := by rw [hz10, hlo]; addr_omega [hvs, hvb] }
  obtain ⟨u, hru, ⟨hpcu, hpres, hpost, hfresh⟩ | hdead⟩ := hG.call hrz hpcz hpre
  swap
  · exact ⟨u, hru, Or.inr hdead⟩
  rw [hz10] at hfresh
  have hcapz : vecCap z v = vecCap x v := by simp only [vecCap, hzm]
  have hptrz : vecPtr z v = vecPtr x v := by simp only [vecPtr, hzm]
  have hlenz : vecLen z v = vecLen x v := by simp only [vecLen, hzm]
  have hf := hpost.frame.dframe
  simp only [hz10, hlo] at hf
  have hlenu : vecLen u v = vecLen x v := by
    rw [← hlenz]
    refine hf.getMem_of (fun y hy h ↦ ?_) (by addr_omega [hvb])
    have hhi := hpost.heap.hi
    simp only [heapEnd, heapNext] at hhi
    rcases h with h | h | h | h
    · addr_omega [hy, h, hvb]
    · addr_omega [hy, h, hvs, hvb]
    · simp only [Outside] at hfree; addr_omega [hy, h, hfree, hvb]
    · simp only [Fresh, Outside, heapNext] at h hfree
      rw [show z.getMem nextAddr = x.getMem nextAddr from hzm _] at h
      addr_omega [hy, h, hfree, hvb, hhi]
  refine ⟨u, hru, Or.inl ⟨by rw [hpcu, returnAddress_eq, hz1]; exact hc,
    fun r hr ↦ (hpres r hr).trans (hzr r hr), ⟨hpost.heap, hnz ▸ hpost.mono, ?_, hlenu,
      hz10 ▸ hpost.raw, Or.inr (hnz ▸ hfresh), fun j hj hjN ↦ ?_, ?_⟩⟩⟩
  · have := hpost.cap
    rw [hz10, hcapz] at this
    rw [hfull]; omega
  · have hb := hpost.bytes
    rw [hz10, hcapz, hptrz] at hb
    have hraw := hpost.raw
    rw [hz10] at hraw
    have hrawx := hv.raw
    simp only [RawVecOk, Buf] at hraw hrawx
    rw [← hptrz]
    have := getMem_eq_of_bytesAt (s := z) hb hraw.1 hrawx.1 hj (by
      rw [hfull] at hjN; rw [Nat.mul_comm]; exact hjN)
    rw [this, hptrz]
    exact hzm _
  · exact ((DFrame.of_same hzm fun _ ↦ False).union hf).mono fun y hy ↦ by
      rcases hy with hy | hy
      · exact hy.elim
      · rcases hy with hy | hy | hy | hy
        · exact Or.inl hy
        · exact Or.inr (Or.inl hy)
        · exact Or.inr (Or.inr (Or.inl hy))
        · exact Or.inr (Or.inr (Or.inr (by simpa only [Fresh, hnz] using hy)))

end Rv64Verifier.Layout
