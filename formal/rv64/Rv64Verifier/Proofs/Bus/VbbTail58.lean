import Rv64Verifier.Proofs.Bus.VbbTail57

/-!
# `verify_bus_balance`'s side loop: the invariant at the block loop's entry

From the side loop's head `h` to a state `e` that wrote only `FrW` (`Front.fr` and what follows it
before the block loop), the invariant's matrix, forms and totals hold at `e` as the block loop's
memory invariant with no block done (`Sides.mm`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript

theorem FrW.mono {s h u u' : MachineState} (hu : heapNext u ≤ heapNext u') {a : Word}
    (ha : FrW s h u a) : FrW s h u' a := by
  rcases ha with ha | ha | ha | ha | ha | ha | ha | ⟨a1, a2⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a1, by omega⟩))))))

/-- A heap address below `h`'s `NEXT` misses `FrW`. -/
theorem FrW.low {s h u : MachineState} (hpre : BusBalancePre s) (hh : HeapOk h) {a : Word}
    (h1 : heapStart ≤ a.toNat) (h2 : a.toNat < heapNext h) : ¬ FrW s h u a := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hE := hh.hi
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

/-- The totals' header misses `FrW`. -/
theorem FrW.totals {s h u : MachineState} (hpre : BusBalancePre s) (hu : HeapOk u) (q : Nat)
    (hq : q < 24) : ¬ FrW s h u (s.getReg .x2 - 632 + BitVec.ofNat 64 q) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hnx := hpre.stack.next
  rw [stackLo_eq] at hnx
  have hE := hu.hi
  simp only [heapNext, heapEnd] at hE
  rintro (hw | hw | hw | hw | hw | hw | hw | ⟨-, hw⟩)
  · addr_omega [hw, hq, hb1]
  · addr_omega [hw, hq, hb1]
  · addr_omega [hw, hq, hb1]
  · addr_omega [hw, hq, hb1]
  · addr_omega [hw, hq, hb1]
  · addr_omega [hw, hq, hb1]
  · addr_omega [hw, hq, hb1, hnx]
  · simp only [heapNext] at hw; addr_omega [hw, hq, hb1, hE]

/-- The invariant at a state past the head that wrote only `FrW`, as `Mm` with no block done. -/
theorem Sides.mm {s z h₀ h e : MachineState} {P : Word} {n : Nat}
    {acc : List (List Form) × List E} (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z)
    (hPb : n = 0 ∨ heapNext z ≤ P.toNat) (Sd : Sides s z h₀ h P n acc) (Ce : Cur s z h e) (fr : DFrame h e (FrW s h e)) :
    Mm s z h e e P n acc.1 acc.2 := by
  have Ih := Sd.inv
  have hhE := Ih.heap.hi
  have hm := Ce.step.mono
  have hz := Sd.mat.mono
  have hlo := hpre.heap.lo
  have hw (x : Word) (h1 : heapStart ≤ x.toNat) (h2 : x.toNat + 8 ≤ heapNext h) :
      e.getMem x = h.getMem x :=
    fr x fun q hq ↦ FrW.low hpre Ih.heap
      (by simp only [heapStart, heapNext, heapEnd] at h1 h2 hhE ⊢; addr_omega [h1, h2, hq, hhE])
      (by simp only [heapStart, heapNext, heapEnd] at h1 h2 hhE ⊢; addr_omega [h1, h2, hq, hhE])
  obtain ⟨M', hrow, hcell, hform⟩ := Sd.mat.keep Ih.heap hm hPb fun x h1 h2 ↦
    hw x (by simp only [heapStart, heapNext] at h1 hz hsz hlo ⊢; omega) h2
  have pe (a : Nat) (ha : a < n) (j : Nat) (hj : j ≤ 3) (x : Word) :
      piece e P a j x ↔ piece h P a j x :=
    piece_congr (hrow a ha) (fun h3 k hk ↦ hcell a ha j h3 k hk) x
  have h632 (q : Nat) (hq : q + 8 ≤ 24) : e.getMem (s.getReg .x2 - 632 + BitVec.ofNat 64 q) =
      h.getMem (s.getReg .x2 - 632 + BitVec.ofNat 64 q) :=
    fr _ fun r hr ↦ by rw [add_ofNat_add]; exact FrW.totals hpre Ce.inv.heap _ (by omega)
  have tp : vecPtr e (s.getReg .x2 - 632) = vecPtr h (s.getReg .x2 - 632) := h632 8 (by omega)
  have tc : vecCap e (s.getReg .x2 - 632) = vecCap h (s.getReg .x2 - 632) := by
    have := h632 0 (by omega); simp only [add_ofNat_zero] at this; exact this
  have TB := Sd.totals
  refine ⟨Ce, fun _ _ _ _ ↦ rfl, M', fun a ha j hj ↦ ?_, ?_, fun a ha j hj x hx ↦
    Or.inl (Sd.mat.below ha hj ((pe a ha j hj x).mp hx)).2, le_refl _, fun _ _ _ ↦ rfl, ?_,
    fun x hx ↦ ?_⟩
  · have hptr : vecPtr e (rowAt P a) = vecPtr h (rowAt P a) := by
      have h := hrow a ha 1 (by omega); simp only [Nat.mul_one] at h; exact h
    have hc : cellAt e (rowAt P a) j = cellAt h (rowAt P a) j := by simp only [cellAt, hptr]
    have ep : vecPtr e (cellAt h (rowAt P a) j) = vecPtr h (cellAt h (rowAt P a) j) := by
      simpa [vecPtr] using hcell a ha j hj 1 (by omega)
    have el : vecLen e (cellAt h (rowAt P a) j) = vecLen h (cellAt h (rowAt P a) j) := by
      simpa [vecLen] using hcell a ha j hj 2 (by omega)
    rw [hc, ep, el]
    exact le_trans (Sd.below a ha j hj) hm
  · rw [formRowsAt_keep (fun a ha ↦ (Sd.mat.rows a ha).2) hrow hform]; exact Sd.forms
  · refine TB.dframe' fr hm (fun q hq ↦ FrW.totals hpre Ce.inv.heap q hq) fun q hq hw' ↦ ?_
    have hl := TB.vec.len
    have hbuf := TB.buf
    simp only [NewBuf] at hbuf
    rcases hbuf.2 with h0 | ⟨b1, b2⟩
    · omega
    · refine FrW.low hpre Ih.heap ?_ ?_ hw'
      · simp only [heapStart, heapNext] at b1 hsz hlo hz ⊢
        addr_omega [b1, b2, hq, hl, hhE, hsz, hlo, hz]
      · simp only [heapNext, heapEnd] at b2 hz hhE ⊢; addr_omega [b1, b2, hq, hl, hhE]
  · rw [tp, tc] at hx
    obtain ⟨t1, t2⟩ := Sd.tbuf x hx
    exact ⟨t1, fun a ha j hj hp ↦ t2 a ha j hj ((pe a ha j hj x).mp hp)⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
