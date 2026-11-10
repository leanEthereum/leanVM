import Rv64Verifier.Proofs.Walk.R17B

/-!
# `walk` R17, `table_sumcheck`'s precondition

`tfacts`: the transcript at `tp` and the proof it reads apart from a callee's stack and a frame
range; `ro_heap`: a buffer `walk` allocated is read only for a callee writing frame ranges;
`tsPre`: `TableSumcheckPre` at `0x80008010`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime Rv64Verifier.Model
  Rv64Verifier.Transcript Rv64Verifier.Blocks.F4 Rv64Verifier.Bus
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The transcript at `tp` and the proof it reads, for a callee with an `m`-byte stack writing
the frame range `[S - c, S - c + n)`. -/
theorem tfacts {s w : MachineState} (hpre : WalkPre s) (h : Inv s w)
    (hptr : w.getMem (tp s) = s.getReg .x13) {m : Nat} (hm : m ≤ 8736) {c : Word} {k n : Nat}
    (hc : c.toNat = k) (hk1 : 104 + n ≤ k) (hk2 : k ≤ 2656)
    (hap : k ≤ 2080 ∨ 2448 + n ≤ k) :
    Apart (tp s) transcriptSize (stackLo w m) m ∧
      Apart (tp s) transcriptSize (s.getReg .x2 - c) n ∧
      Outside w (tp s) transcriptSize ∧ Apart (tp s) transcriptSize rodataBase rodataSize ∧
      ProofApart w (tp s) (stackLo w m) m ∧ ProofApart w (tp s) (s.getReg .x2 - c) n ∧
      Outside w (proofAt w (tp s)) 48 ∧
      Outside w (streamPtr w (tp s)) (24 * streamLen w (tp s)) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hab := hpre.stack.above
  have hx := hpre.stack.next
  have hro := hpre.stack.rodata
  rw [stackLo_eq] at hab
  rw [stackLo_eq, stack_eq] at hx hro
  have hrb : rodataBase.toNat = 2684354560 := rfl
  have hrs : rodataStart.toNat = 2684354560 := rfl
  have pRO := hpre.proofRO.2.1
  have sRO := hpre.streamRO.2.1
  rw [stackLo_eq, stack_eq] at pRO sRO
  obtain ⟨e0, e1, e2⟩ := proofVals hpre h hptr
  have hsl := stackLo_callee h m
  simp only [heapEnd] at hab
  refine ⟨by rw [hsl, tp]; addr_omega [hb1, hm], by rw [tp]; addr_omega [hb1, hc, hk1, hk2, hap],
    ⟨Or.inr (by rw [tp]; addr_omega [hab, hb1]), by rw [tp]; addr_omega [hx, hb1]⟩,
    by rw [tp]; addr_omega [hro, hrb, hrs, hb1], ?_, ?_,
    by rw [e0]; exact outside_mono' hpre.proofRO.1 h.mono,
    by rw [e1, e2]; exact outside_mono' hpre.streamRO.1 h.mono⟩
  · simp only [ProofApart, e0, e1, e2, hsl]
    exact ⟨by addr_omega [pRO, hb1, hm], by addr_omega [sRO, hb1, hm]⟩
  · simp only [ProofApart, e0, e1, e2]
    exact ⟨by addr_omega [pRO, hb1, hc, hk1, hk2], by addr_omega [sRO, hb1, hc, hk1, hk2]⟩

/-- A buffer below `NEXT` is read only for a callee with a stack below the frame that writes
frame ranges and the sponge. -/
theorem ro_heap {s w : MachineState} (hpre : WalkPre s) (h : Inv s w) {m : Nat} (hm : m ≤ 8736)
    {ws : List (Word × Nat)} (hws : ∀ x ∈ ws, (s.getReg .x2 - 2656).toNat ≤ x.1.toNat)
    {a : Word} {n : Nat} (ha : a.toNat % 8 = 0) (hn : a.toNat + n ≤ heapNext w)
    (hlo : n = 0 ∨ heapStart ≤ a.toNat) : RO w m ws (tp s) a n := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hab := hpre.stack.above
  rw [stackLo_eq] at hab
  have hh := h.heap.hi
  have hsl := stackLo_callee h m
  simp only [heapEnd, heapNext, heapStart] at hab hh hn hlo
  refine ⟨?_, ⟨Or.inl hn, by addr_omega [hn, hh]⟩, by rw [hsl]; addr_omega [hn, hh, hab, hb1, hm],
    fun x hx ↦ ?_, by rw [tp]; addr_omega [hn, hh, hab, hb1]⟩
  · rcases hlo with h0 | h0
    · exact Or.inl h0
    · exact Or.inr ⟨Or.inl ⟨by omega, by omega⟩, ha⟩
  · have := hws x hx; addr_omega [hn, hh, hab, hb1, this]

end Rv64Verifier.Proofs.Walk
