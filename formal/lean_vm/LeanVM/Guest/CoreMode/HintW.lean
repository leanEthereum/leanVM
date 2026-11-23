/-
  LeanVM.Guest.CoreMode.HintW

  What a flow hint with a heap destination writes: its run of cells from its pointer's exponent.
-/

module

public import LeanVM.Guest.Mode.SoundHint

/-!
# Heap hints write their destinations

`isaHeap h`: an ISA hint's heap destination (its pointer's frame cell, the offset of the first word,
their number). `hints_heap`: after the hints at a pc ran, each such hint's pointer cell holds `g^b`
and the cells `b + lo + j`, `j < len`, are written.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Prover.Exec
open LeanVM.Guest.Mode (heapBase_val pop_len withMem_putRun written_of_get written_mono)

@[expose] public section

/-- **An ISA hint's heap destination**: its pointer's frame cell, the offset of its first word, their
number. -/
def isaHeap : Hint → Option (ℕ × ℕ × ℕ)
  | .witnessHeap _ ptr lo len => some (ptr, lo, len)
  | .bitDecompose _ (.heap ptr) n => some (ptr, 0, n)
  | .bitDecomposeExp _ (.heap ptr) n => some (ptr, 0, n)
  | .windowsExp _ (.heap ptr) pos _ _ count => some (ptr, pos, count)
  | .digitDecomposeExp _ (.heap ptr) _ nd _ _ _ => some (ptr, 0, nd)
  | _ => none

theorem heapBase_ok {s s1 : St} {c b : ℕ} {what : String} (hs : s.Good) (h : heapBase s c what = .ok (b, s1)) :
    St.Follows s s1 ∧ s1.mem = s.mem ∧ s.mem.get c = some (ofK (g ^ b)) := by
  have hw : s.mem.written c = true := by
    have h' := h
    unfold heapBase at h'
    rw [bind_ok] at h'
    obtain ⟨x, hx, h'⟩ := h'
    obtain ⟨-, hg, -⟩ := St.logOr_ok hs h'
    obtain ⟨-, rfl⟩ := inK_ok hx
    cases hget : s.mem.get c with
    | some v => simp [Mem.written, hget]
    | none =>
      simp only [Mem.peek, hget, Option.getD_none] at hg
      have h0 : (0 : E) = ofK 0 := by simp
      rw [h0, limb_ofK] at hg
      exact absurd (by simpa using hg) (pow_ne_zero b g_ne_zero)
  obtain ⟨f, hm, p, hp, rfl, -⟩ := heapBase_val hs h hw
  exact ⟨f, hm, hp⟩

theorem bitsBase_heap {s s1 : St} {ptr len b : ℕ} {what : String} (hs : s.Good)
    (h : bitsBase s (.heap ptr) len what = .ok (b, s1)) :
    St.Follows s s1 ∧ s.mem.get (s.fp + ptr) = some (ofK (g ^ b)) := by
  simp only [bitsBase, bind_ok, pure_ok, Prod.mk.injEq] at h
  obtain ⟨c, hc, ⟨b', s2⟩, h1, c2, hc2, hb, hs2⟩ := h
  subst hb hs2
  obtain ⟨rfl, -⟩ := cellAt_ok hc
  obtain ⟨rfl, -⟩ := runAt_ok hc2
  obtain ⟨f, _, hp⟩ := heapBase_ok hs h1
  exact ⟨f, by simpa using hp⟩

/-- **One hint with a heap destination** wrote its cells. -/
theorem runHint_heap {C : Ctx} {s s' : St} {h : Hint} (hs : s.Good) (e : runHint C s h = .ok s')
    {ptr lo len : ℕ} (hd : isaHeap h = some (ptr, lo, len)) :
    ∃ b, s.mem.get (s.fp + ptr) = some (ofK (g ^ b)) ∧ ∀ j < len, s'.mem.written (b + lo + j) = true := by
  cases h with
  | witnessHeap name ptr' lo' len' =>
    simp only [isaHeap, Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl, rfl⟩ := hd
    simp only [runHint, bind_ok] at e
    obtain ⟨c, hc, ⟨b, s1⟩, h1, bl, hbl, ⟨v, s2⟩, h2, e⟩ := e
    obtain ⟨rfl, -⟩ := cellAt_ok hc
    obtain ⟨rfl, -⟩ := runAt_ok hbl
    obtain ⟨f1, -, hp⟩ := heapBase_ok hs h1
    obtain ⟨hl, f2, -⟩ := pop_len f1.good h2
    obtain ⟨-, -, hv⟩ := withMem_putRun f2.good e
    subst hl
    exact ⟨b, hp, fun j hj ↦ written_of_get (hv j hj)⟩
  | bitDecompose value bits nbits =>
    cases bits with
    | stack _ => simp [isaHeap] at hd
    | heap ptr' =>
      simp only [isaHeap, Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl, rfl⟩ := hd
      simp only [runHint, bind_ok] at e
      obtain ⟨c, -, ⟨b, s1⟩, h1, e⟩ := e
      obtain ⟨f1, hp⟩ := bitsBase_heap hs h1
      obtain ⟨-, -, hv⟩ := withMem_putRun f1.good e
      exact ⟨b, hp, fun j hj ↦ written_of_get (by simpa using hv j (by simpa using hj))⟩
  | bitDecomposeExp value bits nbits =>
    cases bits with
    | stack _ => simp [isaHeap] at hd
    | heap ptr' =>
      simp only [isaHeap, Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl, rfl⟩ := hd
      simp only [runHint, bind_ok] at e
      obtain ⟨c, -, n, -, ⟨b, s1⟩, h1, e⟩ := e
      obtain ⟨f1, hp⟩ := bitsBase_heap hs h1
      obtain ⟨-, -, hv⟩ := withMem_putRun f1.good e
      exact ⟨b, hp, fun j hj ↦ written_of_get (by simpa using hv j (by simpa using hj))⟩
  | windowsExp value bits pos start width count =>
    cases bits with
    | stack _ => simp [isaHeap] at hd
    | heap ptr' =>
      simp only [isaHeap, Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl, rfl⟩ := hd
      simp only [runHint, bind_ok] at e
      obtain ⟨c, -, ⟨b, s1⟩, h1, e⟩ := e
      obtain ⟨f1, hp⟩ := bitsBase_heap hs h1
      obtain ⟨-, -, hv⟩ := withMem_putRun f1.good e
      exact ⟨b, hp, fun j hj ↦ written_of_get (by simpa using hv j (by simpa using hj))⟩
  | digitDecomposeExp value bits nbits ndigits digitBits start startCell =>
    cases bits with
    | stack _ => simp [isaHeap] at hd
    | heap ptr' =>
      simp only [isaHeap, Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl, rfl⟩ := hd
      simp only [runHint, bind_ok] at e
      obtain ⟨c, -, n, -, e⟩ := e
      have key : ∀ st, (do
          let __x ← bitsBase s (BitsDest.heap ptr') ndigits "hint_decompose_digits_exponent pointer"
          __x.2.withMem (putRun __x.1 ((List.range ndigits).map fun j ↦ ofK (g ^ if 128 ≤ st + digitBits * j then 0
            else n >>> (st + digitBits * j) % 2 ^ digitBits)))) = Except.ok s' →
          ∃ b, s.mem.get (s.fp + ptr') = some (ofK (g ^ b)) ∧ ∀ j < ndigits, s'.mem.written (b + 0 + j) = true := by
        intro st e
        rw [bind_ok] at e
        obtain ⟨⟨b, s1⟩, h1, e⟩ := e
        obtain ⟨f1, hp⟩ := bitsBase_heap hs h1
        obtain ⟨-, -, hv⟩ := withMem_putRun f1.good e
        exact ⟨b, hp, fun j hj ↦ written_of_get (by simpa using hv j (by simpa using hj))⟩
      cases startCell with
      | none => simpa using key start e
      | some c =>
        rw [bind_ok] at e
        obtain ⟨l, -, e⟩ := e
        rw [bind_ok] at e
        obtain ⟨st, -, e⟩ := e
        exact key st e
  | _ => simp [isaHeap] at hd

/-- **The hints at a pc with a heap destination wrote their cells** by the end of the hints. -/
theorem hints_heap {C : Ctx} : ∀ (l : List Hint) {s s1 : St}, s.Good → l.foldlM (runHint C) s = .ok s1 →
    ∀ h ∈ l, ∀ {ptr lo len : ℕ}, isaHeap h = some (ptr, lo, len) →
      ∃ b, s1.mem.get (s.fp + ptr) = some (ofK (g ^ b)) ∧ ∀ j < len, s1.mem.written (b + lo + j) = true
  | [], _, _, _, _, _, hh, _, _, _, _ => by cases hh
  | x :: l, s, s1, hs, e, h, hh, ptr, lo, len, hd => by
    rw [List.foldlM_cons, bind_ok] at e
    obtain ⟨s2, e2, e⟩ := e
    have f2 := runHint_follows hs e2
    have f3 := hints_follows l s2 s1 f2.good e
    rcases List.mem_cons.mp hh with rfl | hh
    · obtain ⟨b, hp, hw⟩ := runHint_heap hs e2 hd
      exact ⟨b, f3.le.get _ _ (f2.le.get _ _ hp), fun j hj ↦ written_mono f3.le (hw j hj)⟩
    · obtain ⟨b, hp, hw⟩ := hints_heap l f2.good e h hh hd
      exact ⟨b, by rw [← f2.fp]; exact hp, hw⟩

end

end LeanVM.Guest.CoreMode
