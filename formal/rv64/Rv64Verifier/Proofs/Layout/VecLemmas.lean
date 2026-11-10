import Rv64Verifier.Proofs.Layout.ReprVec

/-!
# Moving and pushing `Vec<Form>`s

A `Vec<Form>` header copied elsewhere (a push, a buffer's growth) reads as the same value, so long
as its deep footprint is kept (`formVecOf_moved`); a `Vec<Vec<Form>>` whose old elements' headers
and a new one were written to its buffer reads as the old value with the new one pushed
(`formVecsOf_push`). Everything a sound value reaches is allocated (`FormVecOk.deep_below`).
-/

namespace Rv64Verifier.Layout
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Model.LayoutMirror

/-- A form's buffer is in the heap below `NEXT`. -/
theorem FormOk.buf_below {s : MachineState} {a x : Word} (h : FormOk s a) (hx : formBuf s a x) :
    heapStart ≤ x.toNat ∧ x.toNat < heapNext s := by
  have hraw := h.vec.raw
  simp only [RawVecOk, Buf] at hraw
  simp only [formBuf, Within] at hx
  rcases hraw.2 with h0 | h0 <;> omega

/-- Everything a sound `Vec<Form>` reaches is in the heap below `NEXT`. -/
theorem FormVecOk.deep_below {s : MachineState} {a x : Word} (h : FormVecOk s a)
    (hx : formVecDeep s a x) : heapStart ≤ x.toNat ∧ x.toNat < heapNext s := by
  rcases hx with hx | ⟨i, hi, hx⟩
  · have hraw := h.vec.raw
    simp only [RawVecOk, Buf] at hraw
    simp only [formVecBuf, Within] at hx
    rcases hraw.2 with h0 | h0 <;> omega
  · exact (h.forms i hi).buf_below hx

/-- A `Vec<Form>` header copied from `e` in `s` to `e'` in `t` reads as the same value, and is sound
with the same deep footprint, if the frame keeps that footprint. -/
theorem formVecOf_moved {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {e e' : Word}
    (h0 : t.getMem e' = s.getMem e) (h8 : t.getMem (e' + 8) = s.getMem (e + 8))
    (h16 : t.getMem (e' + 16) = s.getMem (e + 16)) (hok : FormVecOk s e)
    (hd : ∀ x, formVecDeep s e x → ¬ w x) (hheap : HeapOk s) (hmono : heapNext s ≤ heapNext t) :
    formVecOf t e' = formVecOf s e ∧ FormVecOk t e' ∧ formVecDeep t e' = formVecDeep s e := by
  have hptr : vecPtr t e' = vecPtr s e := h8
  have hln : vecLen t e' = vecLen s e := h16
  have hcp : vecCap t e' = vecCap s e := h0
  have hb := vecBuf_bounds hok.vec (by decide)
  have hlen := hok.vec.len
  have hhw : (vecPtr s e).toNat + 24 * (vecLen s e).toNat ≤ 2 ^ 64 := by
    have := (s.getMem nextAddr).isLt
    have := (vecPtr s e).isLt
    simp only [heapNext] at hb
    rcases hb.2 with h0 | h0 <;> omega
  have hhd : ∀ x, Within x (vecPtr s e) (24 * (vecLen s e).toNat) → ¬ w x := fun x hx ↦
    hd x (Or.inl (by
      simp only [formVecBuf]
      rcases hb.2 with h0 | h0
      · exfalso; simp only [Within] at hx; omega
      · simp only [Within] at hx ⊢; omega))
  have hf := formsAt_frame h hok.forms hhd (fun x hx ↦ hd x (Or.inr hx)) hhw hheap hmono
  have hfb : formVecBuf t e' = formVecBuf s e := by
    funext x; simp only [formVecBuf, hptr, hcp]
  have hds : formsDeep t (vecPtr t e') (vecLen t e').toNat =
      formsDeep s (vecPtr s e) (vecLen s e).toNat := by
    rw [hptr, hln, formsDeep_frame h hhd hhw]
  refine ⟨by simp only [formVecOf, hptr, hln]; exact hf.1, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · have hraw := hok.vec.raw
    simp only [RawVecOk, Buf, hptr, hcp] at hraw ⊢
    exact ⟨hraw.1, hraw.2.imp id fun h' ↦ ⟨h'.1, Nat.le_trans h'.2 hmono⟩⟩
  · rw [hcp, hln]; exact hok.vec.len
  · rw [hptr, hln]; exact hf.2
  · rw [hfb, hds]; exact hok.sep
  · funext x
    simp only [formVecDeep, hds]
    rw [hfb]

/-- A `Vec<Vec<Form>>` at `v` grown by one: `t` holds `s`'s old elements' headers in its buffer, then
`g`'s header, the frame keeps their deep footprints, which miss the buffer. -/
theorem formVecsOf_push {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {v g : Word}
    (hok : FormVecsOk s v) (hg : FormVecOk s g)
    (hlen : (vecLen t v).toNat = (vecLen s v).toNat + 1)
    (hcap : (vecLen s v).toNat + 1 ≤ (vecCap t v).toNat) (hraw : RawVecOk t v 24 8)
    (hcopy : ∀ i < (vecLen s v).toNat, ∀ k < 3,
      t.getMem (vecPtr t v + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 (8 * k)) =
        s.getMem (vecPtr s v + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 (8 * k)))
    (hslot : ∀ k < 3, t.getMem (vecPtr t v + BitVec.ofNat 64 (24 * (vecLen s v).toNat) +
      BitVec.ofNat 64 (8 * k)) = s.getMem (g + BitVec.ofNat 64 (8 * k)))
    (hold : ∀ i < (vecLen s v).toNat, ∀ x,
      formVecDeep s (vecPtr s v + BitVec.ofNat 64 (24 * i)) x → ¬ w x ∧ ¬ formVecsBuf t v x)
    (hnew : ∀ x, formVecDeep s g x → ¬ w x ∧ ¬ formVecsBuf t v x)
    (hheap : HeapOk s) (hmono : heapNext s ≤ heapNext t) :
    formVecsOf t v = formVecsOf s v ++ [formVecOf s g] ∧ FormVecsOk t v ∧
      ∀ x, formVecsDeep t v x → formVecsBuf t v x ∨ formVecsDeep s v x ∨ formVecDeep s g x := by
  have hc (i : Nat) (k : Nat) (hk : k < 3) (hi : i < (vecLen s v).toNat) := hcopy i hi k hk
  have mv (i : Nat) (hi : i < (vecLen s v).toNat) :=
    formVecOf_moved h (by simpa using hc i 0 (by decide) hi)
      (by simpa [BitVec.add_assoc] using hc i 1 (by decide) hi)
      (by simpa [BitVec.add_assoc] using hc i 2 (by decide) hi)
      (hok.elems i hi) (fun x hx ↦ (hold i hi x hx).1) hheap hmono
  have mg := formVecOf_moved h (by simpa using hslot 0 (by decide))
    (by simpa [BitVec.add_assoc] using hslot 1 (by decide))
    (by simpa [BitVec.add_assoc] using hslot 2 (by decide)) hg (fun x hx ↦ (hnew x hx).1)
    hheap hmono
  have hel (i : Nat) (hi : i < (vecLen t v).toNat) :
      (i < (vecLen s v).toNat ∧
        formVecOf t (vecPtr t v + BitVec.ofNat 64 (24 * i)) =
          formVecOf s (vecPtr s v + BitVec.ofNat 64 (24 * i)) ∧
        FormVecOk t (vecPtr t v + BitVec.ofNat 64 (24 * i)) ∧
        formVecDeep t (vecPtr t v + BitVec.ofNat 64 (24 * i)) =
          formVecDeep s (vecPtr s v + BitVec.ofNat 64 (24 * i))) ∨
      (i = (vecLen s v).toNat ∧
        formVecOf t (vecPtr t v + BitVec.ofNat 64 (24 * i)) = formVecOf s g ∧
        FormVecOk t (vecPtr t v + BitVec.ofNat 64 (24 * i)) ∧
        formVecDeep t (vecPtr t v + BitVec.ofNat 64 (24 * i)) = formVecDeep s g) := by
    rw [hlen] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · exact Or.inl ⟨hi, mv i hi⟩
    · subst hi; exact Or.inr ⟨rfl, mg⟩
  refine ⟨?_, ⟨⟨hraw, by omega⟩, fun i hi ↦ ?_, fun i hi x hx ↦ ?_⟩, fun x hx ↦ ?_⟩
  · simp only [formVecsOf, hlen, List.range_succ, List.map_append, List.map_cons, List.map_nil]
    congr 1
    · apply List.map_congr_left
      intro i hi
      exact (mv i (List.mem_range.mp hi)).1
    · exact congrArg (· :: []) mg.1
  · rcases hel i hi with ⟨-, -, hk, -⟩ | ⟨-, -, hk, -⟩ <;> exact hk
  · rcases hel i hi with ⟨hi', -, -, hd⟩ | ⟨-, -, -, hd⟩
    · rw [hd] at hx; exact (hold i hi' x hx).2
    · rw [hd] at hx; exact (hnew x hx).2
  · rcases hx with hx | ⟨i, hi, hx⟩
    · exact Or.inl hx
    · rcases hel i hi with ⟨hi', -, -, hd⟩ | ⟨-, -, -, hd⟩
      · rw [hd] at hx; exact Or.inr (Or.inl (Or.inr ⟨i, hi', hx⟩))
      · rw [hd] at hx; exact Or.inr (Or.inr hx)

end Rv64Verifier.Layout
