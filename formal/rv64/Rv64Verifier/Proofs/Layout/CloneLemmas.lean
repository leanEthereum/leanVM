import Rv64Verifier.Proofs.Layout.ContractsVec

/-!
# Cloning forms

What `Form::clone` leaves, wherever it is inlined (`Vec<Form>::spec_extend`, `<Vec<Form> as
Clone>::clone`): a new buffer of `len` terms holding the source's doublewords (`termsOf_copy`), and a
header `(len, buffer, len)`, so the same form (`clone_form`). And the element count
`Vec::spec_extend` computes from a slice's bounds, `(end - begin) >> 3` times the inverse of `3`
(`count_eq`).
-/

namespace Rv64Verifier.Layout
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Model.LayoutMirror

theorem add_ofNat_add (p : Word) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Terms whose doublewords were copied are the same terms. -/
theorem termsOf_copy {s t : MachineState} {p q : Word} {n : Nat}
    (h : ∀ k, k % 8 = 0 → k + 8 ≤ 48 * n →
      t.getMem (p + BitVec.ofNat 64 k) = s.getMem (q + BitVec.ofNat 64 k)) :
    termsOf t p n = termsOf s q n ∧
      ∀ i < n, MonoOk s (q + BitVec.ofNat 64 (48 * i)) → MonoOk t (p + BitVec.ofNat 64 (48 * i)) := by
  have g (i : Nat) (hi : i < n) (j : Nat) (hj : j < 6) :
      t.getMem (p + BitVec.ofNat 64 (48 * i) + BitVec.ofNat 64 (8 * j)) =
        s.getMem (q + BitVec.ofNat 64 (48 * i) + BitVec.ofNat 64 (8 * j)) := by
    rw [add_ofNat_add, add_ofNat_add]
    exact h _ (by omega) (by omega)
  have g0 (i : Nat) (hi : i < n) : t.getMem (p + BitVec.ofNat 64 (48 * i)) =
      s.getMem (q + BitVec.ofNat 64 (48 * i)) := by
    simpa using g i hi 0 (by decide)
  refine ⟨List.map_congr_left fun i hm ↦ ?_, fun i hi hm ↦ ?_⟩
  · have hi := List.mem_range.mp hm
    simp only [termOf, Prod.mk.injEq]
    refine ⟨monoOf_congr (g0 i hi) (g i hi 1 (by decide)) (g i hi 2 (by decide)), ?_⟩
    apply eAt_congr <;> simp only [BitVec.add_assoc]
    · exact (by simpa [BitVec.add_assoc] using g i hi 3 (by decide))
    · exact (by simpa [BitVec.add_assoc, ← BitVec.ofNat_add] using g i hi 4 (by decide))
    · exact (by simpa [BitVec.add_assoc, ← BitVec.ofNat_add] using g i hi 5 (by decide))
  · simp only [MonoOk, g0 i hi]; exact hm

/-- A header `(len, p, len)` at `e` over a fresh buffer holding the doublewords of the form at `src`
is that form, sound, its buffer fresh. -/
theorem clone_form {u t : MachineState} {src e p : Word} (hok : FormOk u src) (hheap : HeapOk u)
    (hcap : t.getMem e = vecLen u src) (hptr : t.getMem (e + 8) = p)
    (hlen : t.getMem (e + 16) = vecLen u src)
    (hnew : NewBuf u t p ((vecLen u src).toNat * 48) 8)
    (hcopy : ∀ k, k % 8 = 0 → k + 8 ≤ 48 * (vecLen u src).toNat →
      t.getMem (p + BitVec.ofNat 64 k) = u.getMem (vecPtr u src + BitVec.ofNat 64 k)) :
    formOf t e = formOf u src ∧ FormOk t e ∧ ∀ x, formBuf t e x → Fresh u t x := by
  have hc := termsOf_copy hcopy
  have hlo := hheap.lo
  refine ⟨?_, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simp only [formOf, vecPtr, vecLen, hptr, hlen]
    exact congrArg FormRust.mk hc.1
  · simp only [RawVecOk, Buf, vecPtr, vecCap, hptr, hcap]
    simp only [NewBuf] at hnew
    refine ⟨hnew.1, ?_⟩
    rcases hnew.2 with h0 | h0
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, by omega⟩
  · simp only [vecCap, vecLen, hcap, hlen]; exact Nat.le_refl _
  · intro i hi
    simp only [vecLen, hlen] at hi
    simp only [vecPtr, hptr]
    exact hc.2 i hi (hok.tags i hi)
  · intro x hx
    simp only [formBuf, vecPtr, vecCap, hptr, hcap, Within] at hx
    simp only [NewBuf] at hnew
    simp only [Fresh]
    rcases hnew.2 with h0 | h0 <;> omega

/-- A form whose header was copied from `e'` to `e`, its buffer untouched, is the same form. -/
theorem formOf_move {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {e e' : Word}
    (hok : FormOk s e') (h0 : t.getMem e = s.getMem e') (h8 : t.getMem (e + 8) = s.getMem (e' + 8))
    (h16 : t.getMem (e + 16) = s.getMem (e' + 16)) (hb : ∀ x, formBuf s e' x → ¬ w x)
    (hheap : HeapOk s) (hmono : heapNext s ≤ heapNext t) :
    formOf t e = formOf s e' ∧ FormOk t e ∧ formBuf t e = formBuf s e' := by
  have hraw := hok.vec.raw
  have hlen := hok.vec.len
  have hhi := hheap.hi
  simp only [RawVecOk, Buf, vecCap, vecPtr, vecLen, heapNext] at hraw hlen hhi
  have hterm (i : Nat) (hi : i < (s.getMem (e' + 16)).toNat) :=
    termOf_frame h (a := s.getMem (e' + 8) + BitVec.ofNat 64 (48 * i))
      (fun x hx ↦ hb x (by
        simp only [formBuf, vecPtr, vecCap]
        rcases hraw.2 with h0 | h0
        · exfalso; rw [Nat.mul_eq_zero] at h0; omega
        · addr_omega [hx, h0, hi, hlen, hhi]))
      (by
        rcases hraw.2 with h0 | h0
        · exfalso; rw [Nat.mul_eq_zero] at h0; omega
        · addr_omega [h0, hi, hlen, hhi])
  refine ⟨?_, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · simp only [formOf, vecPtr, vecLen, h8, h16, termsOf, FormRust.mk.injEq]
    apply List.map_congr_left
    intro i hi
    exact (hterm i (List.mem_range.mp hi)).1
  · simp only [RawVecOk, Buf, vecCap, vecPtr, heapNext, h0, h8]
    simp only [heapNext] at hmono
    omega
  · simp only [vecCap, vecLen, h0, h16]
    exact hlen
  · intro i hi
    simp only [vecLen, h16] at hi
    simp only [vecPtr, h8]
    exact (hterm i hi).2 (hok.tags i (by simpa [vecLen] using hi))
  · funext x
    simp only [formBuf, vecPtr, vecCap, h0, h8]

/-- A `Vec<Form>` whose header was copied from `a'` to `a`, its deep footprint untouched, is the same
`Vec`. -/
theorem formVecOf_move {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {a a' : Word}
    (hok : FormVecOk s a') (h0 : t.getMem a = s.getMem a') (h8 : t.getMem (a + 8) = s.getMem (a' + 8))
    (h16 : t.getMem (a + 16) = s.getMem (a' + 16)) (hd : ∀ x, formVecDeep s a' x → ¬ w x)
    (hheap : HeapOk s) (hmono : heapNext s ≤ heapNext t) :
    formVecOf t a = formVecOf s a' ∧ FormVecOk t a ∧ formVecDeep t a = formVecDeep s a' := by
  have hb := vecBuf_bounds hok.vec (by decide)
  have hlen := hok.vec.len
  have hhi := hheap.hi
  simp only [vecCap, vecPtr, vecLen, heapNext, heapStart, heapEnd] at hb hlen hhi
  have hhw : (vecPtr s a').toNat + 24 * (vecLen s a').toNat ≤ 2 ^ 64 := by
    simp only [vecPtr, vecLen]
    have := (s.getMem nextAddr).isLt
    have := (s.getMem (a' + 8)).isLt
    rcases hb.2 with h0 | h0 <;> omega
  have hhd : ∀ x, Within x (vecPtr s a') (24 * (vecLen s a').toNat) → ¬ w x := fun x hx ↦
    hd x (Or.inl (by
      simp only [formVecBuf, vecPtr, vecCap, vecLen] at hx ⊢
      rcases hb.2 with h0 | h0
      · exfalso; simp only [Within] at hx; omega
      · addr_omega [hx, hlen, h0]))
  have hf := formsAt_frame h hok.forms hhd (fun x hx ↦ hd x (Or.inr hx)) hhw hheap hmono
  have hptr : vecPtr t a = vecPtr s a' := h8
  have hln : vecLen t a = vecLen s a' := h16
  have hcp : vecCap t a = vecCap s a' := h0
  have hfb : formVecBuf t a = formVecBuf s a' := by
    funext x; simp only [formVecBuf, hptr, hcp]
  have hfd : formsDeep t (vecPtr t a) (vecLen t a).toNat = formsDeep s (vecPtr s a') (vecLen s a').toNat := by
    rw [hptr, hln, formsDeep_frame h hhd hhw]
  refine ⟨by simp only [formVecOf, hptr, hln]; exact hf.1, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · have hraw := hok.vec.raw
    simp only [RawVecOk, Buf, hptr, hcp] at hraw ⊢
    exact ⟨hraw.1, hraw.2.imp id fun h' ↦ ⟨h'.1, Nat.le_trans h'.2 hmono⟩⟩
  · rw [hcp, hln]; exact hok.vec.len
  · rw [hptr, hln]; exact hf.2
  · rw [hfb, hfd]; exact hok.sep
  · funext x
    simp only [formVecDeep]
    rw [hfb, hfd]

/-- A sound form's buffer lies in the heap below `NEXT`. -/
theorem formBuf_below {s : MachineState} {e x : Word} (hok : FormOk s e) (hx : formBuf s e x) :
    heapStart ≤ x.toNat ∧ x.toNat < heapNext s := by
  have hraw := hok.vec.raw
  simp only [RawVecOk, Buf] at hraw
  simp only [formBuf, Within] at hx
  rcases hraw.2 with h0 | h0
  · rw [Nat.mul_eq_zero] at h0; omega
  · omega

/-- A sound `Vec`'s buffer lies in the heap below `NEXT`. -/
theorem vecBuf_below {s : MachineState} {a x : Word} {size : Nat} (hv : VecOk s a size 8)
    (hx : Within x (vecPtr s a) (size * (vecCap s a).toNat)) :
    heapStart ≤ x.toNat ∧ x.toNat < heapNext s := by
  have hraw := hv.raw
  simp only [RawVecOk, Buf] at hraw
  simp only [Within] at hx
  rcases hraw.2 with h0 | h0
  · rw [Nat.mul_eq_zero] at h0; rcases h0 with h0 | h0 <;> simp_all <;> omega
  · rw [Nat.mul_comm] at h0; omega

/-- `((end - begin) >> 3) * 0xaaaaaaaaaaaaaaab`, the length of a slice of 24-byte elements. -/
theorem count_eq (d : Word) (h : d.toNat % 24 = 0) :
    ((d >>> 3) * (0xaaaaaaaaaaaaaaab : Word)).toNat = d.toNat / 24 := by
  have hd := d.isLt
  rw [BitVec.toNat_mul, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have e : (0xaaaaaaaaaaaaaaab : Word).toNat = 0xaaaaaaaaaaaaaaab := rfl
  rw [e]
  have h3 : d.toNat / 2 ^ 3 = 3 * (d.toNat / 24) := by omega
  have e3 : 3 * (d.toNat / 24) * 0xaaaaaaaaaaaaaaab = d.toNat / 24 + 2 * (d.toNat / 24) * 2 ^ 64 := by
    ring
  rw [h3, e3, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

end Rv64Verifier.Layout
