import Rv64Verifier.Proofs.Layout.Repr

/-!
# `Vec<Form>`, `Vec<Vec<Form>>` and `Flushes` in memory

A `Form` is a 24-byte `Vec` header (`Repr.lean`), so `n` of them from `p` (a slice, an array, a
`Vec`'s buffer) are 24 bytes apart (`formsAt`); a `Vec<Form>` is a header whose buffer holds them
(`formVecOf`), a `Vec<Vec<Form>>` a header whose buffer holds `Vec<Form>` headers
(`formVecsOf`), and `Flushes` the two of those for `push` and `pull`, at `+0` and `+24`
(`flushesOf`, read off `Flushes::pair`).

A value's bytes are its header's and its deep footprint's (`*Deep`): the buffers it reaches, each at
its capacity. Its `Ok` says every buffer is allocated, every tag valid, and a `Vec`'s buffer apart
from its elements' deep footprints, so that pushing into the buffer's spare room keeps the elements.
A frame that writes none of a value's bytes keeps it (`formsAt_frame`, `formVecOf_frame`, ..).
-/

namespace Rv64Verifier.Layout
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Model.LayoutMirror

/-! ## Arrays of forms -/

/-- The `n` `Form`s from `p`. -/
def formsAt (s : MachineState) (p : Word) (n : Nat) : List FormRust :=
  (List.range n).map fun i ↦ formOf s (p + BitVec.ofNat 64 (24 * i))

/-- The buffers of the `n` `Form`s from `p`. -/
@[rv_addr] def formsDeep (s : MachineState) (p : Word) (n : Nat) (x : Word) : Prop :=
  ∃ i < n, formBuf s (p + BitVec.ofNat 64 (24 * i)) x

/-- Every one of the `n` `Form`s from `p` is sound. -/
def FormsOk (s : MachineState) (p : Word) (n : Nat) : Prop :=
  ∀ i < n, FormOk s (p + BitVec.ofNat 64 (24 * i))

/-- A header the frame misses keeps its buffer. -/
theorem formBuf_frame {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {e : Word}
    (hh : ∀ x, Within x e 24 → ¬ w x) (hw : e.toNat + 24 ≤ 2 ^ 64) : formBuf t e = formBuf s e := by
  have hc : t.getMem e = s.getMem e := h.getMem_of (fun x hx ↦ hh x (by addr_omega [hx, hw]))
    (by addr_omega [hw])
  have hp : t.getMem (e + 8) = s.getMem (e + 8) :=
    h.getMem_of (fun x hx ↦ hh x (by addr_omega [hx, hw])) (by addr_omega [hw])
  funext x
  simp only [formBuf, vecPtr, vecCap, hc, hp]

/-- Headers the frame misses keep their buffers. -/
theorem formsDeep_frame {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {p : Word}
    {n : Nat} (hh : ∀ x, Within x p (24 * n) → ¬ w x) (hw : p.toNat + 24 * n ≤ 2 ^ 64) :
    formsDeep t p n = formsDeep s p n := by
  funext x
  apply propext
  simp only [formsDeep]
  constructor <;> rintro ⟨i, hi, hx⟩ <;> refine ⟨i, hi, ?_⟩
  · rwa [formBuf_frame h (fun y hy ↦ hh y (by addr_omega [hy, hi, hw])) (by addr_omega [hi, hw])] at hx
  · rwa [formBuf_frame h (fun y hy ↦ hh y (by addr_omega [hy, hi, hw])) (by addr_omega [hi, hw])]

theorem formsAt_length (s : MachineState) (p : Word) (n : Nat) : (formsAt s p n).length = n := by
  simp [formsAt]

/-- The forms from `p` are unchanged, and still sound, across a frame that writes neither their
headers nor their buffers. -/
theorem formsAt_frame {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {p : Word}
    {n : Nat} (hok : FormsOk s p n) (hh : ∀ x, Within x p (24 * n) → ¬ w x)
    (hd : ∀ x, formsDeep s p n x → ¬ w x) (hw : p.toNat + 24 * n ≤ 2 ^ 64) (hheap : HeapOk s)
    (hmono : heapNext s ≤ heapNext t) :
    formsAt t p n = formsAt s p n ∧ FormsOk t p n := by
  have hi (i : Nat) (hi : i < n) := formOf_frame h (hok i hi)
    (fun x hx ↦ hh x (by addr_omega [hx, hi, hw])) (fun x hx ↦ hd x ⟨i, hi, hx⟩)
    (by addr_omega [hi, hw]) hheap hmono
  refine ⟨List.map_congr_left fun i hm ↦ (hi i (List.mem_range.mp hm)).1, fun i h' ↦ (hi i h').2⟩

/-! ## `Vec<Form>` -/

/-- The `Vec<Form>` at `a`. -/
def formVecOf (s : MachineState) (a : Word) : List FormRust :=
  formsAt s (vecPtr s a) (vecLen s a).toNat

/-- Its buffer, at its capacity. -/
@[rv_addr] def formVecBuf (s : MachineState) (a : Word) (x : Word) : Prop :=
  Within x (vecPtr s a) (24 * (vecCap s a).toNat)

/-- Its buffer and its forms' buffers. -/
@[rv_addr] def formVecDeep (s : MachineState) (a : Word) (x : Word) : Prop :=
  formVecBuf s a x ∨ formsDeep s (vecPtr s a) (vecLen s a).toNat x

/-- An allocated `Vec` of sound forms whose buffers miss its own. -/
structure FormVecOk (s : MachineState) (a : Word) : Prop where
  vec : VecOk s a 24 8
  forms : FormsOk s (vecPtr s a) (vecLen s a).toNat
  sep : ∀ x, formsDeep s (vecPtr s a) (vecLen s a).toNat x → ¬ formVecBuf s a x

/-- A `Vec`'s buffer: aligned, and empty or in the heap below `NEXT`. -/
theorem vecBuf_bounds {s : MachineState} {a : Word} {size : Nat} (hv : VecOk s a size 8)
    (hsz : 0 < size) :
    (vecPtr s a).toNat % 8 = 0 ∧ ((vecCap s a).toNat = 0 ∨
      (heapStart ≤ (vecPtr s a).toNat ∧ (vecPtr s a).toNat + (vecCap s a).toNat * size ≤ heapNext s)) := by
  have hraw := hv.raw
  simp only [RawVecOk, Buf] at hraw
  refine ⟨hraw.1, ?_⟩
  rcases hraw.2 with h | h
  · exact Or.inl (by rcases Nat.mul_eq_zero.mp h with h | h <;> omega)
  · exact Or.inr h

/-- The `Vec<Form>` at `a` is unchanged, and still sound, across a frame that writes neither its
header nor its deep footprint. -/
theorem formVecOf_frame {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {a : Word}
    (hok : FormVecOk s a) (hh : ∀ x, Within x a 24 → ¬ w x) (hd : ∀ x, formVecDeep s a x → ¬ w x)
    (haw : a.toNat + 24 ≤ 2 ^ 64) (hheap : HeapOk s) (hmono : heapNext s ≤ heapNext t) :
    formVecOf t a = formVecOf s a ∧ FormVecOk t a := by
  have hc : t.getMem a = s.getMem a := h.getMem_of (fun x hx ↦ hh x (by addr_omega [hx, haw]))
    (by addr_omega [haw])
  have hp : t.getMem (a + 8) = s.getMem (a + 8) :=
    h.getMem_of (fun x hx ↦ hh x (by addr_omega [hx, haw])) (by addr_omega [haw])
  have hl : t.getMem (a + 16) = s.getMem (a + 16) :=
    h.getMem_of (fun x hx ↦ hh x (by addr_omega [hx, haw])) (by addr_omega [haw])
  have hb := vecBuf_bounds hok.vec (by decide)
  have hlen := hok.vec.len
  have hhi := hheap.hi
  simp only [vecCap, vecPtr, vecLen, heapNext, heapStart, heapEnd] at hb hlen hhi
  have hhw : (vecPtr s a).toNat + 24 * (vecLen s a).toNat ≤ 2 ^ 64 := by
    simp only [vecPtr, vecLen]
    have := (s.getMem nextAddr).isLt
    have := (s.getMem (a + 8)).isLt
    rcases hb.2 with h0 | h0 <;> omega
  have hf := formsAt_frame h hok.forms
    (fun x hx ↦ hd x (Or.inl (by
      simp only [formVecBuf, vecPtr, vecCap, vecLen] at hx ⊢
      rcases hb.2 with h0 | h0
      · exfalso; simp only [Within] at hx; omega
      · addr_omega [hx, hlen, h0])))
    (fun x hx ↦ hd x (Or.inr hx)) hhw hheap hmono
  have hptr : vecPtr t a = vecPtr s a := hp
  have hln : vecLen t a = vecLen s a := hl
  have hcp : vecCap t a = vecCap s a := hc
  refine ⟨by simp only [formVecOf, hptr, hln]; exact hf.1, ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
  · have hraw := hok.vec.raw
    simp only [RawVecOk, Buf, hptr, hcp] at hraw ⊢
    exact ⟨hraw.1, hraw.2.imp id fun h' ↦ ⟨h'.1, Nat.le_trans h'.2 hmono⟩⟩
  · rw [hcp, hln]; exact hok.vec.len
  · rw [hptr, hln]; exact hf.2
  · have hfb : formVecBuf t a = formVecBuf s a := by
      funext x; simp only [formVecBuf, hptr, hcp]
    have hhd : ∀ x, Within x (vecPtr s a) (24 * (vecLen s a).toNat) → ¬ w x := fun x hx ↦
      hd x (Or.inl (by
        simp only [formVecBuf, vecPtr, vecCap, vecLen] at hx ⊢
        rcases hb.2 with h0 | h0
        · exfalso; simp only [Within] at hx; omega
        · addr_omega [hx, hlen, h0]))
    rw [hfb, hptr, hln, formsDeep_frame h hhd hhw]
    exact hok.sep

/-! ## `Vec<Vec<Form>>` -/

/-- The `Vec<Vec<Form>>` at `a`. -/
def formVecsOf (s : MachineState) (a : Word) : List (List FormRust) :=
  (List.range (vecLen s a).toNat).map fun i ↦ formVecOf s (vecPtr s a + BitVec.ofNat 64 (24 * i))

/-- Its buffer, at its capacity. -/
@[rv_addr] def formVecsBuf (s : MachineState) (a : Word) (x : Word) : Prop :=
  Within x (vecPtr s a) (24 * (vecCap s a).toNat)

/-- Its buffer and its elements' deep footprints. -/
@[rv_addr] def formVecsDeep (s : MachineState) (a : Word) (x : Word) : Prop :=
  formVecsBuf s a x ∨
    ∃ i < (vecLen s a).toNat, formVecDeep s (vecPtr s a + BitVec.ofNat 64 (24 * i)) x

/-- An allocated `Vec` of sound `Vec<Form>`s whose deep footprints miss its buffer. -/
structure FormVecsOk (s : MachineState) (a : Word) : Prop where
  vec : VecOk s a 24 8
  elems : ∀ i < (vecLen s a).toNat, FormVecOk s (vecPtr s a + BitVec.ofNat 64 (24 * i))
  sep : ∀ i < (vecLen s a).toNat, ∀ x,
    formVecDeep s (vecPtr s a + BitVec.ofNat 64 (24 * i)) x → ¬ formVecsBuf s a x

/-! ## `Flushes` -/

/-- The `Flushes` at `a`: `push` at `+0`, `pull` at `+24`. -/
def flushesOf (s : MachineState) (a : Word) : FlushesRust :=
  ⟨formVecsOf s a, formVecsOf s (a + 24)⟩

/-- Its two buffers, at their capacities. -/
@[rv_addr] def flushesBuf (s : MachineState) (a : Word) (x : Word) : Prop :=
  formVecsBuf s a x ∨ formVecsBuf s (a + 24) x

/-- Its deep footprint. -/
@[rv_addr] def flushesDeep (s : MachineState) (a : Word) (x : Word) : Prop :=
  formVecsDeep s a x ∨ formVecsDeep s (a + 24) x

/-- Both sides sound, each side's buffer missing the other's deep footprint, and the header missing
both. -/
structure FlushesOk (s : MachineState) (a : Word) : Prop where
  push : FormVecsOk s a
  pull : FormVecsOk s (a + 24)
  pushPull : ∀ x, formVecsBuf s a x → ¬ formVecsDeep s (a + 24) x
  pullPush : ∀ x, formVecsBuf s (a + 24) x → ¬ formVecsDeep s a x
  header : ∀ x, Within x a 48 → ¬ flushesDeep s a x

end Rv64Verifier.Layout
