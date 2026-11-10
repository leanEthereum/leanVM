import Rv64Verifier.Proofs.Layout.CloneLemmas
import Rv64Verifier.Proofs.Layout.AddScaled
import Rv64Verifier.Proofs.Layout.VecLemmas

/-!
# What a callee's scratch writes keep

A builder calls functions that write its stack, `NEXT` and the heap they allocate (`Scratch`)
besides their outputs. Everything allocated before lies below the old `NEXT`, so such writes keep
every sound value outside the stack: a `Vec<Vec<Form>>` (`formVecsOf_frame`), a `Flushes`
(`flushesOf_frame`, `flushesOf_keep`), a `Form` (`formOf_keep`), and `.rodata` (`RodataOk.dframe`).
-/

namespace Rv64Verifier.Layout
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Model.LayoutMirror

/-- The `Vec<Vec<Form>>` at `a` is unchanged, and still sound, across a frame that writes neither its
header nor its deep footprint. -/
theorem formVecsOf_frame {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {a : Word}
    (hok : FormVecsOk s a) (hh : ∀ x, Within x a 24 → ¬ w x)
    (hd : ∀ x, formVecsDeep s a x → ¬ w x) (haw : a.toNat + 24 ≤ 2 ^ 64) (hheap : HeapOk s)
    (hmono : heapNext s ≤ heapNext t) :
    formVecsOf t a = formVecsOf s a ∧ FormVecsOk t a ∧ formVecsDeep t a = formVecsDeep s a ∧
      formVecsBuf t a = formVecsBuf s a := by
  have g (k : Nat) (hk : k + 8 ≤ 24) :
      t.getMem (a + BitVec.ofNat 64 k) = s.getMem (a + BitVec.ofNat 64 k) :=
    h.getMem_of (fun x hx ↦ hh x (by addr_omega [hx, hk, haw])) (by addr_omega [hk, haw])
  have hcp : vecCap t a = vecCap s a := by simpa [vecCap] using g 0 (by decide)
  have hptr : vecPtr t a = vecPtr s a := g 8 (by decide)
  have hln : vecLen t a = vecLen s a := g 16 (by decide)
  have hb := vecBuf_bounds hok.vec (by decide)
  have hlen := hok.vec.len
  have hhi := hheap.hi
  have hslot (i : Nat) (hi : i < (vecLen s a).toNat) (k : Nat) (hk : k + 8 ≤ 24) :
      t.getMem (vecPtr s a + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 k) =
        s.getMem (vecPtr s a + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 k) := by
    rcases hb.2 with h0 | h0
    · omega
    · exact h.getMem_of (fun x hx ↦ hd x (Or.inl (by
        simp only [formVecsBuf]; addr_omega [hx, h0, hi, hlen, hk, hhi])))
        (by addr_omega [h0, hi, hlen, hk, hhi])
  have hel (i : Nat) (hi : i < (vecLen s a).toNat) :=
    formVecOf_moved h (e := vecPtr s a + BitVec.ofNat 64 (24 * i))
      (e' := vecPtr s a + BitVec.ofNat 64 (24 * i))
      (by simpa using hslot i hi 0 (by decide)) (hslot i hi 8 (by decide))
      (hslot i hi 16 (by decide)) (hok.elems i hi) (fun x hx ↦ hd x (Or.inr ⟨i, hi, hx⟩))
      hheap hmono
  have hbuf : formVecsBuf t a = formVecsBuf s a := by
    funext x; simp only [formVecsBuf, hptr, hcp]
  refine ⟨?_, ⟨⟨?_, ?_⟩, fun i hi ↦ ?_, fun i hi x hx ↦ ?_⟩, ?_, hbuf⟩
  · simp only [formVecsOf, hptr, hln]
    exact List.map_congr_left fun i hm ↦ (hel i (List.mem_range.mp hm)).1
  · have hraw := hok.vec.raw
    simp only [RawVecOk, Buf, hptr, hcp] at hraw ⊢
    exact ⟨hraw.1, hraw.2.imp id fun h' ↦ ⟨h'.1, Nat.le_trans h'.2 hmono⟩⟩
  · rw [hcp, hln]; exact hlen
  · rw [hln] at hi; rw [hptr]; exact (hel i hi).2.1
  · rw [hln] at hi; rw [hptr, (hel i hi).2.2] at hx; rw [hbuf]; exact hok.sep i hi x hx
  · funext x
    apply propext
    simp only [formVecsDeep, hbuf, hptr, hln]
    refine or_congr Iff.rfl (exists_congr fun i ↦ ⟨fun ⟨hi, hx⟩ ↦ ⟨hi, ?_⟩, fun ⟨hi, hx⟩ ↦ ⟨hi, ?_⟩⟩)
    · rwa [(hel i hi).2.2] at hx
    · rwa [(hel i hi).2.2]

/-- The `Flushes` at `a` is unchanged, and still sound, across a frame that writes neither its header
nor its deep footprint. -/
theorem flushesOf_frame {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {a : Word}
    (hok : FlushesOk s a) (hh : ∀ x, Within x a 48 → ¬ w x)
    (hd : ∀ x, flushesDeep s a x → ¬ w x) (haw : a.toNat + 48 ≤ 2 ^ 64) (hheap : HeapOk s)
    (hmono : heapNext s ≤ heapNext t) :
    flushesOf t a = flushesOf s a ∧ FlushesOk t a ∧ flushesDeep t a = flushesDeep s a ∧
      flushesBuf t a = flushesBuf s a := by
  have h1 := formVecsOf_frame h hok.push (fun x hx ↦ hh x (by addr_omega [hx, haw]))
    (fun x hx ↦ hd x (Or.inl hx)) (by addr_omega [haw]) hheap hmono
  have h2 := formVecsOf_frame h hok.pull (fun x hx ↦ hh x (by addr_omega [hx, haw]))
    (fun x hx ↦ hd x (Or.inr hx)) (by addr_omega [haw]) hheap hmono
  have hdeep : flushesDeep t a = flushesDeep s a := by
    funext x; simp only [flushesDeep, h1.2.2.1, h2.2.2.1]
  have hbuf : flushesBuf t a = flushesBuf s a := by
    funext x; simp only [flushesBuf, h1.2.2.2, h2.2.2.2]
  refine ⟨by simp only [flushesOf, h1.1, h2.1], ⟨h1.2.1, h2.2.1, ?_, ?_, ?_⟩, hdeep, hbuf⟩
  · rw [h1.2.2.2, h2.2.2.1]; exact hok.pushPull
  · rw [h2.2.2.2, h1.2.2.1]; exact hok.pullPush
  · rw [hdeep]; exact hok.header

/-- Everything a sound `Vec<Vec<Form>>` reaches is in the heap below `NEXT`. -/
theorem FormVecsOk.deep_below {s : MachineState} {a x : Word} (h : FormVecsOk s a)
    (hx : formVecsDeep s a x) : heapStart ≤ x.toNat ∧ x.toNat < heapNext s := by
  rcases hx with hx | ⟨i, hi, hx⟩
  · have hraw := h.vec.raw
    simp only [RawVecOk, Buf] at hraw
    simp only [formVecsBuf, Within] at hx
    rcases hraw.2 with h0 | h0 <;> omega
  · exact (h.elems i hi).deep_below hx

/-- Everything a sound `Flushes` reaches is in the heap below `NEXT`. -/
theorem FlushesOk.deep_below {s : MachineState} {a x : Word} (h : FlushesOk s a)
    (hx : flushesDeep s a x) : heapStart ≤ x.toNat ∧ x.toNat < heapNext s := by
  rcases hx with hx | hx
  · exact h.push.deep_below hx
  · exact h.pull.deep_below hx

theorem FlushesOk.buf_below {s : MachineState} {a x : Word} (h : FlushesOk s a)
    (hx : flushesBuf s a x) : heapStart ≤ x.toNat ∧ x.toNat < heapNext s :=
  h.deep_below (hx.imp Or.inl Or.inl)

/-! ## Scratch writes -/

/-- What a callee writes besides its outputs, from `s` to `t`: the stack from `lo`, `NEXT`, and what it
allocates. -/
@[rv_addr] def Scratch (s t : MachineState) (lo : Word) (n : Nat) (x : Word) : Prop :=
  Within x lo n ∨ Within x nextAddr 8 ∨ Fresh s t x

/-- Scratch writes in sequence. -/
theorem DFrame.scratch_trans {s t u : MachineState} {lo : Word} {n : Nat}
    (h₁ : DFrame s t (Scratch s t lo n)) (h₂ : DFrame t u (Scratch t u lo n))
    (hm₁ : heapNext s ≤ heapNext t) (hm₂ : heapNext t ≤ heapNext u) :
    DFrame s u (Scratch s u lo n) :=
  (h₁.union h₂).mono fun x hx ↦ by
    simp only [Scratch, Fresh] at hx ⊢
    rcases hx with (h | h | h) | (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h.1, by omega⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨by omega, h.2⟩)

/-- Below the old `NEXT`, in the heap: no scratch write. -/
theorem not_scratch {s t : MachineState} {lo : Word} {n : Nat} {x : Word}
    (hlo : heapEnd ≤ lo.toNat) (hs : heapNext s ≤ heapEnd) (hx : x.toNat < heapNext s) :
    ¬ Scratch s t lo n x := by
  simp only [Scratch, Fresh]
  rintro (h | h | h) <;> addr_omega [h, hlo, hs, hx]

/-- A `Flushes` outside the stack and the free heap is kept by scratch writes. -/
theorem flushesOf_keep {s t : MachineState} {lo : Word} {n : Nat} {a : Word}
    (h : DFrame s t (Scratch s t lo n)) (hok : FlushesOk s a) (hheap : HeapOk s)
    (hmono : heapNext s ≤ heapNext t) (hht : heapNext t ≤ heapEnd) (hlo : heapEnd ≤ lo.toNat)
    (hf : Outside s a 48) (hs : Apart a 48 lo n) (haw : a.toNat + 48 ≤ 2 ^ 64) :
    flushesOf t a = flushesOf s a ∧ FlushesOk t a ∧ flushesDeep t a = flushesDeep s a ∧
      flushesBuf t a = flushesBuf s a :=
  flushesOf_frame h hok
    (fun x hx hw ↦ by simp only [Scratch, Fresh] at hw; rcases hw with hw | hw | hw <;>
      addr_omega [hx, hw, hf, hs, hht])
    (fun x hx ↦ not_scratch hlo hheap.hi (hok.deep_below hx).2) haw hheap hmono

/-- A `Form` outside the stack and the free heap is kept by scratch writes. -/
theorem formOf_keep {s t : MachineState} {lo : Word} {n : Nat} {e : Word}
    (h : DFrame s t (Scratch s t lo n)) (hok : FormOk s e) (hheap : HeapOk s)
    (hmono : heapNext s ≤ heapNext t) (hht : heapNext t ≤ heapEnd) (hlo : heapEnd ≤ lo.toNat)
    (hf : Outside s e 24) (hs : Apart e 24 lo n) (haw : e.toNat + 24 ≤ 2 ^ 64) :
    formOf t e = formOf s e ∧ FormOk t e ∧ formBuf t e = formBuf s e :=
  formOf_move h hok
    (h.getMem_of (fun x hx hw ↦ by simp only [Scratch, Fresh] at hw; rcases hw with hw | hw | hw <;>
      addr_omega [hx, hw, hf, hs, hht, haw]) (by addr_omega [haw]))
    (h.getMem_of (fun x hx hw ↦ by simp only [Scratch, Fresh] at hw; rcases hw with hw | hw | hw <;>
      addr_omega [hx, hw, hf, hs, hht, haw]) (by addr_omega [haw]))
    (h.getMem_of (fun x hx hw ↦ by simp only [Scratch, Fresh] at hw; rcases hw with hw | hw | hw <;>
      addr_omega [hx, hw, hf, hs, hht, haw]) (by addr_omega [haw]))
    (fun x hx ↦ not_scratch hlo hheap.hi (hok.buf_below hx).2) hheap hmono

/-- `.rodata` is kept by a frame that misses it. -/
theorem RodataOk.dframe {s t : MachineState} {w : Word → Prop} (h : RodataOk s) (hf : DFrame s t w)
    (hw : ∀ x, w x → ¬ Within x rodataBase rodataSize) : RodataOk t := by
  intro p hp
  obtain ⟨h8, hlo, hhi⟩ := AddScaled.rodataWords_aligned p hp
  rw [hf.getMem_of (fun x hx hx' ↦ hw x hx' (by addr_omega [hx, hlo, hhi])) (by omega)]
  exact h p hp

/-- Scratch writes miss `.rodata`. -/
theorem not_rodata_of_scratch {s t : MachineState} {lo : Word} {n : Nat} {x : Word}
    (hlo : Apart lo n rodataStart rodataSize) (ht : heapNext t ≤ heapEnd) (hx : Scratch s t lo n x) :
    ¬ Within x rodataBase rodataSize := by
  simp only [Scratch, Fresh] at hx
  rcases hx with hx | hx | hx <;> intro h <;> addr_omega [hx, h, hlo, ht]

/-- `formVecOf_frame`, with the deep footprint kept. -/
theorem formVecOf_frame' {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {a : Word}
    (hok : FormVecOk s a) (hh : ∀ x, Within x a 24 → ¬ w x) (hd : ∀ x, formVecDeep s a x → ¬ w x)
    (haw : a.toNat + 24 ≤ 2 ^ 64) (hheap : HeapOk s) (hmono : heapNext s ≤ heapNext t) :
    formVecOf t a = formVecOf s a ∧ FormVecOk t a ∧ formVecDeep t a = formVecDeep s a := by
  have g (k : Nat) (hk : k + 8 ≤ 24) :
      t.getMem (a + BitVec.ofNat 64 k) = s.getMem (a + BitVec.ofNat 64 k) :=
    h.getMem_of (fun x hx ↦ hh x (by addr_omega [hx, hk, haw])) (by addr_omega [hk, haw])
  exact formVecOf_moved h (by simpa using g 0 (by decide)) (g 8 (by decide)) (g 16 (by decide))
    hok hd hheap hmono

/-- Forms outside the stack and the free heap are kept by scratch writes. -/
theorem formsAt_keep {s t : MachineState} {lo : Word} {n : Nat} {p : Word} {k : Nat}
    (h : DFrame s t (Scratch s t lo n)) (hok : FormsOk s p k) (hheap : HeapOk s)
    (hmono : heapNext s ≤ heapNext t) (hht : heapNext t ≤ heapEnd) (hlo : heapEnd ≤ lo.toNat)
    (hf : Outside s p (24 * k)) (hs : Apart p (24 * k) lo n) (hpw : p.toNat + 24 * k ≤ 2 ^ 64) :
    formsAt t p k = formsAt s p k ∧ FormsOk t p k ∧ formsDeep t p k = formsDeep s p k := by
  have hh : ∀ x, Within x p (24 * k) → ¬ Scratch s t lo n x := fun x hx hw ↦ by
    simp only [Scratch, Fresh] at hw
    rcases hw with hw | hw | hw <;> addr_omega [hx, hw, hf, hs, hht]
  have hd : ∀ x, formsDeep s p k x → ¬ Scratch s t lo n x := fun x ⟨i, hi, hx⟩ ↦
    not_scratch hlo hheap.hi ((hok i hi).buf_below hx).2
  have := formsAt_frame h hok hh hd hpw hheap hmono
  exact ⟨this.1, this.2, formsDeep_frame h hh hpw⟩

/-! ## A `Vec` of three forms -/

/-- A header `(3, B, 3)` at `v` over 72 allocated bytes at `B` holding three sound forms whose
buffers miss those bytes is a sound `Vec<Form>` of the three. -/
theorem formVec3 {t : MachineState} {v B : Word} (hcap : t.getMem v = 3)
    (hptr : t.getMem (v + 8) = B) (hlen : t.getMem (v + 16) = 3) (hal : B.toNat % 8 = 0)
    (hlo : heapStart ≤ B.toNat) (hhi : B.toNat + 72 ≤ heapNext t) (h0 : FormOk t B)
    (h1 : FormOk t (B + 24)) (h2 : FormOk t (B + 48))
    (hsep : ∀ x, formBuf t B x ∨ formBuf t (B + 24) x ∨ formBuf t (B + 48) x → ¬ Within x B 72) :
    FormVecOk t v ∧ formVecOf t v = [formOf t B, formOf t (B + 24), formOf t (B + 48)] ∧
      ∀ x, formVecDeep t v x →
        Within x B 72 ∨ formBuf t B x ∨ formBuf t (B + 24) x ∨ formBuf t (B + 48) x := by
  have hp : vecPtr t v = B := hptr
  have hl : (vecLen t v).toNat = 3 := by rw [vecLen, hlen]; rfl
  have hc : (vecCap t v).toNat = 3 := by rw [vecCap, hcap]; rfl
  have three {P : Word → Prop} (p0 : P B) (p1 : P (B + 24)) (p2 : P (B + 48)) :
      ∀ i < 3, P (B + BitVec.ofNat 64 (24 * i)) := by
    intro i hi
    rcases i with _ | _ | _ | i
    · simpa using p0
    · exact p1
    · exact p2
    · omega
  have hbuf : formVecBuf t v = fun x ↦ Within x B 72 := by
    funext x; simp only [formVecBuf, hp, hc]
  have hdeep : ∀ x, formsDeep t B 3 x → formBuf t B x ∨ formBuf t (B + 24) x ∨ formBuf t (B + 48) x := by
    rintro x ⟨i, hi, hx⟩
    rcases i with _ | _ | _ | i
    · exact Or.inl (by simpa using hx)
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr hx)
    · omega
  refine ⟨⟨⟨?_, by rw [hl, hc]⟩, ?_, ?_⟩, ?_, fun x hx ↦ ?_⟩
  · simp only [RawVecOk, Buf, hp, hc]
    exact ⟨hal, Or.inr ⟨hlo, by omega⟩⟩
  · rw [hp, hl]; exact three h0 h1 h2
  · rw [hp, hl, hbuf]; exact fun x hx ↦ hsep x (hdeep x hx)
  · have e : formsAt t B 3 = [formOf t (B + BitVec.ofNat 64 (24 * 0)),
        formOf t (B + BitVec.ofNat 64 (24 * 1)), formOf t (B + BitVec.ofNat 64 (24 * 2))] := rfl
    rw [formVecOf, hp, hl, e]
    simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
  · rcases hx with hx | hx
    · rw [hbuf] at hx; exact Or.inl hx
    · rw [hp, hl] at hx; exact Or.inr (hdeep x hx)

/-- `ONE` in `.rodata`, at `0xa00000b0`. -/
theorem eAt_one {s : MachineState} (h : RodataOk s) : eAt s 0xa00000b0 = 1 := by
  have h0 : s.getMem 0xa00000b0 = 1 := h.word
  have h1 : s.getMem (0xa00000b0 + 8) = 0 := h.word
  have h2 : s.getMem (0xa00000b0 + 16) = 0 := h.word
  exact eAt_eq_of_limbs (by rw [h0, h1, h2, limbs_one])

/-- `GEN` in `.rodata`, at `0xa00000c8`. -/
theorem eAt_gen {s : MachineState} (h : RodataOk s) : eAt s 0xa00000c8 = genRust := by
  have h0 : s.getMem 0xa00000c8 = 2 := h.word
  have h1 : s.getMem (0xa00000c8 + 8) = 0 := h.word
  have h2 : s.getMem (0xa00000c8 + 16) = 0 := h.word
  exact eq_of_limbs (by rw [limbs_eAt, h0, h1, h2]; rfl)

end Rv64Verifier.Layout
