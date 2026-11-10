import Rv64Verifier.Proofs.Runtime.Inv
import Rv64Verifier.Model.Layout

/-!
# Forms in memory

How the image holds `layout.rs`'s values, read off its code:

* A `Monomial` is three doublewords: the tag at `+0` (`0` for `One`, `1` for `X(i)`, `2` for
  `Xy(i, j)`), `i` at `+8`, `j` at `+16` (`Form::term`, `Form::evaluate`, `Form::add_scaled`).
  `monoOf` reads it back, any tag but `0` and `1` as `Xy`; `MonoOk` says the tag is one of the three.
* A term `(Monomial, E)` is 48 bytes, the monomial then the coefficient at `+24` (`termOf`).
* A `Form` is a `Vec` of terms: capacity, pointer and length at `+0`, `+8`, `+16` (`formOf`).
  `FormOk`: the `Vec` is allocated and every tag is valid.

A value read from memory stays the same across a step that writes none of its bytes
(`formOf_frame`): its bytes are its header's and its buffer's (`formRange`, the buffer at its
capacity, which a push writes).
-/

namespace Rv64Verifier.Layout
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Model.LayoutMirror

/-! ## Byte frames of blocks -/

/-- A block whose writes are aligned doublewords inside `w` is a byte frame of `w`. -/
theorem _root_.Rv64Verifier.Sym.Expect.Holds.byteFrame {x : Sym.Expect} {s t : MachineState}
    (h : x.Holds s t) {w : Word → Prop}
    (hw : ∀ k ∈ x.writes, (k.eval s).toNat % 8 = 0 ∧ ∀ i < 8, w (k.eval s + BitVec.ofNat 64 i)) :
    ByteFrame s t w := by
  refine ⟨fun a ha ↦ ?_, h.unaligned fun k hk ↦ (hw k hk).1⟩
  rw [byteAt_eq, byteAt_eq, h.frame _ fun k hk heq ↦ ?_]
  obtain ⟨h8, hk⟩ := hw k hk
  apply ha
  have e : a = k.eval s + BitVec.ofNat 64 (a.toNat % 8) := by
    apply BitVec.eq_of_toNat_eq
    have h1 := toNat_alignDown a
    rw [heq] at h1
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have := a.isLt
    omega
  rw [e]
  exact hk _ (Nat.mod_lt _ (by decide))

/-- Two frames in sequence: the union of their ranges. -/
theorem _root_.Rv64Verifier.Runtime.ByteFrame.union {s t u : MachineState} {w₁ w₂ : Word → Prop}
    (h₁ : ByteFrame s t w₁) (h₂ : ByteFrame t u w₂) : ByteFrame s u fun a ↦ w₁ a ∨ w₂ a :=
  ⟨fun a ha ↦ (h₂.byte a fun h ↦ ha (Or.inr h)).trans (h₁.byte a fun h ↦ ha (Or.inl h)),
    fun a ha ↦ (h₂.unaligned a ha).trans (h₁.unaligned a ha)⟩

/-- A step that writes nothing. -/
theorem byteFrame_same {t u : MachineState} (h : ∀ a, u.getMem a = t.getMem a) {s : MachineState}
    {w : Word → Prop} (hs : ByteFrame s t w) : ByteFrame s u w :=
  hs.trans (ByteFrame.of_same h fun _ ↦ False) fun _ h ↦ h.elim

/-! ## Doubleword frames

What a value read from memory needs of a step: every doubleword whose bytes miss `w` is unchanged
(`DFrame`). A byte frame (`ByteFrame`, the runtime's contracts) and a doubleword frame (`MemFrame`,
the field's) are both one. -/

/-- `t`'s doublewords whose eight bytes miss `w` are `s`'s. -/
def DFrame (s t : MachineState) (w : Word → Prop) : Prop :=
  ∀ a, (∀ x, Within x a 8 → ¬ w x) → a.toNat + 8 ≤ 2 ^ 64 → t.getMem a = s.getMem a

theorem DFrame.refl (s : MachineState) (w : Word → Prop) : DFrame s s w := fun _ _ _ ↦ rfl

theorem DFrame.mono {s t : MachineState} {w w' : Word → Prop} (h : DFrame s t w)
    (hw : ∀ a, w a → w' a) : DFrame s t w' :=
  fun a ha hw8 ↦ h a (fun x hx h' ↦ ha x hx (hw x h')) hw8

/-- Two frames in sequence: the union of their ranges. -/
theorem DFrame.union {s t u : MachineState} {w₁ w₂ : Word → Prop} (h₁ : DFrame s t w₁)
    (h₂ : DFrame t u w₂) : DFrame s u fun a ↦ w₁ a ∨ w₂ a :=
  fun a ha hw ↦ (h₂ a (fun x hx h ↦ ha x hx (Or.inr h)) hw).trans
    (h₁ a (fun x hx h ↦ ha x hx (Or.inl h)) hw)

/-- A step that writes nothing. -/
theorem DFrame.of_same {s t : MachineState} (h : ∀ a, t.getMem a = s.getMem a) (w : Word → Prop) :
    DFrame s t w := fun a _ _ ↦ h a

theorem _root_.Rv64Verifier.Runtime.ByteFrame.dframe {s t : MachineState} {w : Word → Prop}
    (h : ByteFrame s t w) : DFrame s t w :=
  fun _ ha hw ↦ h.getMem fun i hi ↦ ha _ (by addr_omega [hi, hw])

/-- A frame of doublewords outside `n` bytes from `lo`. -/
theorem _root_.Rv64Verifier.MemFrame.dframe {s t : MachineState} {lo : Word} {n : Nat}
    (h : MemFrame s t lo n) : DFrame s t (Within · lo n) :=
  fun a ha hw ↦ h a fun h' ↦ ha a (by addr_omega [hw]) h'

/-- A frame of doublewords outside three ranges (the field's contracts). -/
theorem dframe_of_three {s t : MachineState} {a₁ a₂ a₃ : Word} {n₁ n₂ n₃ : Nat}
    (h : ∀ a, ¬ Within a a₁ n₁ → ¬ Within a a₂ n₂ → ¬ Within a a₃ n₃ → t.getMem a = s.getMem a) :
    DFrame s t fun x ↦ Within x a₁ n₁ ∨ Within x a₂ n₂ ∨ Within x a₃ n₃ :=
  fun a ha hw ↦ h a (fun h' ↦ ha a (by addr_omega [hw]) (Or.inl h'))
    (fun h' ↦ ha a (by addr_omega [hw]) (Or.inr (Or.inl h')))
    (fun h' ↦ ha a (by addr_omega [hw]) (Or.inr (Or.inr h')))

/-- A frame of doublewords outside two ranges. -/
theorem dframe_of_two {s t : MachineState} {a₁ a₂ : Word} {n₁ n₂ : Nat}
    (h : ∀ a, ¬ Within a a₁ n₁ → ¬ Within a a₂ n₂ → t.getMem a = s.getMem a) :
    DFrame s t fun x ↦ Within x a₁ n₁ ∨ Within x a₂ n₂ :=
  fun a ha hw ↦ h a (fun h' ↦ ha a (by addr_omega [hw]) (Or.inl h'))
    (fun h' ↦ ha a (by addr_omega [hw]) (Or.inr h'))

/-- A doubleword whose bytes all miss a frame's range is unchanged. -/
theorem DFrame.getMem_of {s t : MachineState} {w : Word → Prop} (h : DFrame s t w)
    {a : Word} (ha : ∀ x, Within x a 8 → ¬ w x) (hw : a.toNat + 8 ≤ 2 ^ 64) :
    t.getMem a = s.getMem a :=
  h a ha hw

/-! ## The stack below a callee's `sp` -/

/-- The stack of a callee whose `sp` is `k` below the caller's, `m` bytes within the caller's `n`. -/
theorem _root_.Rv64Verifier.Runtime.RtStack.inner {s t : MachineState} {n m k : Nat}
    (h : RtStack s n) (hsp : t.getReg .x2 = s.getReg .x2 - BitVec.ofNat 64 k) (hk : k + m ≤ n)
    (hk16 : k % 16 = 0) (hm : m % 8 = 0) (hn : 8 ≤ n) (hn8 : n % 8 = 0) : RtStack t m := by
  have hb := h.bounds hn hn8
  have ha := h.above
  have hx := h.next
  have hr := h.rodata
  have hsp' := (s.getReg .x2).isLt
  have hk' : k < 2 ^ 64 := by omega
  have hm' : m < 2 ^ 64 := by omega
  have hn' : n < 2 ^ 64 := by omega
  have hd : n - k - m < 2 ^ 64 := by omega
  have hlo : stackLo t m = stackLo s n + BitVec.ofNat 64 (n - k - m) := by
    simp only [stackLo, hsp]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk',
      Nat.mod_eq_of_lt hm', Nat.mod_eq_of_lt hn', Nat.mod_eq_of_lt hd]
    omega
  have hlo' : (stackLo t m).toNat = (s.getReg .x2).toNat - k - m := by
    rw [hlo, BitVec.toNat_add, hb.2.2.2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]
    omega
  have hlo₀ := hb.2.2.2
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · have hadd : (stackLo s n + BitVec.ofNat 64 (n - k - m)).toNat = (stackLo s n).toNat + (n - k - m) := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd, hlo₀]
      omega
    rw [hlo]
    exact ValidMemRange.sub h.valid (by omega) (by omega) (by omega)
  · rw [hsp, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk']; omega
  · rw [hlo']; simp only [heapEnd] at ha ⊢; omega
  · simp only [Apart, hlo'] at hx ⊢; simp only [nextAddr] at hx ⊢; omega
  · simp only [Apart, hlo'] at hr ⊢; simp only [rodataStart, rodataSize] at hr ⊢; omega

/-- Every byte of an aligned doubleword within `n` bytes from `p` is within them. -/
theorem within_dword {p k : Word} {n : Nat} (h : k.toNat + 8 ≤ p.toNat + n) (h' : p.toNat ≤ k.toNat)
    (hk : k.toNat + 8 ≤ 2 ^ 64) : ∀ i < 8, Within (k + BitVec.ofNat 64 i) p n := by
  intro i hi
  addr_omega [h, h', hk, hi]

/-- Aligned doublewords in a data window are valid. -/
theorem validMemRange_of {a : Word} {n : Nat} (h8 : a.toNat % 8 = 0)
    (h : (0x20 ≤ a.toNat ∧ a.toNat + 8 * n ≤ 0x78000000) ∨
      (0xa0000000 ≤ a.toNat ∧ a.toNat + 8 * n ≤ 0xc0000000)) : ValidMemRange a n := by
  intro i hi
  show Sym.validAccess 8 _ = true
  rw [Sym.validAccess_eight]
  have : (a + BitVec.ofNat 64 (8 * i)).toNat = a.toNat + 8 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have := a.isLt
    omega
  rw [this]
  omega

/-! ## Monomials, terms, forms -/

/-- The `Monomial` at `a`. -/
def monoOf (s : MachineState) (a : Word) : Monomial :=
  if s.getMem a = 0 then .one
  else if s.getMem a = 1 then .x (s.getMem (a + 8)).toNat
  else .xy (s.getMem (a + 8)).toNat (s.getMem (a + 16)).toNat

/-- Its tag is `One`'s, `X`'s or `Xy`'s. -/
def MonoOk (s : MachineState) (a : Word) : Prop := (s.getMem a).toNat ≤ 2

/-- The term at `a`: the monomial, then the coefficient at `+24`. -/
def termOf (s : MachineState) (a : Word) : Term := (monoOf s a, eAt s (a + 24))

/-- The `n` terms from `p`, 48 bytes apart. -/
def termsOf (s : MachineState) (p : Word) (n : Nat) : List Term :=
  (List.range n).map fun i ↦ termOf s (p + BitVec.ofNat 64 (48 * i))

/-- The `Form` at `a`. -/
def formOf (s : MachineState) (a : Word) : FormRust :=
  ⟨termsOf s (vecPtr s a) (vecLen s a).toNat⟩

/-- The `Form` at `a` is an allocated `Vec` whose tags are valid. -/
structure FormOk (s : MachineState) (a : Word) : Prop where
  vec : VecOk s a 48 8
  tags : ∀ i < (vecLen s a).toNat, MonoOk s (vecPtr s a + BitVec.ofNat 64 (48 * i))

/-- The bytes of the `Form`'s buffer, at its capacity. -/
@[rv_addr] def formBuf (s : MachineState) (a : Word) (x : Word) : Prop :=
  Within x (vecPtr s a) (48 * (vecCap s a).toNat)

theorem termsOf_length (s : MachineState) (p : Word) (n : Nat) : (termsOf s p n).length = n := by
  simp [termsOf]

theorem termsOf_getElem (s : MachineState) (p : Word) (n i : Nat)
    (h : i < (termsOf s p n).length) :
    (termsOf s p n)[i] = termOf s (p + BitVec.ofNat 64 (48 * i)) := by
  simp [termsOf]

/-! ## Values across frames -/

/-- A doubleword whose bytes all miss a frame's range is unchanged. -/
theorem _root_.Rv64Verifier.Runtime.ByteFrame.getMem_of {s t : MachineState} {w : Word → Prop} (h : ByteFrame s t w)
    {a : Word} (ha : ∀ x, Within x a 8 → ¬ w x) (hw : a.toNat + 8 ≤ 2 ^ 64) :
    t.getMem a = s.getMem a :=
  h.getMem fun i hi ↦ ha _ (by addr_omega [hi, hw])

theorem monoOf_congr {s t : MachineState} {a b : Word} (h0 : t.getMem a = s.getMem b)
    (h1 : t.getMem (a + 8) = s.getMem (b + 8)) (h2 : t.getMem (a + 16) = s.getMem (b + 16)) :
    monoOf t a = monoOf s b := by
  simp only [monoOf, h0, h1, h2]

theorem eAt_congr' {s t : MachineState} {a : Word} (h0 : t.getMem a = s.getMem a)
    (h1 : t.getMem (a + 8) = s.getMem (a + 8)) (h2 : t.getMem (a + 16) = s.getMem (a + 16)) :
    eAt t a = eAt s a := by
  simp only [eAt, h0, h1, h2]

/-- A term whose 48 bytes miss a frame's range is unchanged. -/
theorem termOf_frame {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {a : Word}
    (ha : ∀ x, Within x a 48 → ¬ w x) (hw : a.toNat + 48 ≤ 2 ^ 64) :
    termOf t a = termOf s a ∧ (MonoOk s a → MonoOk t a) := by
  have g (k : Nat) (hk : k + 8 ≤ 48) : t.getMem (a + BitVec.ofNat 64 k) = s.getMem (a + BitVec.ofNat 64 k) :=
    h.getMem_of (fun x hx ↦ ha x (by addr_omega [hx, hk, hw])) (by addr_omega [hk, hw])
  have g0 : t.getMem a = s.getMem a := by simpa using g 0 (by decide)
  have g8 := g 8 (by decide)
  have g16 := g 16 (by decide)
  have g24 := g 24 (by decide)
  have g32 := g 32 (by decide)
  have g40 := g 40 (by decide)
  refine ⟨?_, fun hm ↦ ?_⟩
  · simp only [termOf, monoOf_congr g0 g8 g16, Prod.mk.injEq, true_and]
    apply eAt_congr'
    · exact g24
    · rw [BitVec.add_assoc]; exact g32
    · rw [BitVec.add_assoc]; exact g40
  · simp only [MonoOk, g0]; exact hm

/-- The `Form` at `a` is unchanged, and still sound, across a frame that writes neither its
header nor its buffer, and keeps `NEXT` from going down. -/
theorem formOf_frame {s t : MachineState} {w : Word → Prop} (h : DFrame s t w) {a : Word}
    (hok : FormOk s a) (ha : ∀ x, Within x a 24 → ¬ w x) (hb : ∀ x, formBuf s a x → ¬ w x)
    (haw : a.toNat + 24 ≤ 2 ^ 64) (hheap : HeapOk s) (hmono : heapNext s ≤ heapNext t) :
    formOf t a = formOf s a ∧ FormOk t a := by
  have hc : t.getMem a = s.getMem a := h.getMem_of (fun x hx ↦ ha x (by addr_omega [hx, haw]))
    (by addr_omega [haw])
  have hp : t.getMem (a + 8) = s.getMem (a + 8) :=
    h.getMem_of (fun x hx ↦ ha x (by addr_omega [hx, haw])) (by addr_omega [haw])
  have hl : t.getMem (a + 16) = s.getMem (a + 16) :=
    h.getMem_of (fun x hx ↦ ha x (by addr_omega [hx, haw])) (by addr_omega [haw])
  have hraw := hok.vec.raw
  have hlen := hok.vec.len
  have hhi := hheap.hi
  simp only [RawVecOk, Buf, vecCap, vecPtr, vecLen, heapNext] at hraw hlen hc hp hl hhi
  have hterm (i : Nat) (hi : i < (s.getMem (a + 16)).toNat) :=
    termOf_frame h (a := s.getMem (a + 8) + BitVec.ofNat 64 (48 * i))
      (fun x hx ↦ hb x (by
        simp only [formBuf, vecPtr, vecCap]
        rcases hraw.2 with h0 | h0
        · exfalso; rw [Nat.mul_eq_zero] at h0; omega
        · addr_omega [hx, h0, hi, hlen, hhi]))
      (by
        rcases hraw.2 with h0 | h0
        · exfalso; rw [Nat.mul_eq_zero] at h0; omega
        · addr_omega [h0, hi, hlen, hhi])
  refine ⟨?_, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · simp only [formOf, vecPtr, vecLen, hp, hl, termsOf, FormRust.mk.injEq]
    apply List.map_congr_left
    intro i hi
    exact (hterm i (List.mem_range.mp hi)).1
  · simp only [RawVecOk, Buf, vecCap, vecPtr, heapNext, hc, hp]
    simp only [heapNext] at hmono
    omega
  · simp only [vecCap, vecLen, hc, hl]
    exact hlen
  · intro i hi
    simp only [vecLen, hl] at hi
    simp only [vecPtr, hp]
    exact (hterm i hi).2 (hok.tags i (by simpa [vecLen] using hi))

end Rv64Verifier.Layout
