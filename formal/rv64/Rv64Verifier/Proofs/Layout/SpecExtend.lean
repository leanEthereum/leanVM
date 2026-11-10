import Rv64Verifier.Proofs.Layout.CloneLemmas
import Rv64Verifier.Blocks.F90

/-!
# `Vec<Form>::spec_extend` from a slice, at `0x80011db8`

```rust
fn spec_extend(&mut self, iter: slice::Iter<'_, Form>) {
    self.reserve(iter.len());
    for form in iter { push_unchecked(form.clone()) }    // set_len at the end
}
```

compiled (`Blocks/F90.lean`): `0x80011db8` makes a 112-byte frame, saves `ra`, `s0`..`s8`, computes
the count `n = (end - begin) / 24` and calls `reserve(self, n)`; `0x80011e1c` reads the length and
returns at once for an empty slice (`0x80011ebc`); `0x80011e24` points `s6` at the first form's
length and `s7` at the first free slot's pointer field. The loop head `0x80011e64` calls
`try_allocate_in(sp + 8, len, 0, 8, 48)` for the form's terms (`0x80011e88` traps on an error),
`0x80011e90`/`0x80011e9c` `memcpy` them unless empty, and `0x80011e44` writes the clone's header into
the slot and advances. `0x80011ebc` writes the new length, restores and returns.

`reserve`'s contract as the runtime states it does not say where the buffer it leaves is; the loop
writes past the old length, so the proof takes it with that (`ReserveFreshSpec`): the old buffer, or
a new one.
-/

namespace Rv64Verifier.Layout.SpecExtend
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Blocks.F90
  Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- `Vec<Form>::reserve`, its buffer the old one or a new one. -/
def ReserveFreshSpec : Prop :=
  FunSpec Image.code 0x80004aec (ReservePre 24 8) fun s t ↦ ReservePost 24 8 s t ∧
    ((vecPtr t (s.getReg .x10) = vecPtr s (s.getReg .x10) ∧
      vecCap t (s.getReg .x10) = vecCap s (s.getReg .x10)) ∨
    NewBuf s t (vecPtr t (s.getReg .x10)) ((vecCap t (s.getReg .x10)).toNat * 24) 8)

/-- The slice's length. -/
def nOf (s : MachineState) : Nat := ((s.getReg .x12).toNat - (s.getReg .x11).toNat) / 24

/-- The `Vec`'s length at entry. -/
def lenOf (s : MachineState) : Nat := (vecLen s (s.getReg .x10)).toNat

/-- The count as computed. -/
def cntOf (s : MachineState) : Word :=
  ((s.getReg .x12 - s.getReg .x11) >>> 3) * (0xaaaaaaaaaaaaaaab : Word)

theorem cntOf_toNat {s : MachineState} (hpre : SpecExtendPre s) : (cntOf s).toNat = nOf s := by
  have hb := hpre.bounds
  have hw := hpre.whole
  have h1 := (s.getReg .x11).isLt
  have h2 := (s.getReg .x12).isLt
  have hd : (s.getReg .x12 - s.getReg .x11).toNat = (s.getReg .x12).toNat - (s.getReg .x11).toNat := by
    rw [BitVec.toNat_sub]; omega
  rw [cntOf, count_eq _ (by rw [hd]; exact hw), hd, nOf]

theorem vecOk_congr {s t : MachineState} {a : Word} {size align : Nat}
    (h0 : t.getMem a = s.getMem a) (h8 : t.getMem (a + 8) = s.getMem (a + 8))
    (h16 : t.getMem (a + 16) = s.getMem (a + 16)) (hn : heapNext s ≤ heapNext t)
    (h : VecOk s a size align) : VecOk t a size align := by
  have hr := h.raw
  have hl := h.len
  simp only [RawVecOk, Buf, vecPtr, vecCap, vecLen] at hr hl
  refine ⟨?_, ?_⟩
  · simp only [RawVecOk, Buf, vecPtr, vecCap, h0, h8]
    exact ⟨hr.1, hr.2.imp id fun h' ↦ ⟨h'.1, Nat.le_trans h'.2 hn⟩⟩
  · simp only [vecLen, vecCap, h0, h16]; exact hl

/-- From the entry `s` to `r`, back from `reserve`, called at `t₁`. -/
structure Ctx (s t₁ r : MachineState) : Prop where
  pc : r.pc = 0x80011e1c
  sp₁ : t₁.getReg .x2 = s.getReg .x2 - 112
  sp : r.getReg .x2 = s.getReg .x2 - 112
  x8 : r.getReg .x8 = s.getReg .x10
  x9 : r.getReg .x9 = cntOf s
  x18 : r.getReg .x18 = s.getReg .x11
  x19 : r.getReg .x19 = s.getReg .x12
  kept : ∀ q ∈ [Reg.x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27], r.getReg q = s.getReg q
  saved : ∀ a : Word, (s.getReg .x2).toNat - 80 ≤ a.toNat → a.toNat + 8 ≤ (s.getReg .x2).toNat →
    r.getMem a = t₁.getMem a
  ra : t₁.getMem (s.getReg .x2 - 8) = s.getReg .x1
  s0 : t₁.getMem (s.getReg .x2 - 16) = s.getReg .x8
  s1 : t₁.getMem (s.getReg .x2 - 24) = s.getReg .x9
  s2 : t₁.getMem (s.getReg .x2 - 32) = s.getReg .x18
  s3 : t₁.getMem (s.getReg .x2 - 40) = s.getReg .x19
  s4 : t₁.getMem (s.getReg .x2 - 48) = s.getReg .x20
  s5 : t₁.getMem (s.getReg .x2 - 56) = s.getReg .x21
  s6 : t₁.getMem (s.getReg .x2 - 64) = s.getReg .x22
  s7 : t₁.getMem (s.getReg .x2 - 72) = s.getReg .x23
  s8 : t₁.getMem (s.getReg .x2 - 80) = s.getReg .x24
  heap : HeapOk r
  mono : heapNext s ≤ heapNext r
  vec : VecOk r (s.getReg .x10) 24 8
  cap : lenOf s + nOf s ≤ (vecCap r (s.getReg .x10)).toNat
  len : vecLen r (s.getReg .x10) = vecLen s (s.getReg .x10)
  fresh : (vecPtr r (s.getReg .x10) = vecPtr s (s.getReg .x10) ∧
      vecCap r (s.getReg .x10) = vecCap s (s.getReg .x10)) ∨
    NewBuf s r (vecPtr r (s.getReg .x10)) ((vecCap r (s.getReg .x10)).toNat * 24) 8
  old : ∀ k, k % 8 = 0 → k + 8 ≤ 24 * lenOf s →
    r.getMem (vecPtr r (s.getReg .x10) + BitVec.ofNat 64 k) =
      s.getMem (vecPtr s (s.getReg .x10) + BitVec.ofNat 64 k)
  frame : DFrame s r fun x ↦ Within x (s.getReg .x10) 24 ∨
    Within x (stackLo s specExtendStack) specExtendStack ∨ Within x nextAddr 8 ∨ Fresh s r x

/-- `sp` and the arguments as numbers. -/
theorem _root_.Rv64Verifier.Layout.SpecExtendPre.bounds' {s : MachineState} (hpre : SpecExtendPre s) :
    0x78000000 + 272 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ (s.getReg .x10).toNat % 8 = 0 ∧
      (s.getReg .x10).toNat + 24 ≤ 0xc0000008 := by
  have := hpre.stack.bounds (by decide) (by decide)
  have ha := hpre.stack.above
  have ho := ValidMemRange.bounds hpre.self (by decide)
  simp only [specExtendStack, reserveStack, stackLo, heapEnd] at this ha
  rw [this.2.2.2] at ha
  omega

/-- The prologue and `reserve`. -/
theorem setup (hR : ReserveFreshSpec) {s : MachineState} (hpc : s.pc = 0x80011db8)
    (hpre : SpecExtendPre s) :
    ∃ r, Reaches Image.code s r ∧ ((∃ t₁, Ctx s t₁ r) ∨ Dead Image.code r) := by
  have hb := hpre.bounds'
  have hst := hpre.stack
  have hnx := hst.next
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  simp only [specExtendStack, reserveStack] at hnx hss
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80011db8_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hst.valid [hb])
  have k₁ := b80011db8_keeps h₁
  have hm₁ := b80011db8_frame h₁ (by addr_omega [hb])
  have x2₁ := b80011db8_x2 h₁
  have x10₁ : t₁.getReg .x10 = s.getReg .x10 := k₁ .x10 (by decide)
  have hh (a : Word) (ha : Apart a 8 (s.getReg .x2 - 80) 80) : t₁.getMem a = s.getMem a :=
    hm₁ a (by addr_omega [ha])
  have e0 := hh (s.getReg .x10) (by addr_omega [hss, hb])
  have e8 := hh (s.getReg .x10 + 8) (by addr_omega [hss, hb])
  have e16 := hh (s.getReg .x10 + 16) (by addr_omega [hss, hb])
  have hn₁ : t₁.getMem nextAddr = s.getMem nextAddr := hh _ (by addr_omega [hnx, hb])
  have hnext₁ : heapNext t₁ = heapNext s := by simp only [heapNext, hn₁]
  have hres : ReservePre 24 8 t₁ := {
    heap := ⟨hnext₁ ▸ hpre.heap.lo, hnext₁ ▸ hpre.heap.hi⟩
    self := by rw [x10₁]; exact hpre.self
    vec := by rw [x10₁]; exact vecOk_congr e0 e8 e16 hnext₁.ge hpre.ok.vec
    stack := hst.inner (k := 112) x2₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    selfFree := by rw [x10₁]; simp only [Outside, hnext₁]; exact hsf
    selfStack := by rw [x10₁]; addr_omega [hss, hb, x2₁] }
  obtain ⟨r, hr₂, ⟨hpc₂, hpres₂, hpost, hfresh⟩ | hdead⟩ := hR.call hr₁ (b80011db8_pc h₁) hres
  swap
  · exact ⟨r, hr₂, Or.inr hdead⟩
  have hpf := hpost.frame.dframe
  have hpcap := hpost.cap
  have hpvec := hpost.vec
  have hplen := hpost.len
  have hpbytes := hpost.bytes
  have hhi₂ := hpost.heap.hi
  have hab := hst.above
  simp only [specExtendStack, reserveStack, stackLo, heapEnd] at hab
  rw [x10₁] at hpf hpcap hpvec hplen hpbytes hfresh
  rw [show stackLo t₁ reserveStack = s.getReg .x2 - 272 by
    simp only [stackLo, x2₁, reserveStack]; rv_eval []] at hpf
  have hcnt := cntOf_toNat hpre
  have hsv := hpre.ok.vec
  have hraw := hsv.raw
  have hsl := hsv.len
  simp only [RawVecOk, Buf] at hraw
  simp only [heapNext, heapEnd] at hhi₂
  refine ⟨r, hr₂, Or.inl ⟨t₁, {
    pc := by rw [hpc₂, returnAddress_eq, b80011db8_x1 h₁]; decide
    sp₁ := x2₁
    sp := (hpres₂.reg .x2).trans x2₁
    x8 := (hpres₂.reg .x8).trans (b80011db8_x8 h₁)
    x9 := (hpres₂.reg .x9).trans (b80011db8_x9 h₁)
    x18 := (hpres₂.reg .x18).trans (b80011db8_x18 h₁)
    x19 := (hpres₂.reg .x19).trans (b80011db8_x19 h₁)
    kept := fun q hq ↦ (hpres₂ q (mem_of_mem hq _)).trans (k₁ q (mem_of_mem hq _))
    saved := fun a h1 h2 ↦ hpf.getMem_of (fun x hx h ↦ by
        rcases h with h | h | h | h
        · addr_omega [hx, h, hss, hb, h1, h2]
        · addr_omega [hx, h, hb, h1, h2]
        · addr_omega [hx, h, hnx, hb, h1, h2]
        · simp only [Fresh, heapNext] at h; addr_omega [hx, h, hab, hb, h1, h2, hhi₂])
      (by addr_omega [hb, h2])
    ra := b80011db8_m_x2_n8 h₁
    s0 := b80011db8_m_x2_n16 h₁
    s1 := b80011db8_m_x2_n24 h₁
    s2 := b80011db8_m_x2_n32 h₁
    s3 := b80011db8_m_x2_n40 h₁
    s4 := b80011db8_m_x2_n48 h₁
    s5 := b80011db8_m_x2_n56 h₁
    s6 := b80011db8_m_x2_n64 h₁
    s7 := b80011db8_m_x2_n72 h₁
    s8 := b80011db8_m_x2_n80 h₁
    heap := hpost.heap
    mono := hnext₁ ▸ hpost.mono
    vec := hpvec
    cap := by
      have := hpcap
      rw [b80011db8_x11 h₁] at this
      simp only [vecLen, e16] at this
      simp only [lenOf, vecLen]
      rw [← hcnt]; exact this
    len := by rw [hplen]; simp only [vecLen, e16]
    fresh := by
      rcases hfresh with ⟨h1, h2⟩ | h
      · exact Or.inl ⟨by rw [h1]; simp only [vecPtr, e8], by rw [h2]; simp only [vecCap, e0]⟩
      · exact Or.inr (by simpa only [NewBuf, hnext₁] using h)
    old := fun k hk hkN ↦ by
      have hsl' : (s.getMem (s.getReg .x10 + 16)).toNat ≤ (s.getMem (s.getReg .x10)).toNat := hsl
      simp only [lenOf, vecLen] at hkN
      have hcap0 : 0 < (s.getMem (s.getReg .x10)).toNat := by omega
      have hpal := hpvec.raw.1
      have g := getMem_eq_of_bytesAt hpbytes hpal (by simp only [vecPtr, e8]; exact hraw.1) hk
        (by simp only [vecCap, e0]; omega)
      rw [g]
      simp only [vecPtr, e8]
      rcases hraw.2 with h0 | h0
      · exfalso; simp only [vecCap] at h0; rw [Nat.mul_eq_zero] at h0; omega
      · simp only [vecPtr, vecCap, heapNext, heapStart] at h0
        have hhs := hpre.heap.hi
        simp only [heapNext, heapEnd] at hhs
        exact hh _ (by addr_omega [h0, hb, hhs, hkN, hsl', hk])
    frame := (hm₁.dframe.union hpf).mono fun a h ↦ by
      rcases h with h | h | h | h | h
      · exact Or.inr (Or.inl (by addr_omega [h, hb]))
      · exact Or.inl (by addr_omega [h])
      · exact Or.inr (Or.inl (by addr_omega [h, hb]))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (by simpa only [Fresh, hnext₁] using h))) }⟩⟩


/-- The slot of the `j`-th clone. -/
def slot (s r : MachineState) (j : Nat) : Word :=
  vecPtr r (s.getReg .x10) + BitVec.ofNat 64 (24 * (lenOf s + j))

/-- The `j`-th source form. -/
def src (s : MachineState) (j : Nat) : Word := s.getReg .x11 + BitVec.ofNat 64 (24 * j)

/-- The sources' bytes: their headers and buffers. -/
@[rv_addr] def srcFoot (s : MachineState) (x : Word) : Prop :=
  Within x (s.getReg .x11) (24 * nOf s) ∨ formsDeep s (s.getReg .x11) (nOf s) x

/-- `k` forms cloned, from `r` on: the slots written, the stack below the saved registers, `NEXT`
and what is allocated changed, the saved registers kept. -/
structure Core (s t₁ r u : MachineState) (k : Nat) : Prop where
  heap : HeapOk u
  mono : heapNext r ≤ heapNext u
  saved : ∀ a : Word, (s.getReg .x2).toNat - 80 ≤ a.toNat → a.toNat + 8 ≤ (s.getReg .x2).toNat →
    u.getMem a = t₁.getMem a
  frame : DFrame r u fun x ↦ Within x (slot s r 0) (24 * k) ∨
    Within x (s.getReg .x2 - 272) 192 ∨ Within x nextAddr 8 ∨ Fresh r u x
  new : ∀ j < k, formOf u (slot s r j) = formOf s (src s j) ∧ FormOk u (slot s r j) ∧
    ∀ x, formBuf u (slot s r j) x → Fresh r u x

/-- At the loop head, `k` forms cloned. -/
structure Inv (s t₁ r u : MachineState) (k : Nat) : Prop extends Core s t₁ r u k where
  lt : k < nOf s
  pc : u.pc = 0x80011e64
  sp : u.getReg .x2 = s.getReg .x2 - 112
  x8 : u.getReg .x8 = s.getReg .x10
  x9 : u.getReg .x9 = cntOf s - BitVec.ofNat 64 k
  x21 : u.getReg .x21 = vecLen s (s.getReg .x10) + BitVec.ofNat 64 k
  x22 : u.getReg .x22 = src s k + 16
  x23 : u.getReg .x23 = slot s r k + 8
  kept : ∀ q ∈ [Reg.x25, .x26, .x27], u.getReg q = s.getReg q

/-- At the epilogue, every form cloned. -/
structure AtExit (s t₁ r u : MachineState) : Prop extends Core s t₁ r u (nOf s) where
  pc : u.pc = 0x80011ebc
  sp : u.getReg .x2 = s.getReg .x2 - 112
  x8 : u.getReg .x8 = s.getReg .x10
  x21 : u.getReg .x21 = vecLen s (s.getReg .x10) + BitVec.ofNat 64 (nOf s)
  kept : ∀ q ∈ [Reg.x25, .x26, .x27], u.getReg q = s.getReg q

/-- The numbers the loop needs. -/
structure Nums (s r : MachineState) : Prop where
  sp : 0x78000000 + 272 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
    (s.getReg .x2).toNat % 16 = 0
  self : (s.getReg .x10).toNat % 8 = 0 ∧ (s.getReg .x10).toNat + 24 ≤ 0xc0000008
  ptr : (vecPtr r (s.getReg .x10)).toNat % 8 = 0
  buf : 0x20000000 ≤ (vecPtr r (s.getReg .x10)).toNat ∧
    (vecPtr r (s.getReg .x10)).toNat + 24 * (vecCap r (s.getReg .x10)).toNat ≤ heapNext r
  cap : lenOf s + nOf s ≤ (vecCap r (s.getReg .x10)).toNat
  next : heapNext s ≤ heapNext r ∧ heapNext r ≤ 0x78000000
  src : 0x20 ≤ (s.getReg .x11).toNat ∧ (s.getReg .x11).toNat % 8 = 0 ∧
    (s.getReg .x11).toNat + 24 * nOf s ≤ 0xc0000008

theorem nums {s t₁ r : MachineState} (hpre : SpecExtendPre s) (ctx : Ctx s t₁ r) (hn : 0 < nOf s) :
    Nums s r := by
  have hb := hpre.bounds'
  have hraw := ctx.vec.raw
  have hcap := ctx.cap
  have hhi := ctx.heap.hi
  have hw := hpre.whole
  have hbd := hpre.bounds
  have hs := ValidMemRange.bounds hpre.src (by simp only [nOf] at hn; omega)
  simp only [RawVecOk, Buf] at hraw
  refine ⟨⟨hb.1, hb.2.1, hb.2.2.1⟩, hb.2.2.2, hraw.1, ?_, hcap, ⟨ctx.mono, hhi⟩, ?_⟩
  · rcases hraw.2 with h0 | h0
    · exfalso; rw [Nat.mul_eq_zero] at h0; omega
    · simp only [heapStart] at h0; omega
  · simp only [nOf]; omega

/-- The sources miss everything written from the entry on. -/
theorem srcApart {s t₁ r u : MachineState} {k : Nat} (hpre : SpecExtendPre s) (ctx : Ctx s t₁ r)
    (hn : 0 < nOf s) (hk : k ≤ nOf s) (hu : heapNext u ≤ 0x78000000) {x : Word} (hx : srcFoot s x) :
    ¬ ((Within x (s.getReg .x10) 24 ∨ Within x (stackLo s specExtendStack) specExtendStack ∨
      Within x nextAddr 8 ∨ Fresh s r x) ∨ (Within x (slot s r 0) (24 * k) ∨
      Within x (s.getReg .x2 - 272) 192 ∨ Within x nextAddr 8 ∨ Fresh r u x)) := by
  have N := nums hpre ctx hn
  have hab := hpre.stack.above
  have hss := hpre.srcStack
  have hsf := hpre.srcFree
  have hapart := hpre.apart
  have hnx := hpre.stack.next
  simp only [specExtendStack, reserveStack, stackLo, heapEnd] at hab hss hnx
  simp only [Outside, heapNext, heapEnd] at hsf
  have hbd := hpre.bounds
  have hlen : (s.getReg .x12).toNat - (s.getReg .x11).toNat = 24 * nOf s := by
    have := hpre.whole; simp only [nOf]; omega
  have hdiv : 24 * nOf s / 24 = nOf s := Nat.mul_div_cancel_left _ (by decide)
  rw [hlen] at hss hsf hapart
  simp only [hdiv] at hapart
  have hhs := hpre.heap.hi
  simp only [heapNext, heapEnd] at hhs
  have N2 := N.next
  have N3 := N.buf
  have N4 := N.cap
  simp only [heapNext] at N2 N3
  -- the slots lie in `r`'s buffer: the old one, or one allocated after the entry
  have hslot : Within x (slot s r 0) (24 * k) → formVecBuf s (s.getReg .x10) x ∨
      (heapNext s ≤ x.toNat ∧ x.toNat < heapNext r) := by
    intro h
    simp only [slot, Nat.add_zero] at h
    rcases ctx.fresh with ⟨h1, h2⟩ | h3
    · left
      simp only [formVecBuf]
      rw [h1] at h
      rw [h2] at N4
      rw [h1, h2] at N3
      addr_omega [h, N4, N3, N2, hk]
    · right
      simp only [NewBuf, heapNext] at h3
      simp only [heapNext]
      rcases h3.2 with h0 | h0
      · exfalso; rw [Nat.mul_eq_zero] at h0; simp only [Within] at h; omega
      · addr_omega [h, N4, h0, N3, N2, hk]
  rcases hx with hx | hx
  · -- a header
    have hx' := hapart x (Or.inl hx)
    intro h
    rcases h with (h | h | h | h) | (h | h | h | h)
    · exact hx' (Or.inl h)
    · addr_omega [hx, h, hss]
    · addr_omega [hx, h, hsf.2]
    · simp only [Fresh, heapNext] at h; addr_omega [hx, h, hsf.1, N2]
    · rcases hslot h with h' | h'
      · exact hx' (Or.inr h')
      · simp only [heapNext] at h'; addr_omega [hx, h', hsf.1, N2]
    · addr_omega [hx, h, hss, N.sp]
    · addr_omega [hx, h, hsf.2]
    · simp only [Fresh, heapNext] at h; addr_omega [hx, h, hsf.1, N2, hu]
  · -- a buffer
    have hx' := hapart x (Or.inr hx)
    obtain ⟨j, hj, hxj⟩ := hx
    have hbl := formBuf_below (hpre.srcOk j hj) hxj
    simp only [heapNext, heapStart] at hbl
    intro h
    rcases h with (h | h | h | h) | (h | h | h | h)
    · exact hx' (Or.inl h)
    · addr_omega [hbl, h, N.sp, hab, hhs]
    · addr_omega [hbl, h, N2]
    · simp only [Fresh, heapNext] at h; omega
    · rcases hslot h with h' | h'
      · exact hx' (Or.inr h')
      · simp only [heapNext] at h'; omega
    · addr_omega [hbl, h, N.sp, N2]
    · addr_omega [hbl, h, N2]
    · simp only [Fresh, heapNext] at h; omega

/-- The `j`-th source at `u` is the entry's. -/
theorem src_same {s t₁ r u : MachineState} {k : Nat} (hpre : SpecExtendPre s) (ctx : Ctx s t₁ r)
    (hc : Core s t₁ r u k) (hn : 0 < nOf s) (hk : k ≤ nOf s) {j : Nat} (hj : j < nOf s) :
    formOf u (src s j) = formOf s (src s j) ∧ FormOk u (src s j) ∧
      vecLen u (src s j) = vecLen s (src s j) ∧ vecPtr u (src s j) = vecPtr s (src s j) := by
  have N := nums hpre ctx hn
  have hf := ctx.frame.union hc.frame
  have hhi := hc.heap.hi
  simp only [heapNext, heapEnd] at hhi
  have ha := fun x hx ↦ srcApart hpre ctx hn hk hhi (x := x) hx
  have hsrc := N.src
  have hh : ∀ x, Within x (src s j) 24 → srcFoot s x := fun x hx ↦
    Or.inl (by simp only [src] at hx; addr_omega [hx, hj, hsrc])
  have hfo := formOf_frame hf (hpre.srcOk j hj) (fun x hx ↦ ha x (hh x hx))
    (fun x hx ↦ ha x (Or.inr ⟨j, hj, hx⟩)) (by addr_omega [hj, hsrc])
    hpre.heap (ctx.mono.trans hc.mono)
  refine ⟨hfo.1, hfo.2, ?_, ?_⟩
  · simp only [vecLen]
    exact hf.getMem_of (fun x hx ↦ ha x (hh x (by simp only [src] at hx ⊢; addr_omega [hx, hj, hsrc])))
      (by simp only [src]; addr_omega [hj, hsrc])
  · simp only [vecPtr]
    exact hf.getMem_of (fun x hx ↦ ha x (hh x (by simp only [src] at hx ⊢; addr_omega [hx, hj, hsrc])))
      (by simp only [src]; addr_omega [hj, hsrc])

theorem trap : Image.code.fetch 0x80011ef0 = none :=
  Option.isNone_iff_eq_none.mp (by decide +kernel)

/-- The clone of form `k`, before its header is written: at `0x80011e44`, its terms copied into a
new buffer `p`. -/
structure Cloned (s u y : MachineState) (k : Nat) (p : Word) : Prop where
  pc : y.pc = 0x80011e44
  regs : ∀ q ∈ [Reg.x2, .x8, .x9, .x21, .x22, .x23, .x25, .x26, .x27], y.getReg q = u.getReg q
  x24 : y.getReg .x24 = vecLen s (src s k)
  x20 : y.getReg .x20 = p
  x18 : y.getReg .x18 = vecLen s (src s k)
  heap : HeapOk y
  mono : heapNext u ≤ heapNext y
  fresh : NewBuf u y p ((vecLen s (src s k)).toNat * 48) 8
  copy : ∀ k', k' % 8 = 0 → k' + 8 ≤ 48 * (vecLen s (src s k)).toNat →
    y.getMem (p + BitVec.ofNat 64 k') = s.getMem (vecPtr s (src s k) + BitVec.ofNat 64 k')
  frame : DFrame u y fun x ↦ Within x (s.getReg .x2 - 160) 80 ∨ Within x nextAddr 8 ∨ Fresh u y x

/-- `try_allocate_in` and `memcpy` for form `k`. -/
theorem cloneStep (hT : TryAllocZeroedSpec) (hM : MemcpySpec 0x800126e4) {s t₁ r u : MachineState}
    {k : Nat} (hpre : SpecExtendPre s) (ctx : Ctx s t₁ r) (hi : Inv s t₁ r u k) :
    ∃ y, Reaches Image.code u y ∧ ((∃ p, Cloned s u y k p) ∨ Dead Image.code y) := by
  have hn : 0 < nOf s := by have := hi.lt; omega
  have N := nums hpre ctx hn
  have hsrc := N.src
  have hk := hi.lt
  have hst := hpre.stack
  have hab := hst.above
  have hnx := hst.next
  simp only [specExtendStack, reserveStack, stackLo, heapEnd] at hab hnx
  obtain ⟨hfs, hok, hlen, hptr⟩ := src_same hpre ctx hi.toCore hn (Nat.le_of_lt hk) hk
  have hsv : ValidMemRange (s.getReg .x11) (3 * nOf s) := by
    have := hpre.src; have hw := hpre.whole; have hbd := hpre.bounds
    rw [show ((s.getReg .x12).toNat - (s.getReg .x11).toNat) / 8 = 3 * nOf s by
      simp only [nOf]; omega] at this
    exact this
  have hx22 := hi.x22
  simp only [src] at hx22
  -- the call to `try_allocate_in`
  obtain ⟨v, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80011e64_spec hi.pc (by
    rv_eval [hx22]
    and_intros <;> valid_access hsv [hsrc, hk])
  have k₁ := b80011e64_keeps h₁
  have x2₁ : v.getReg .x2 = s.getReg .x2 - 112 := (k₁ .x2 (by decide)).trans hi.sp
  have x10₁ : v.getReg .x10 = s.getReg .x2 - 104 := by rw [b80011e64_x10 h₁, hi.sp]; rv_eval []
  have x11₁ : v.getReg .x11 = vecLen s (src s k) := by
    rw [b80011e64_x11 h₁, hx22, ← hlen]; rfl
  have x18₁ : v.getReg .x18 = vecLen s (src s k) := by
    rw [b80011e64_x18 h₁, hx22, ← hlen]; rfl
  have x19₁ : v.getReg .x19 = vecPtr s (src s k) := by
    rw [b80011e64_x19 h₁, hx22, ← hptr, vecPtr, src]; congr 1; rv_eval []
  have hm₁ := b80011e64_mem_same h₁
  have hnext₁ : heapNext v = heapNext u := by simp only [heapNext, hm₁]
  have hheap₁ : HeapOk v := ⟨hnext₁ ▸ hi.heap.lo, hnext₁ ▸ hi.heap.hi⟩
  have hta : TryAllocPre .x13 .x14 v := {
    heap := hheap₁
    out := by rw [x10₁]; valid_sub hst.valid [N.sp]
    align := by rw [b80011e64_x13 h₁]; decide
    size := by rw [b80011e64_x14 h₁]; decide
    stack := hst.inner (k := 112) x2₁ (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by
      rw [x10₁]
      have := hheap₁.hi
      simp only [Outside, heapNext, heapEnd] at this ⊢
      exact ⟨Or.inr (by addr_omega [N.sp]), by addr_omega [N.sp, hnx]⟩
    outStack := by rw [x10₁]; addr_omega [N.sp, x2₁] }
  obtain ⟨w, hr₂, ⟨hpc₂, hpres₂, hpost, -⟩ | hdead⟩ := hT.call hr₁ (b80011e64_pc h₁) hta
  swap
  · exact ⟨w, hr₂, Or.inr hdead⟩
  have hwf := hpost.frame.dframe
  rw [x10₁, show stackLo v tryAllocStack = s.getReg .x2 - 160 by
    simp only [stackLo, x2₁, tryAllocStack]; rv_eval []] at hwf
  have x2₂ : w.getReg .x2 = s.getReg .x2 - 112 := (hpres₂.reg .x2).trans x2₁
  -- the error check
  obtain ⟨w₂, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80011e88_spec
    (by rw [hpc₂, returnAddress_eq, b80011e64_x1 h₁]; decide) (by
      rv_eval [x2₂]
      valid_access hst.valid [N.sp])
  have hok₂ := hpost.ok
  rw [x10₁] at hok₂
  by_cases htag : w.getMem (s.getReg .x2 - 104) = 0
  swap
  · exact ⟨w₂, hr₂.trans hr₃, Or.inr (dead_of_fetch (by
      rw [b80011e88_pc_taken h₃ (by rw [x2₂]; rv_eval []; exact htag)]; exact trap))⟩
  obtain ⟨hcap₂, hnew₂⟩ := hok₂ htag
  rw [x11₁, b80011e64_x14 h₁, b80011e64_x13 h₁] at hnew₂
  rw [x11₁] at hcap₂
  have k₃ := b80011e88_keeps h₃
  have hm₃ := b80011e88_mem_same h₃
  obtain ⟨w₃, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80011e90_spec
    (b80011e88_pc_not_taken h₃ (by rw [x2₂]; rv_eval []; exact htag)) (by
      rv_eval [k₃ .x2 (by decide), x2₂]
      and_intros <;> valid_access hst.valid [N.sp])
  have k₄ := b80011e90_keeps h₄
  have hm₄ := b80011e90_mem_same h₄
  obtain ⟨p, hp⟩ : ∃ p, p = w.getMem (s.getReg .x2 - 88) := ⟨_, rfl⟩
  have x20₄ : w₃.getReg .x20 = p := by
    rw [b80011e90_x20 h₄, k₃ .x2 (by decide), x2₂, hm₃, hp]; rv_eval []
  have x24₄ : w₃.getReg .x24 = vecLen s (src s k) := by
    rw [b80011e90_x24 h₄, k₃ .x2 (by decide), x2₂, hm₃, ← hcap₂]; rv_eval []
  have x18₂ : w₂.getReg .x18 = vecLen s (src s k) := by
    rw [k₃ .x18 (by decide), hpres₂.reg .x18, x18₁]
  have x18₄ : w₃.getReg .x18 = vecLen s (src s k) := by rw [k₄ .x18 (by decide), x18₂]
  have hnewp : NewBuf v w p ((vecLen s (src s k)).toNat * 48) 8 := by
    rw [hp]; simpa only [show s.getReg .x2 - 104 + 16 = s.getReg .x2 - 88 by rv_eval [],
      show (48 : Word).toNat = 48 from rfl, show (8 : Word).toNat = 8 from rfl] using hnew₂
  have hnext₄ : heapNext w₃ = heapNext w := by simp only [heapNext, hm₄, hm₃]
  -- the frame so far
  have hf₄ : DFrame u w₃ fun x ↦ Within x (s.getReg .x2 - 160) 80 ∨ Within x nextAddr 8 ∨
      Fresh u w₃ x :=
    (((DFrame.of_same hm₁ fun _ ↦ False).union hwf).union
      ((DFrame.of_same hm₃ fun _ ↦ False).union (DFrame.of_same hm₄ fun _ ↦ False))).mono
      fun x h ↦ by
        rcases h with (h | h | h | h | h) | h | h
        · exact h.elim
        · exact Or.inl (by addr_omega [h, N.sp])
        · exact Or.inl (by addr_omega [h, N.sp])
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (by simpa only [Fresh, hnext₁, hnext₄] using h))
        · exact h.elim
        · exact h.elim
  have hregs₄ : ∀ q ∈ [Reg.x2, .x8, .x9, .x21, .x22, .x23, .x25, .x26, .x27],
      w₃.getReg q = u.getReg q := fun q hq ↦ by
    rw [k₄ q (mem_of_mem hq _), k₃ q (mem_of_mem hq _), hpres₂ q (mem_of_mem hq _),
      k₁ q (mem_of_mem hq _)]
  have hheap₄ : HeapOk w₃ := ⟨hnext₄ ▸ hpost.heap.lo, hnext₄ ▸ hpost.heap.hi⟩
  have hmono₄ : heapNext u ≤ heapNext w₃ := by rw [hnext₄, ← hnext₁]; exact hpost.mono
  by_cases hz : vecLen s (src s k) = 0
  · -- nothing to copy
    refine ⟨w₃, hr₂.trans (hr₃.trans hr₄), Or.inl ⟨p, b80011e90_pc_taken h₄
      (by rw [x18₂, hz]), hregs₄, x24₄, x20₄, x18₄, hheap₄, hmono₄, ?_, ?_, hf₄⟩⟩
    · simp only [NewBuf, hnext₁.symm, hnext₄] at hnewp ⊢; exact hnewp
    · intro k' _ hk'; rw [hz] at hk'; simp at hk'
  -- the copy
  have hlz : 0 < (vecLen s (src s k)).toNat := by
    rcases Nat.eq_zero_or_pos (vecLen s (src s k)).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq h) hz
    · exact h
  have hnp := hnewp
  simp only [NewBuf] at hnp
  have hp8 := hnp.1
  have hpb : heapNext v ≤ p.toNat ∧ p.toNat + (vecLen s (src s k)).toNat * 48 ≤ heapNext w := by
    rcases hnp.2 with h | h
    · exfalso; rw [Nat.mul_eq_zero] at h; omega
    · exact h
  have hwhi := hpost.heap.hi
  have hslen := hok.vec.len
  have hsraw := hok.vec.raw
  simp only [RawVecOk, Buf] at hsraw
  rw [hlen] at hslen
  rw [hptr] at hsraw
  have hsb : heapStart ≤ (vecPtr s (src s k)).toNat ∧ (vecPtr s (src s k)).toNat +
      (vecCap u (src s k)).toNat * 48 ≤ heapNext u := by
    rcases hsraw.2 with h | h
    · exfalso; rw [Nat.mul_eq_zero] at h; omega
    · exact h
  have hnext₁' := hnext₁
  simp only [heapNext, heapStart, heapEnd] at hpb hwhi hsb hnext₁
  obtain ⟨w₄, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80011e9c_spec
    (b80011e90_pc_not_taken h₄ (by rw [x18₂]; exact hz)) trivial
  have k₅ := b80011e9c_keeps h₅
  have hm₅ := b80011e9c_mem_same h₅
  have x12₅ : (w₄.getReg .x12).toNat = 48 * (vecLen s (src s k)).toNat := by
    rw [b80011e9c_x12 h₅, x18₄]
    rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_mul]
    simp only [show (32 : Word).toNat = 32 from rfl, show (16 : Word).toNat = 16 from rfl]
    omega
  have x10₅ : w₄.getReg .x10 = p := by rw [b80011e9c_x10 h₅, x20₄]
  have x11₅ : w₄.getReg .x11 = vecPtr s (src s k) := by
    rw [b80011e9c_x11 h₅, k₄ .x19 (by decide), k₃ .x19 (by decide), hpres₂.reg .x19, x19₁]
  have x2₅ : w₄.getReg .x2 = s.getReg .x2 - 112 := by
    rw [k₅ .x2 (by decide), hregs₄ .x2 (by decide), hi.sp]
  have hmc : MemcpyPre w₄ := {
    dst := by rw [x10₅, x12₅]; simp only [Mapped]; omega
    src := by rw [x11₅, x12₅]; simp only [Mapped]; omega
    apart := by rw [x10₅, x11₅, x12₅]; simp only [Apart]; omega
    stack := (hst.inner (k := 112) x2₅ (by decide) (by decide) (by decide) (by decide)
      (by decide)).toStackOk
    dstStack := by rw [x10₅, x12₅]; addr_omega [hpb, hwhi, x2₅, N.sp]
    srcStack := by rw [x11₅, x12₅]; addr_omega [hsb, hnext₁, hwhi, x2₅, N.sp, hpb] }
  obtain ⟨mc, hr₆, ⟨hpc₆, hpres₆, hmpost⟩ | hdead⟩ := hM.call hr₅ (b80011e9c_pc h₅) hmc
  swap
  · exact ⟨mc, hr₂.trans (hr₃.trans (hr₄.trans hr₆)), Or.inr hdead⟩
  obtain ⟨y, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80011eb8_spec
    (by rw [hpc₆, returnAddress_eq, b80011e9c_x1 h₅]; decide) trivial
  have k₇ := b80011eb8_keeps h₇
  have hm₇ := b80011eb8_mem_same h₇
  have hmf := hmpost.frame.dframe
  rw [x10₅, x12₅, show stackLo w₄ memcpyStack = s.getReg .x2 - 128 by
    simp only [stackLo, x2₅, memcpyStack]; rv_eval []] at hmf
  have hny : heapNext y = heapNext w := by
    simp only [heapNext, hm₇]
    rw [hmf.getMem_of (fun x hx h ↦ by
      rcases h with h | h
      · addr_omega [hx, h, hpb, hwhi]
      · addr_omega [hx, h, N.sp, hnx]) (by decide), hm₅, hm₄, hm₃]
  refine ⟨y, hr₂.trans (hr₃.trans (hr₄.trans (hr₆.trans hr₇))), Or.inl ⟨p, b80011eb8_pc h₇,
    fun q hq ↦ ?_, ?_, ?_, ?_, ⟨hny ▸ hpost.heap.lo, hny ▸ hpost.heap.hi⟩, ?_, ?_, ?_, ?_⟩⟩
  · rw [k₇ q (mem_of_mem hq _), hpres₆ q (mem_of_mem hq _), k₅ q (mem_of_mem hq _), hregs₄ q hq]
  · rw [k₇ .x24 (by decide), hpres₆.reg .x24, k₅ .x24 (by decide), x24₄]
  · rw [k₇ .x20 (by decide), hpres₆.reg .x20, k₅ .x20 (by decide), x20₄]
  · rw [k₇ .x18 (by decide), hpres₆.reg .x18, k₅ .x18 (by decide), x18₄]
  · rw [hny, ← hnext₁']; exact hpost.mono
  · have h' := hnewp
    simp only [NewBuf, hny] at h' ⊢
    rw [hnext₁'] at h'
    exact h'
  · intro k' hk8 hk'
    have hb := hmpost.bytes
    rw [x10₅, x11₅, x12₅] at hb
    have hcs := (hpre.srcOk k hk).vec.len
    have hcs' : (vecLen s (src s k)).toNat ≤ (vecCap s (src s k)).toNat := hcs
    have hsk' : s.getMem (vecPtr s (src s k) + BitVec.ofNat 64 k') =
        u.getMem (vecPtr s (src s k) + BitVec.ofNat 64 k') := by
      have hhi := hi.heap.hi
      simp only [heapNext, heapEnd] at hhi
      have hfr := (ctx.frame.union hi.frame).getMem_of
        (a := vecPtr s (src s k) + BitVec.ofNat 64 k')
        (fun x hx h ↦ srcApart hpre ctx hn (Nat.le_of_lt hk) hhi (Or.inr ⟨k, hk, by
          show formBuf s (src s k) x
          simp only [formBuf]; addr_omega [hx, hcs', hk', hsb, hslen]⟩) h)
        (by addr_omega [hsb, hslen, hk'])
      exact hfr.symm
    rw [hm₇, getMem_eq_of_bytesAt hb hp8 hsraw.1 hk8 hk', hm₅, hm₄, hm₃, hsk']
    rw [hwf.getMem_of (fun x hx h ↦ by
      rcases h with h | h | h | h
      · addr_omega [hx, h, hsb, hslen, hk', N.sp, hwhi, hpb, hnext₁]
      · addr_omega [hx, h, hsb, hslen, hk', N.sp, hwhi, hpb, hnext₁]
      · addr_omega [hx, h, hsb, hslen, hk', hwhi, hpb, hnext₁]
      · simp only [Fresh, heapNext] at h; addr_omega [hx, h, hsb, hslen, hk', hnext₁])
      (by addr_omega [hsb, hslen, hk']), hm₁]
  · refine ((((hf₄.union (DFrame.of_same hm₅ fun _ ↦ False)).union hmf).union
      (DFrame.of_same hm₇ fun _ ↦ False))).mono fun x h ↦ ?_
    rcases h with (((h | h | h) | h) | h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr ?_)
      simp only [Fresh] at h ⊢
      rw [hny, ← hnext₄]; exact h
    · exact h.elim
    · refine Or.inr (Or.inr ?_)
      simp only [Fresh]
      rw [hny]
      simp only [heapNext]
      addr_omega [h, hpb, hnext₁]
    · exact Or.inl (by addr_omega [h, N.sp])
    · exact h.elim

/-- The loop is over: at the epilogue, or at a dead end. -/
def Done (s t₁ r u : MachineState) : Prop := AtExit s t₁ r u ∨ Dead Image.code u

/-- One iteration: form `k` cloned into its slot. -/
theorem body (hT : TryAllocZeroedSpec) (hM : MemcpySpec 0x800126e4) {s t₁ r : MachineState}
    (hpre : SpecExtendPre s) (ctx : Ctx s t₁ r) (u : MachineState) (hu : ∃ k, Inv s t₁ r u k) :
    (∃ z, Reaches Image.code u z ∧ Done s t₁ r z) ∨
      (∃ z, Reaches Image.code u z ∧ (∃ k, Inv s t₁ r z k) ∧
        (z.getReg .x9).toNat < (u.getReg .x9).toNat) := by
  obtain ⟨k, hi⟩ := hu
  obtain ⟨y, hry, ⟨p, hc⟩ | hdead⟩ := cloneStep hT hM hpre ctx hi
  swap
  · exact Or.inl ⟨y, hry, Or.inr hdead⟩
  have hk := hi.lt
  have hn : 0 < nOf s := by omega
  have N := nums hpre ctx hn
  have hcnt := cntOf_toNat hpre
  have hsrc := N.src
  have hbuf := N.buf
  have hcap := N.cap
  have hnext := N.next
  have hcapl := (vecCap r (s.getReg .x10)).isLt
  simp only [heapNext] at hbuf hnext
  have hx23 : y.getReg .x23 = slot s r k + 8 := (hc.regs .x23 (by decide)).trans hi.x23
  have hPv : ValidMemRange (vecPtr r (s.getReg .x10)) (3 * (vecCap r (s.getReg .x10)).toNat) :=
    validMemRange_of N.ptr (Or.inl ⟨by omega, by omega⟩)
  obtain ⟨z, hrz, h⟩ := Sym.BlockSpec.reaches b80011e44_spec hc.pc (by
    rv_eval [hx23, slot]
    and_intros <;> valid_access hPv [hbuf, hcap, hk, hnext, hcapl])
  have k₂ := b80011e44_keeps h
  have hslb : (slot s r k).toNat = (vecPtr r (s.getReg .x10)).toNat + 24 * (lenOf s + k) := by
    simp only [slot]; addr_omega [hbuf, hcap, hk, hnext, hcapl]
  have hmf := b80011e44_frame h (by rw [hx23]; addr_omega [hslb, hbuf, hcap, hk, hnext])
  rw [hx23, show slot s r k + 8 - 8 = slot s r k by rv_eval []] at hmf
  have w0 := b80011e44_m_x23_n8 h
  have w8 := b80011e44_m_x23_0 h
  have w16 := b80011e44_m_x23_8 h
  rw [hx23, show slot s r k + 8 - 8 = slot s r k by rv_eval [], hc.x24] at w0
  rw [hx23, hc.x20] at w8
  rw [hx23, show slot s r k + 8 + 8 = slot s r k + 16 by rv_eval [], hc.x18] at w16
  have hfz : DFrame u z fun x ↦ (Within x (s.getReg .x2 - 160) 80 ∨ Within x nextAddr 8 ∨
      Fresh u y x) ∨ Within x (slot s r k) 24 := hc.frame.union hmf.dframe
  have hnu := hi.mono
  have hny := hc.mono
  have hyhi := hc.heap.hi
  simp only [heapNext, heapEnd] at hnu hny hyhi
  have hnz : z.getMem nextAddr = y.getMem nextAddr :=
    hmf nextAddr (by addr_omega [hslb, hbuf, hcap, hk, hnext])
  have hnextz : heapNext z = heapNext y := by simp only [heapNext, hnz]
  have hfr := hc.fresh
  simp only [NewBuf, heapNext] at hfr
  -- what `W` misses
  have hW : ∀ x : Word, x.toNat < heapNext u → ¬ Within x (slot s r k) 24 →
      ¬ ((Within x (s.getReg .x2 - 160) 80 ∨ Within x nextAddr 8 ∨ Fresh u y x) ∨
        Within x (slot s r k) 24) := by
    intro x h1 h2 h3
    simp only [heapNext] at h1
    rcases h3 with (h3 | h3 | h3) | h3
    · addr_omega [h1, h3, N.sp, hyhi, hny]
    · addr_omega [h1, h3, hyhi, hny]
    · simp only [Fresh, heapNext] at h3; omega
    · exact h2 h3
  -- the clone
  have hcl := clone_form (u := s) (src := src s k) (e := slot s r k) (p := p) (hpre.srcOk k hk) hpre.heap w0 w8 w16
    (by
      simp only [NewBuf, heapNext, hnz]
      have := ctx.mono
      simp only [heapNext] at this
      rcases hfr.2 with h0 | h0
      · exact ⟨hfr.1, Or.inl h0⟩
      · exact ⟨hfr.1, Or.inr ⟨by omega, h0.2⟩⟩)
    (fun k' hk8 hk' ↦ by
      rw [hmf (p + BitVec.ofNat 64 k') (by
        rcases hfr.2 with h0 | h0
        · rw [Nat.mul_eq_zero] at h0; omega
        · addr_omega [h0, hk', hslb, hbuf, hcap, hk, hnext, hnu, hyhi])]
      exact hc.copy k' hk8 hk')
  have hcore : Core s t₁ r z (k + 1) := {
    heap := ⟨hnextz ▸ hc.heap.lo, hnextz ▸ hc.heap.hi⟩
    mono := by rw [hnextz]; exact hi.mono.trans hc.mono
    saved := fun a h1 h2 ↦ by
      have hnx := hpre.stack.next
      simp only [specExtendStack, reserveStack, stackLo] at hnx
      rw [hfz.getMem_of (a := a) (fun x hx h ↦ by
        rcases h with (h | h | h) | h
        · addr_omega [hx, h, h1, h2, N.sp]
        · addr_omega [hx, h, h1, h2, N.sp, hnx]
        · simp only [Fresh, heapNext] at h; addr_omega [hx, h, h1, h2, N.sp, hyhi]
        · addr_omega [hx, h, h1, h2, N.sp, hslb, hbuf, hnext, hcap, hk]) (by addr_omega [h2, N.sp])]
      exact hi.saved a h1 h2
    frame := (hi.frame.union hfz).mono fun x h ↦ by
      rcases h with (h | h | h | h) | ((h | h | h) | h)
      · exact Or.inl (by addr_omega [h])
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · refine Or.inr (Or.inr (Or.inr ?_))
        simp only [Fresh, hnextz] at h ⊢; simp only [heapNext] at h ⊢; omega
      · exact Or.inr (Or.inl (by addr_omega [h, N.sp]))
      · exact Or.inr (Or.inr (Or.inl h))
      · refine Or.inr (Or.inr (Or.inr ?_))
        simp only [Fresh, hnextz] at h ⊢; simp only [heapNext] at h ⊢; omega
      · refine Or.inl ?_
        have hs0 : (slot s r 0).toNat = (vecPtr r (s.getReg .x10)).toNat + 24 * lenOf s := by
          simp only [slot]; addr_omega [hbuf, hcap, hk, hnext, hcapl]
        addr_omega [h, hs0, hslb]
    new := fun j hj ↦ by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · obtain ⟨hv, hok, hb⟩ := hi.new j hj
        have hsj : (slot s r j).toNat = (vecPtr r (s.getReg .x10)).toNat + 24 * (lenOf s + j) := by
          simp only [slot]; addr_omega [hbuf, hcap, hk, hnext, hcapl, hj]
        have hhd : ∀ x, Within x (slot s r j) 24 → ¬ ((Within x (s.getReg .x2 - 160) 80 ∨
            Within x nextAddr 8 ∨ Fresh u y x) ∨ Within x (slot s r k) 24) := fun x hx ↦
          hW x (by simp only [heapNext]; addr_omega [hx, hsj, hbuf, hcap, hk, hnext, hnu, hj])
            (by addr_omega [hx, hsj, hslb, hj])
        have hbd : ∀ x, formBuf u (slot s r j) x → ¬ ((Within x (s.getReg .x2 - 160) 80 ∨
            Within x nextAddr 8 ∨ Fresh u y x) ∨ Within x (slot s r k) 24) := fun x hx ↦ by
          have h' := hb x hx
          simp only [Fresh, heapNext] at h'
          exact hW x (by simp only [heapNext]; omega)
            (by addr_omega [h', hslb, hbuf, hcap, hk, hnext])
        have hfo := formOf_frame hfz hok hhd hbd (by addr_omega [hsj, hbuf, hcap, hk, hnext, hj])
          hi.heap (by rw [hnextz]; exact hc.mono)
        refine ⟨hfo.1.trans hv, hfo.2, fun x hx ↦ ?_⟩
        rw [formBuf_frame hfz hhd (by addr_omega [hsj, hbuf, hcap, hk, hnext, hj])] at hx
        have h' := hb x hx
        simp only [Fresh, hnextz] at h' ⊢
        simp only [heapNext] at h' ⊢
        omega
      · refine ⟨hcl.1, hcl.2.1, fun x hx ↦ ?_⟩
        simp only [formBuf, vecPtr, vecCap, w0, w8] at hx
        simp only [Fresh, hnextz]
        simp only [heapNext]
        have := ctx.mono
        simp only [heapNext] at this
        rcases hfr.2 with h0 | h0
        · rw [Nat.mul_eq_zero] at h0; simp only [Within] at hx; omega
        · simp only [Within] at hx; omega }
  have x9y : y.getReg .x9 = cntOf s - BitVec.ofNat 64 k := (hc.regs .x9 (by decide)).trans hi.x9
  have hz2 : z.getReg .x2 = s.getReg .x2 - 112 := by
    rw [k₂ .x2 (by decide), hc.regs .x2 (by decide), hi.sp]
  have hz8 : z.getReg .x8 = s.getReg .x10 := by
    rw [k₂ .x8 (by decide), hc.regs .x8 (by decide), hi.x8]
  have hz21 : z.getReg .x21 = vecLen s (s.getReg .x10) + BitVec.ofNat 64 (k + 1) := by
    rw [b80011e44_x21 h, hc.regs .x21 (by decide), hi.x21]
    have := (vecLen s (s.getReg .x10)).isLt
    simp only [lenOf] at hcap
    addr_omega [hcap, hk, hcapl]
  have hzk : ∀ q ∈ [Reg.x25, .x26, .x27], z.getReg q = s.getReg q := fun q hq ↦ by
    rw [k₂ q (mem_of_mem hq _), hc.regs q (mem_of_mem hq _), hi.kept q hq]
  have hx9n : (cntOf s - BitVec.ofNat 64 k).toNat = nOf s - k := by addr_omega [hcnt, hk]
  by_cases hlast : k + 1 = nOf s
  · refine Or.inl ⟨z, hry.trans hrz, Or.inl ⟨hlast ▸ hcore, b80011e44_pc_taken h (by
      rw [x9y]; addr_omega [hcnt, hk, hlast]), hz2, hz8, hlast ▸ hz21, hzk⟩⟩
  · have hk1 : k + 1 < nOf s := by omega
    refine Or.inr ⟨z, hry.trans hrz, ⟨k + 1, { hcore with
      lt := hk1
      pc := b80011e44_pc_not_taken h (by rw [x9y]; addr_omega [hcnt, hk, hk1])
      sp := hz2
      x8 := hz8
      x9 := by rw [b80011e44_x9 h, x9y]; addr_omega [hcnt, hk, hk1]
      x21 := hz21
      x22 := by
        rw [b80011e44_x22 h, hc.regs .x22 (by decide), hi.x22]
        simp only [src]; addr_omega [hsrc, hk1]
      x23 := by
        rw [b80011e44_x23 h, hx23]
        simp only [slot]; addr_omega [hbuf, hcap, hk1, hnext, hcapl]
      kept := hzk }⟩, ?_⟩
    rw [b80011e44_x9 h, x9y, hi.x9]
    addr_omega [hcnt, hk, hk1]

/-- The epilogue: the new length written, the registers restored. -/
theorem exit {s t₁ r u : MachineState} (hpre : SpecExtendPre s) (ctx : Ctx s t₁ r)
    (he : AtExit s t₁ r u) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧ SpecExtendPost s t := by
  have hb := hpre.bounds'
  have hst := hpre.stack
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  have hnx := hst.next
  have hab := hst.above
  simp only [specExtendStack, reserveStack, stackLo, heapEnd] at hss hnx hab
  simp only [Outside, heapNext, heapEnd] at hsf
  obtain ⟨t, hrt, h⟩ := Sym.BlockSpec.reaches b80011ebc_spec he.pc (by
    rv_eval [he.sp, he.x8]
    and_intros <;> first
      | valid_access hst.valid [hb]
      | valid_access hpre.self [hb]
      | addr_omega [hb, hss])
  have k := b80011ebc_keeps h
  have hmf := b80011ebc_frame h (by rw [he.x8]; addr_omega [hb])
  rw [he.x8] at hmf
  have hlen := b80011ebc_m_x8_16 h
  rw [he.x8, he.x21] at hlen
  have hsv (a : Word) (h1 : (s.getReg .x2).toNat - 80 ≤ a.toNat)
      (h2 : a.toNat + 8 ≤ (s.getReg .x2).toNat) : u.getMem a = t₁.getMem a := he.saved a h1 h2
  have pc := b80011ebc_pc h
  have r₁ := b80011ebc_x1 h
  have r₂ := b80011ebc_x2 h
  have r₈ := b80011ebc_x8 h
  have r₉ := b80011ebc_x9 h
  have r₁₈ := b80011ebc_x18 h
  have r₁₉ := b80011ebc_x19 h
  have r₂₀ := b80011ebc_x20 h
  have r₂₁ := b80011ebc_x21 h
  have r₂₂ := b80011ebc_x22 h
  have r₂₃ := b80011ebc_x23 h
  have r₂₄ := b80011ebc_x24 h
  rw [he.sp] at pc r₁ r₂ r₈ r₉ r₁₈ r₁₉ r₂₀ r₂₁ r₂₂ r₂₃ r₂₄
  rv_eval [] at pc r₁ r₂ r₈ r₉ r₁₈ r₁₉ r₂₀ r₂₁ r₂₂ r₂₃ r₂₄
  rw [hsv _ (by addr_omega [hb]) (by addr_omega [hb]), ctx.ra] at pc r₁
  rw [hsv _ (by addr_omega [hb]) (by addr_omega [hb]), ctx.s0] at r₈
  rw [hsv _ (by addr_omega [hb]) (by addr_omega [hb]), ctx.s1] at r₉
  rw [hsv _ (by addr_omega [hb]) (by addr_omega [hb]), ctx.s2] at r₁₈
  rw [hsv _ (by addr_omega [hb]) (by addr_omega [hb]), ctx.s3] at r₁₉
  rw [hsv _ (by addr_omega [hb]) (by addr_omega [hb]), ctx.s4] at r₂₀
  rw [hsv _ (by addr_omega [hb]) (by addr_omega [hb]), ctx.s5] at r₂₁
  rw [hsv _ (by addr_omega [hb]) (by addr_omega [hb]), ctx.s6] at r₂₂
  rw [hsv _ (by addr_omega [hb]) (by addr_omega [hb]), ctx.s7] at r₂₃
  rw [hsv _ (by addr_omega [hb]) (by addr_omega [hb]), ctx.s8] at r₂₄
  refine ⟨t, hrt, pc.trans (returnAddress_eq s).symm, preserves_of r₂ r₈ r₉ r₁₈ r₁₉ fun q hq ↦ ?_,
    ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact r₂₀
    · exact r₂₁
    · exact r₂₂
    · exact r₂₃
    · exact r₂₄
    · rw [k .x25 (by decide), he.kept .x25 (by decide)]
    · rw [k .x26 (by decide), he.kept .x26 (by decide)]
    · rw [k .x27 (by decide), he.kept .x27 (by decide)]
  -- the numbers
  have hraw := ctx.vec.raw
  simp only [RawVecOk, Buf] at hraw
  have hcap := ctx.cap
  have hrhi := ctx.heap.hi
  have hrs := ctx.mono
  have hur := he.mono
  have huhi := he.heap.hi
  have hshi := hpre.heap.hi
  simp only [heapNext, heapEnd] at hrhi hrs hur huhi hshi
  have hsok := hpre.ok
  have hsraw := hsok.vec.raw
  have hslen := hsok.vec.len
  simp only [RawVecOk, Buf] at hsraw
  -- `r`'s buffer: below `NEXT` at `r`, and the old one or one allocated after the entry
  have hP : ∀ x, Within x (vecPtr r (s.getReg .x10)) (24 * (vecCap r (s.getReg .x10)).toNat) →
      x.toNat < heapNext r ∧ (formVecBuf s (s.getReg .x10) x ∨ heapNext s ≤ x.toNat) := by
    intro x hx
    simp only [Within] at hx
    refine ⟨?_, ?_⟩
    · rcases hraw.2 with h0 | h0
      · rw [Nat.mul_eq_zero] at h0; omega
      · omega
    · rcases ctx.fresh with ⟨h1, h2⟩ | h3
      · left; simp only [formVecBuf, Within]; rw [← h1, ← h2]; exact hx
      · right; simp only [NewBuf] at h3
        rcases h3.2 with h0 | h0
        · rw [Nat.mul_eq_zero] at h0; omega
        · omega
  have hPself : ∀ x, Within x (vecPtr r (s.getReg .x10)) (24 * (vecCap r (s.getReg .x10)).toNat) →
      ¬ Within x (s.getReg .x10) 24 := by
    intro x hx hs
    obtain ⟨h1, h2 | h2⟩ := hP x hx
    · exact hpre.header x hs (Or.inl h2)
    · simp only [heapNext] at h1 h2; addr_omega [hs, h1, h2, hsf, hrhi]
  -- the header at `t`: `r`'s capacity and buffer, the new length
  have hself (o : Word) (ho : o = 0 ∨ o = 8) : t.getMem (s.getReg .x10 + o) = r.getMem (s.getReg .x10 + o) := by
    rw [hmf _ (by rcases ho with rfl | rfl <;> addr_omega [hb])]
    refine he.frame.getMem_of (fun x hx h ↦ ?_) (by rcases ho with rfl | rfl <;> addr_omega [hb])
    have hx' : Within x (s.getReg .x10) 24 := by rcases ho with rfl | rfl <;> addr_omega [hx, hb]
    rcases h with h | h | h | h
    · simp only [slot, Nat.add_zero] at h
      exact hPself x (by addr_omega [h, hcap, hraw]) hx'
    · addr_omega [hx', h, hss, hb]
    · addr_omega [hx', h, hsf.2]
    · simp only [Fresh, heapNext] at h; addr_omega [hx', h, hsf.1, hrs, hur, huhi]
  have hC0 : lenOf s + nOf s ≤ (vecCap r (s.getReg .x10)).toNat := hcap
  have hPb : ∀ i, i < (vecCap r (s.getReg .x10)).toNat → (vecPtr r (s.getReg .x10)).toNat + 24 * i + 24 ≤
      heapNext r := by
    intro i hi; rcases hraw.2 with h0 | h0
    · rw [Nat.mul_eq_zero] at h0; omega
    · simp only [heapNext] at h0 ⊢; omega
  simp only [heapNext] at hPb
  -- the old forms' headers, copied by `reserve`
  have hword : ∀ m, m % 8 = 0 → m + 8 ≤ 24 * lenOf s →
      t.getMem (vecPtr r (s.getReg .x10) + BitVec.ofNat 64 m) =
        s.getMem (vecPtr s (s.getReg .x10) + BitVec.ofNat 64 m) := by
    intro m hm hmL
    have hmb := hPb (m / 24) (by omega)
    have hPC := hPb ((vecCap r (s.getReg .x10)).toNat - 1) (by omega)
    rw [← ctx.old m hm hmL, hmf (vecPtr r (s.getReg .x10) + BitVec.ofNat 64 m)
      (fun h' ↦ hPself (vecPtr r (s.getReg .x10) + BitVec.ofNat 64 m)
        (by addr_omega [hmb, hmL, hC0, hrhi, hm, hPC]) (by addr_omega [h', hmb, hmL, hb, hrhi, hm]))]
    refine he.frame.getMem_of (a := vecPtr r (s.getReg .x10) + BitVec.ofNat 64 m)
      (fun x hx h ↦ ?_) (by addr_omega [hmb, hmL, hrhi, hm])
    rcases h with h | h | h | h
    · simp only [slot, Nat.add_zero] at h; addr_omega [hx, h, hmb, hmL, hrhi, hC0, hPC, hm]
    · addr_omega [hx, h, hmb, hb, hrhi, hmL, hab, hm]
    · addr_omega [hx, h, hmb, hrhi, hmL, hm]
    · simp only [Fresh, heapNext] at h; addr_omega [hx, h, hmb, hmL, hrhi, hm]
  have hf := (ctx.frame.union he.frame).union hmf.dframe
  have hmono : heapNext s ≤ heapNext t := by
    have : heapNext t = heapNext u := by
      simp only [heapNext]; rw [hmf _ (by addr_omega [hsf.2, hb])]
    rw [this]; simp only [heapNext]; omega
  have hold : ∀ i < lenOf s, formOf t (vecPtr r (s.getReg .x10) + BitVec.ofNat 64 (24 * i)) =
      formOf s (vecPtr s (s.getReg .x10) + BitVec.ofNat 64 (24 * i)) ∧
      FormOk t (vecPtr r (s.getReg .x10) + BitVec.ofNat 64 (24 * i)) ∧
      formBuf t (vecPtr r (s.getReg .x10) + BitVec.ofNat 64 (24 * i)) =
        formBuf s (vecPtr s (s.getReg .x10) + BitVec.ofNat 64 (24 * i)) := by
    intro i hi
    have g (m : Nat) (hm : m < 3) : t.getMem (vecPtr r (s.getReg .x10) + BitVec.ofNat 64 (24 * i) +
        BitVec.ofNat 64 (8 * m)) = s.getMem (vecPtr s (s.getReg .x10) + BitVec.ofNat 64 (24 * i) +
        BitVec.ofNat 64 (8 * m)) := by
      rw [add_ofNat_add, add_ofNat_add]; exact hword _ (by omega) (by omega)
    refine formOf_move hf (hsok.forms i hi) (by simpa using g 0 (by decide))
      (g 1 (by decide)) (g 2 (by decide)) (fun x hx h ↦ ?_) hpre.heap hmono
    have hbl := formBuf_below (hsok.forms i hi) hx
    have hsep := hsok.sep x ⟨i, hi, hx⟩
    have hhd := hpre.header x
    simp only [heapNext, heapStart] at hbl
    rcases h with ((h | h | h | h) | (h | h | h | h)) | h
    · exact hhd h (Or.inr ⟨i, hi, hx⟩)
    · addr_omega [hbl, h, hb, hab, hshi]
    · addr_omega [hbl, h, hshi]
    · simp only [Fresh, heapNext] at h; omega
    · simp only [slot, Nat.add_zero] at h
      simp only [heapNext] at hraw
      obtain ⟨-, h2 | h2⟩ := hP x (by addr_omega [h, hC0, hraw, hrhi])
      · exact hsep h2
      · simp only [heapNext] at h2; omega
    · addr_omega [hbl, h, hb, hshi]
    · addr_omega [hbl, h, hshi]
    · simp only [Fresh, heapNext] at h; omega
    · exact hhd (by addr_omega [h, hb]) (Or.inr ⟨i, hi, hx⟩)
  have hnew' : ∀ j < nOf s, formOf t (slot s r j) = formOf s (src s j) ∧ FormOk t (slot s r j) ∧
      ∀ x, formBuf t (slot s r j) x → Fresh r t x := by
    intro j hj
    obtain ⟨hv, hok, hbf⟩ := he.new j hj
    have hsj := hPb (lenOf s + j) (by omega)
    have hjs : (slot s r j).toNat = (vecPtr r (s.getReg .x10)).toNat + 24 * (lenOf s + j) := by
      simp only [slot]; addr_omega [hsj]
    have hhd : ∀ x, Within x (slot s r j) 24 → ¬ Within x (s.getReg .x10 + 16) 8 := fun x hx h' ↦
      hPself x (by addr_omega [hx, hjs, hsj, hj, hC0]) (by addr_omega [h', hb])
    have hbd : ∀ x, formBuf u (slot s r j) x → ¬ Within x (s.getReg .x10 + 16) 8 := fun x hx h' ↦ by
      have := hbf x hx
      simp only [Fresh, heapNext] at this
      addr_omega [this, h', hsf.1, hrs, huhi, hb]
    have hfo := formOf_frame hmf.dframe hok hhd hbd (by addr_omega [hjs, hsj]) he.heap
      (by simp only [heapNext]; rw [hmf _ (by addr_omega [hsf.2, hb])])
    refine ⟨hfo.1.trans hv, hfo.2, fun x hx ↦ ?_⟩
    rw [formBuf_frame hmf.dframe hhd (by addr_omega [hjs, hsj])] at hx
    have := hbf x hx
    simp only [Fresh] at this ⊢
    constructor
    · simp only [heapNext] at this ⊢; omega
    · have : heapNext t = heapNext u := by
        simp only [heapNext]; rw [hmf _ (by addr_omega [hsf.2, hb])]
      omega
  have hcapl := (vecCap r (s.getReg .x10)).isLt
  have hlenw : (vecLen t (s.getReg .x10)).toNat = lenOf s + nOf s := by
    have hL : lenOf s = (s.getMem (s.getReg .x10 + 16)).toNat := rfl
    simp only [vecLen]; rw [hlen]; simp only [vecLen]; addr_omega [hC0, hcapl, hL]
  have hptrw : vecPtr t (s.getReg .x10) = vecPtr r (s.getReg .x10) := hself 8 (Or.inr rfl)
  have hcapw : vecCap t (s.getReg .x10) = vecCap r (s.getReg .x10) := by
    simpa [vecCap] using hself 0 (Or.inl rfl)
  have hnt : heapNext t = heapNext u := by
    simp only [heapNext]; rw [hmf _ (by addr_omega [hsf.2, hb])]
  -- a form of the result: an old one or a clone
  have hcases : ∀ i < lenOf s + nOf s,
      (i < lenOf s ∧ formOf t (vecPtr r (s.getReg .x10) + BitVec.ofNat 64 (24 * i)) =
        formOf s (vecPtr s (s.getReg .x10) + BitVec.ofNat 64 (24 * i)) ∧
        FormOk t (vecPtr r (s.getReg .x10) + BitVec.ofNat 64 (24 * i)) ∧
        formBuf t (vecPtr r (s.getReg .x10) + BitVec.ofNat 64 (24 * i)) =
          formBuf s (vecPtr s (s.getReg .x10) + BitVec.ofNat 64 (24 * i))) ∨
      (FormOk t (vecPtr r (s.getReg .x10) + BitVec.ofNat 64 (24 * i)) ∧
        ∀ x, formBuf t (vecPtr r (s.getReg .x10) + BitVec.ofNat 64 (24 * i)) x → Fresh r t x) := by
    intro i hi
    rcases Nat.lt_or_ge i (lenOf s) with h | h
    · exact Or.inl ⟨h, hold i h⟩
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
      exact Or.inr ⟨(hnew' j (by omega)).2.1, (hnew' j (by omega)).2.2⟩
  have hnt' := hnt
  simp only [heapNext] at hnt'
  refine ⟨⟨by simp only [heapNext, hnt']; have := he.heap.lo; simpa [heapNext] using this,
    by simp only [heapNext, hnt']; exact huhi⟩, hmono, ?_, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · -- the value
    simp only [formVecOf, formsAt, hptrw, hlenw, List.range_add, List.map_append, List.map_map]
    congr 1
    · apply List.map_congr_left
      intro i hi
      exact (hold i (List.mem_range.mp hi)).1
    · apply List.map_congr_left
      intro j hj
      exact (hnew' j (List.mem_range.mp hj)).1
  · simp only [RawVecOk, Buf, hptrw, hcapw]
    refine ⟨hraw.1, hraw.2.imp id fun h' ↦ ⟨h'.1, ?_⟩⟩
    have := h'.2; simp only [heapNext] at this ⊢; omega
  · rw [hlenw, hcapw]; exact hC0
  · intro i hi
    rw [hlenw] at hi
    rw [hptrw]
    rcases hcases i hi with ⟨-, -, h, -⟩ | ⟨h, -⟩ <;> exact h
  · intro x ⟨i, hi, hx⟩ hb'
    rw [hlenw] at hi
    rw [hptrw] at hx
    simp only [formVecBuf, hptrw, hcapw] at hb'
    obtain ⟨hlt, h2⟩ := hP x hb'
    rcases hcases i hi with ⟨hiL, -, -, hbf⟩ | ⟨-, hbf⟩
    · rw [hbf] at hx
      rcases h2 with h2 | h2
      · exact hsok.sep x ⟨i, hiL, hx⟩ h2
      · have := formBuf_below (hsok.forms i hiL) hx; omega
    · have := hbf x hx
      simp only [Fresh] at this
      have hu := he.mono
      omega
  · intro x hx
    rcases hx with hx | ⟨i, hi, hx⟩
    · simp only [formVecBuf, hptrw, hcapw] at hx
      rcases ctx.fresh with ⟨h1, h2⟩ | h3
      · left; left; simp only [formVecBuf]; rw [← h1, ← h2]; exact hx
      · right
        simp only [NewBuf] at h3
        simp only [Fresh, hnt]
        simp only [Within] at hx
        have hu := he.mono
        rcases h3.2 with h0 | h0
        · rw [Nat.mul_eq_zero] at h0; omega
        · omega
    · rw [hlenw] at hi
      rw [hptrw] at hx
      rcases hcases i hi with ⟨hiL, -, -, hbf⟩ | ⟨-, hbf⟩
      · rw [hbf] at hx; exact Or.inl (Or.inr ⟨i, hiL, hx⟩)
      · have := hbf x hx
        have := ctx.mono
        simp only [Fresh] at *
        exact Or.inr ⟨by omega, by omega⟩
  · refine hf.mono fun x h ↦ ?_
    rcases h with ((h | h | h | h) | (h | h | h | h)) | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
      simp only [Fresh] at h ⊢; have hu := he.mono; omega
    · simp only [slot, Nat.add_zero] at h
      simp only [heapNext] at hraw
      obtain ⟨hlt, h2 | h2⟩ := hP x (by addr_omega [h, hC0, hraw, hrhi])
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h2, by
          simp only [heapNext] at hlt ⊢; rw [hnt']; omega⟩)))
    · exact Or.inr (Or.inr (Or.inl (by addr_omega [h, hb])))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
      simp only [Fresh, hnt] at h ⊢; have := ctx.mono; omega
    · exact Or.inl (by addr_omega [h, hb])

/-- **`Vec<Form>::spec_extend` meets its contract**, given `reserve`'s (with where its buffer is),
`try_allocate_in`'s and `memcpy`'s. -/
theorem spec_extend_spec (hR : ReserveFreshSpec) (hT : TryAllocZeroedSpec)
    (hM : MemcpySpec 0x800126e4) : SpecExtendSpec := by
  intro s hpc hpre
  have hb := hpre.bounds'
  obtain ⟨r, hr, ⟨t₁, ctx⟩ | hdead⟩ := setup hR hpc hpre
  swap
  · exact ⟨r, hr, Or.inr hdead⟩
  obtain ⟨r₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80011e1c_spec ctx.pc (by
    rv_eval [ctx.x8]
    valid_access hpre.self [hb])
  have k₂ := b80011e1c_keeps h₂
  have hm₂ := b80011e1c_mem_same h₂
  have x21₂ : r₂.getReg .x21 = vecLen s (s.getReg .x10) := by
    rw [b80011e1c_x21 h₂, ctx.x8, ← ctx.len]; rfl
  have hcore₀ (v : MachineState) (hv : ∀ a, v.getMem a = r.getMem a) : Core s t₁ r v 0 := {
    heap := ⟨by simp only [heapNext, hv]; exact ctx.heap.lo, by simp only [heapNext, hv]; exact ctx.heap.hi⟩
    mono := by simp only [heapNext, hv]; exact Nat.le_refl _
    saved := fun a h1 h2 ↦ (hv a).trans (ctx.saved a h1 h2)
    frame := DFrame.of_same (fun a ↦ hv a) _
    new := fun j hj ↦ absurd hj (Nat.not_lt_zero _) }
  have hfin : ∀ v, Reaches Image.code s v → Done s t₁ r v → ∃ t, Reaches Image.code s t ∧
      ((t.pc = returnAddress s ∧ Preserves s t ∧ SpecExtendPost s t) ∨ Dead Image.code t) := by
    intro v hv hd
    rcases hd with he | hd
    · obtain ⟨t, hvt, hpc', hpres, hpost⟩ := exit hpre ctx he
      exact ⟨t, hv.trans hvt, Or.inl ⟨hpc', hpres, hpost⟩⟩
    · exact ⟨v, hv, Or.inr hd⟩
  have hbd := hpre.bounds
  have hw := hpre.whole
  by_cases he : s.getReg .x12 = s.getReg .x11
  · -- an empty slice
    have hn0 : nOf s = 0 := by simp only [nOf, he]; simp
    refine hfin r₂ (hr.trans hr₂) (Or.inl {
      toCore := hn0 ▸ hcore₀ r₂ hm₂
      pc := b80011e1c_pc_taken h₂ (by rw [ctx.x19, ctx.x18, he])
      sp := (k₂ .x2 (by decide)).trans ctx.sp
      x8 := (k₂ .x8 (by decide)).trans ctx.x8
      x21 := by rw [x21₂, hn0]; simp
      kept := fun q hq ↦ (k₂ q (mem_of_mem hq _)).trans (ctx.kept q (mem_of_mem hq _)) })
  -- the loop
  have hn : 0 < nOf s := by
    have : (s.getReg .x12).toNat ≠ (s.getReg .x11).toNat := fun h ↦ he (BitVec.eq_of_toNat_eq h)
    simp only [nOf]; omega
  have N := nums hpre ctx hn
  have hbuf := N.buf
  have hcap := N.cap
  have hnext := N.next
  have hcapl := (vecCap r (s.getReg .x10)).isLt
  have hL : lenOf s = (vecLen s (s.getReg .x10)).toNat := rfl
  simp only [heapNext] at hbuf hnext
  obtain ⟨r₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80011e24_spec
    (b80011e1c_pc_not_taken h₂ (by rw [ctx.x19, ctx.x18]; exact he)) (by
      rv_eval [k₂ .x8 (by decide), ctx.x8]
      valid_access hpre.self [hb])
  have k₃ := b80011e24_keeps h₃
  have hm₃ := b80011e24_mem_same h₃
  have inv₀ : Inv s t₁ r r₃ 0 := {
    toCore := hcore₀ r₃ fun a ↦ (hm₃ a).trans (hm₂ a)
    lt := hn
    pc := b80011e24_pc h₃
    sp := by rw [k₃ .x2 (by decide), k₂ .x2 (by decide), ctx.sp]
    x8 := by rw [k₃ .x8 (by decide), k₂ .x8 (by decide), ctx.x8]
    x9 := by rw [k₃ .x9 (by decide), k₂ .x9 (by decide), ctx.x9]; simp
    x21 := by rw [k₃ .x21 (by decide), x21₂]; simp
    x22 := by rw [b80011e24_x22 h₃, k₂ .x18 (by decide), ctx.x18]; simp [src]
    x23 := by
      rw [b80011e24_x23 h₃, x21₂, k₂ .x8 (by decide), ctx.x8, hm₂]
      simp only [slot, Nat.add_zero]
      have hp : r.getMem (s.getReg .x10 + 8) = vecPtr r (s.getReg .x10) := rfl
      rw [hp]
      addr_omega [hbuf, hcap, hcapl, hL, hnext]
    kept := fun q hq ↦ by
      rw [k₃ q (mem_of_mem hq _), k₂ q (mem_of_mem hq _), ctx.kept q (mem_of_mem hq _)] }
  obtain ⟨v, hv, hd⟩ := Reaches.loop (fun v ↦ ∃ k, Inv s t₁ r v k) (fun v ↦ (v.getReg .x9).toNat)
    (Done s t₁ r) (body hT hM hpre ctx) r₃ ⟨0, inv₀⟩
  exact hfin v (hr.trans (hr₂.trans (hr₃.trans hv))) hd

end Rv64Verifier.Layout.SpecExtend
