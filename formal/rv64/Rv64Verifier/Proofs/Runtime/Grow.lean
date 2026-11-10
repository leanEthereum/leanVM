import Rv64Verifier.Proofs.Runtime.Inv
import Rv64Verifier.Blocks.F42

/-!
# `RawVecInner::grow_amortized`, at `0x8000c184`

```rust
let required_cap = len.checked_add(additional).ok_or(CapacityOverflow)?;
let cap = cmp::max(self.cap * 2, required_cap);
let cap = cmp::max(min_non_zero_cap(elem_layout.size()), cap);
let ptr = finish_grow(cap, self.current_memory(elem_layout), &mut self.alloc, elem_layout)?;
self.set_ptr_and_cap(ptr, cap);
```

compiled (`Blocks/F42.lean`): `0x8000c184` adds and returns `0` (`0x8000c194`) on a carry;
`0x8000c19c`, `0x8000c1a8` take the larger of `2 * cap` and the sum; `0x8000c1ac` makes a 48-byte
frame (`ra`, `s0`, `s1`; the result of `finish_grow` at `sp`), and with `0x8000c1c4`..`0x8000c1d4`
takes the larger with `8` (one-byte elements) or `4`; `0x8000c1d8` calls `finish_grow`;
`0x8000c1f0` branches on its tag: `Ok`, `0x8000c200` stores the capacity and the pointer and
returns `-1`; `Err`, `0x8000c1f8` returns its payload. `0x8000c210` restores and returns.
-/

namespace Rv64Verifier.Runtime.Grow
open RiscvZkvm.Rv64 Rv64Verifier.Blocks.F42
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

def slots : List (Nat × Reg) := [(8, .x1), (16, .x8), (24, .x9)]

def kept : List Reg := [.x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- What the function writes besides its saved registers: the `RawVec`, `finish_grow`'s result at
the bottom of the frame and its 96 bytes below. -/
@[rv_addr] def W (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x10) 16 ∨ Within a (stackLo s growStack) 96 ∨
    Within a (s.getReg .x2 - 48) 24

abbrev Inv (s u : MachineState) (nx : Word) : Prop := FnInv s u 48 slots kept (W s) nx

theorem _root_.Rv64Verifier.Runtime.GrowPre.bounds {s : MachineState} (h : GrowPre s) :
    0x78000090 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ (s.getReg .x10).toNat % 8 = 0 ∧
      (s.getReg .x10).toNat + 16 ≤ 0xc0000008 := by
  have := h.stack.bounds (by decide) (by decide)
  have ha := h.stack.above
  have ho := ValidMemRange.bounds h.self (by decide)
  simp only [growStack, stackLo, heapEnd] at this ha
  rw [this.2.2.2] at ha
  omega

/-- The 48-byte frame lies above the heap. -/
theorem stack48 {s : MachineState} (h : GrowPre s) : RtStack s 48 := by
  have hb := h.bounds
  have hst := h.stack
  have hn := hst.next
  have hro := hst.rodata
  refine ⟨⟨?_, hst.aligned⟩, by addr_omega [hb], by addr_omega [hb, hn], by addr_omega [hb, hro]⟩
  exact ValidMemRange.sub hst.valid (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])

theorem Inv.step {s u v : MachineState} {nx nx' : Word} {X : Word → Prop}
    (hpre : GrowPre s) (h : Inv s u nx) (hX : ByteFrame u v X)
    (hXsub : ∀ a, X a → W s a ∨ Within a nextAddr 8 ∨ (heapNext s ≤ a.toNat ∧ a.toNat < nx'.toNat))
    (hnx : v.getMem nextAddr = nx') (hle : nx.toNat ≤ nx'.toNat) (hend : nx'.toNat ≤ heapEnd)
    (hr : ∀ r ∈ Reg.x2 :: kept, v.getReg r = u.getReg r) :
    Inv s v nx' := by
  have hb := hpre.bounds
  have hs := hpre.selfStack
  exact FnInv.step (m := 24) h (stack48 hpre) (by decide) (by decide) (by decide)
    (fun a ha ha' ↦ by simp only [W] at ha; addr_omega [ha, ha', hs, hb]) hX hXsub hnx hle hend
    (hr _ (by decide)) fun r hr' ↦ hr r (List.mem_cons_of_mem _ hr')

/-- A block that writes nothing. -/
theorem Inv.same {s u v : MachineState} {nx : Word} (hpre : GrowPre s) (h : Inv s u nx)
    (hm : ∀ a, v.getMem a = u.getMem a) {l : List Reg} (hk : ∀ r ∈ l, v.getReg r = u.getReg r)
    (hl : ∀ r ∈ Reg.x2 :: kept, r ∈ l := by decide) : Inv s v nx :=
  h.step hpre (ByteFrame.of_same hm fun _ ↦ False) (fun _ h ↦ h.elim) ((hm _).trans h.next)
    (Nat.le_refl _) h.fits fun r hr ↦ hk r (hl r hr)

theorem Inv.saved {s u : MachineState} {nx : Word} (h : Inv s u nx) :
    u.getReg .x2 = s.getReg .x2 - 48 ∧ u.getMem (s.getReg .x2 - 8) = s.getReg .x1 ∧
      u.getMem (s.getReg .x2 - 16) = s.getReg .x8 ∧ u.getMem (s.getReg .x2 - 24) = s.getReg .x9 := by
  have hsp := h.sp
  have sl := h.slots
  simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true] at sl
  rv_eval [] at hsp sl
  exact ⟨hsp, sl⟩

/-- The epilogue: restore, return. -/
theorem exit {s u : MachineState} {nx : Word} (hpre : GrowPre s) (hpc : u.pc = 0x8000c210)
    (h : Inv s u nx) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      t.getReg .x10 = u.getReg .x10 ∧ ∀ a, t.getMem a = u.getMem a := by
  have hb := hpre.bounds
  obtain ⟨hsp, sl1, sl2, sl3⟩ := h.saved
  obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b8000c210_spec hpc (by
    rv_eval [hsp]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have kk := b8000c210_keeps ht
  have pc := b8000c210_pc ht
  have x2 := b8000c210_x2 ht
  have x8 := b8000c210_x8 ht
  have x9 := b8000c210_x9 ht
  rv_eval [hsp, sl1, sl2, sl3] at pc x2 x8 x9
  refine ⟨t, hr, pc.trans (returnAddress_eq s).symm,
    preserves_of x2 x8 x9 ((kk .x18 (by decide)).trans (h.kept .x18 (by decide)))
      ((kk .x19 (by decide)).trans (h.kept .x19 (by decide)))
      fun r hr' ↦ (kk r (mem_of_mem hr' _)).trans (h.kept r (mem_of_mem hr' _)),
    kk .x10 (by decide), b8000c210_mem_same ht⟩

/-- The end: the heap and the contract's frame. -/
theorem finish {s u t : MachineState} {nx : Word} (hpre : GrowPre s) (h : Inv s u nx)
    (hbt : ByteFrame u t (Within · (s.getReg .x10) 16)) :
    t.getMem nextAddr = nx ∧ HeapOk t ∧ heapNext s ≤ heapNext t ∧
      ByteFrame s t fun a ↦ Within a (s.getReg .x10) 16 ∨
        Within a (stackLo s growStack) growStack ∨ Within a nextAddr 8 ∨ Fresh s t a := by
  have hb := hpre.bounds
  have ho := hpre.selfFree
  have hn : t.getMem nextAddr = nx :=
    (hbt.getMem fun i hi hw ↦ by addr_omega [hw, ho, hi, hb]).trans h.next
  have hlo := hpre.heap.lo
  have hm := h.mono
  have hf := h.fits
  have hnext : heapNext t = nx.toNat := by simp only [heapNext, hn]
  refine ⟨hn, ⟨by omega, by omega⟩, by omega,
    (h.frame hbt (fun a ha ↦ Or.inl ha) hn).mono ?_⟩
  intro a ha
  simp only [W] at ha
  rcases ha with (ha | ha | ha) | ha | ha | ha
  · exact Or.inl ha
  · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
  · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
  · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr ha))

/-- From `0x8000c1d8`, the new capacity in `s0`: `finish_grow`, then the `RawVec` updated. -/
theorem call (hF : FinishGrowSpec) {s u : MachineState} (hpre : GrowPre s)
    (hpc : u.pc = 0x8000c1d8) (h : Inv s u (s.getMem nextAddr))
    (hmem : ∀ a, ¬ Within a (stackLo s 48) 48 → u.getMem a = s.getMem a)
    (hself : u.getReg .x10 = s.getReg .x10) (hcap : u.getReg .x11 = s.getMem (s.getReg .x10))
    (hal : u.getReg .x14 = s.getReg .x13) (hsz : u.getReg .x15 = s.getReg .x14)
    (hnc : (s.getReg .x11).toNat + (s.getReg .x12).toNat ≤ (u.getReg .x8).toNat)
    (hle : (s.getMem (s.getReg .x10)).toNat ≤ (u.getReg .x8).toNat) :
    ∃ t, Reaches Image.code u t ∧
      ((t.pc = returnAddress s ∧ Preserves s t ∧ GrowPost s t) ∨ Dead Image.code t) := by
  have hb := hpre.bounds
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have ho := hpre.selfFree
  have hheap := hpre.heap
  have hss := hpre.selfStack
  have hlo := hheap.lo
  have hhi := hheap.hi
  have hraw := hpre.raw
  simp only [RawVecOk, Buf, vecPtr, vecCap] at hraw
  have hsp := h.saved.1
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000c1d8_spec hpc (by
    rv_eval [hself]
    valid_access hpre.self [hb])
  have k₁ := b8000c1d8_keeps h₁
  have inv₁ := h.same hpre (b8000c1d8_mem_same h₁) k₁
  have hout : t₁.getReg .x10 = s.getReg .x2 - 48 := by rw [b8000c1d8_x10 h₁, hsp]
  have hptr : t₁.getReg .x12 = s.getMem (s.getReg .x10 + 8) := by
    rw [b8000c1d8_x12 h₁, hself, hmem _ (by addr_omega [hb, hss])]
  have hn₁ : heapNext t₁ = heapNext s := by simp only [heapNext, inv₁.next]
  have hsl : stackLo t₁ finishGrowStack = s.getReg .x2 - 144 := by
    simp only [stackLo, finishGrowStack, k₁ .x2 (by decide), hsp]
    rw [Sym.sub_sub_lit]; rfl
  have hcap₁ : t₁.getReg .x11 = s.getMem (s.getReg .x10) := (k₁ .x11 (by decide)).trans hcap
  have hvout : ValidMemRange (t₁.getReg .x10) 3 := by
    rw [hout]
    exact ValidMemRange.sub hst.valid (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
  have hvst : ValidMemRange (stackLo t₁ finishGrowStack) (finishGrowStack / 8) := by
    rw [hsl]
    exact ValidMemRange.sub hst.valid (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
  have hold : Buf t₁ (t₁.getReg .x12) ((t₁.getReg .x11).toNat * (t₁.getReg .x15).toNat)
      (t₁.getReg .x14).toNat := by
    rw [hptr, hcap₁, k₁ .x14 (by decide), hal, k₁ .x15 (by decide), hsz]
    simp only [Buf, hn₁]
    exact hraw
  have hoo : Apart (t₁.getReg .x10) 24 (t₁.getReg .x12)
      ((t₁.getReg .x11).toNat * (t₁.getReg .x15).toNat) := by
    rw [hout, hptr, hcap₁, k₁ .x15 (by decide), hsz]
    rcases hraw.2 with h0 | h0
    · exact Or.inr (Or.inl h0)
    · addr_omega [h0, hab, hb, hhi]
  have hpre₁ : FinishGrowPre t₁ := {
    heap := ⟨hn₁ ▸ hlo, hn₁ ▸ hhi⟩
    out := hvout
    align := by rw [k₁ .x14 (by decide), hal]; exact hpre.align
    size := by rw [k₁ .x15 (by decide), hsz]; exact hpre.size
    old := hold
    le := by rw [hcap₁, b8000c1d8_x13 h₁]; exact hle
    stack := ⟨⟨hvst, by rw [k₁ .x2 (by decide), hsp]; addr_omega [hb]⟩,
      by rw [hsl]; addr_omega [hb, hab], by rw [hsl]; addr_omega [hb, hnx8],
      by rw [hsl]; addr_omega [hb, hst.rodata]⟩
    outFree := ⟨Or.inr (by rw [hout]; addr_omega [hb, hab]), by rw [hout]; addr_omega [hb, hnx8]⟩
    outStack := by rw [hout, hsl]; addr_omega [hb]
    outOld := hoo }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost⟩ | hdead⟩ := hF.call hr₁ (b8000c1d8_pc h₁) hpre₁
  swap
  · exact ⟨t₂, hr₂, Or.inr hdead⟩
  have hf := hpost.frame
  rw [hout, hsl] at hf
  have hm2 := hpost.mono
  have inv₂ := inv₁.step hpre hf (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl (Or.inr (Or.inr ha))
      · exact Or.inl (Or.inr (Or.inl (by addr_omega [ha, hb])))
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (by simp only [Fresh, hn₁] at ha; exact ha)))
    rfl (by simp only [heapNext, inv₁.next] at hm2 ⊢; exact hm2) hpost.heap.hi
    fun r hr ↦ hpres₂ r (mem_of_mem hr _)
  have hsp₂ : t₂.getReg .x2 = s.getReg .x2 - 48 := inv₂.saved.1
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000c1f0_spec
    (by rw [hpc₂, returnAddress_eq, b8000c1d8_x1 h₁]; decide) (by
      rv_eval [hsp₂]
      valid_access hst.valid [hb])
  have k₃ := b8000c1f0_keeps h₃
  have inv₃ := inv₂.same hpre (b8000c1f0_mem_same h₃) k₃
  have hx9 : t₃.getReg .x9 = s.getReg .x10 := by
    rw [k₃ .x9 (by decide), hpres₂.reg .x9, b8000c1d8_x9 h₁, hself]
  by_cases htag : t₂.getMem (s.getReg .x2 - 48) = 0
  · -- `Ok`: the capacity and the pointer to the `RawVec`, `-1`
    obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000c200_spec
      (b8000c1f0_pc_taken h₃ (by rw [hsp₂]; exact htag)) (by
        rv_eval [hx9, k₃ .x2 (by decide), hsp₂]
        and_intros <;> first | valid_access hpre.self [hb] | valid_access hst.valid [hb])
    have k₄ := b8000c200_keeps h₄
    have hm₄ := b8000c200_frame h₄ (by rw [hx9]; addr_omega [hb])
    rw [hx9] at hm₄
    have bf₄ := ByteFrame.of_memFrame hm₄ (by addr_omega [hb]) (by decide)
      (h₄.unaligned (by rv_eval [hx9]; and_intros <;> addr_omega [hb]))
    have inv₄ := inv₃.step hpre bf₄ (fun a ha ↦ Or.inl (Or.inl ha))
      ((bf₄.getMem fun i hi ha ↦ by addr_omega [ha, hi, ho, hb]).trans inv₃.next) (Nat.le_refl _)
      inv₃.fits fun r hr ↦ k₄ r (mem_of_mem hr _)
    obtain ⟨t, hr, hpc', hpres, hx10, hmt⟩ := exit hpre (b8000c200_pc h₄) inv₄
    obtain ⟨hnt, hheap', hmono, hframe⟩ := finish hpre inv₄ (ByteFrame.of_same hmt _)
    have hok := hpost.ok (by rw [hout]; exact htag)
    rw [hout] at hok
    obtain ⟨hnew, hbytes⟩ := hok
    have hp : vecPtr t (s.getReg .x10) = t₂.getMem (s.getReg .x2 - 48 + 8) := by
      have := b8000c200_m_x9_8 h₄
      rw [hx9, k₃ .x2 (by decide), hsp₂] at this
      rw [vecPtr, hmt, this, b8000c1f0_mem_same h₃]
    have hc : vecCap t (s.getReg .x10) = u.getReg .x8 := by
      have := b8000c200_m_x9_0 h₄
      rw [hx9] at this
      rw [vecCap, hmt, this, k₃ .x8 (by decide), hpres₂.reg .x8, k₁ .x8 (by decide)]
    have hbt : heapNext t = heapNext t₂ := by simp only [heapNext, hnt]
    rw [b8000c1d8_x13 h₁, k₁ .x15 (by decide), hsz, k₁ .x14 (by decide), hal] at hnew
    rw [k₁ .x11 (by decide), hcap, k₁ .x15 (by decide), hsz, hptr] at hbytes
    have hbuf := hnew.buf ⟨hn₁ ▸ hlo, hn₁ ▸ hhi⟩
    have hfresh : NewBuf s t (vecPtr t (s.getReg .x10))
        ((vecCap t (s.getReg .x10)).toNat * (s.getReg .x14).toNat) (s.getReg .x13).toNat := by
      simp only [NewBuf, hc, hp, hbt, hn₁] at hnew ⊢
      exact hnew
    refine ⟨t, hr₂.trans (hr₃.trans (hr₄.trans hr)), Or.inl ⟨hpc', hpres,
      hheap', hmono, fun _ ↦ ?_, hframe, fun _ ↦ hfresh⟩⟩
    refine ⟨by rw [hc]; exact hnc, ?_, ?_⟩
    · simp only [RawVecOk, Buf, hc, hp, hbt] at hbuf ⊢
      exact hbuf
    · have hle' : (s.getMem (s.getReg .x10)).toNat * (s.getReg .x14).toNat ≤
          (u.getReg .x8).toNat * (s.getReg .x14).toNat := Nat.mul_le_mul_right _ hle
      have hm2' : heapNext t₂ ≤ heapEnd := hpost.heap.hi
      rcases hraw.2 with h0 | h0
      · simp only [vecCap, h0]; rfl
      rw [hp]
      simp only [vecCap, vecPtr]
      rw [(ByteFrame.of_same hmt fun _ ↦ False).bytesAt fun _ _ h ↦ h,
        bf₄.bytesAt fun i hi ha ↦ ?_,
        (ByteFrame.of_same (b8000c1f0_mem_same h₃) fun _ ↦ False).bytesAt fun _ _ h ↦ h,
        hbytes,
        bytesAt_of_below (lo := stackLo s 48) (N := 48)
          (fun a ha ↦ (b8000c1d8_mem_same h₁ a).trans (hmem a ha))]
      · addr_omega [h0, hab, hhi, hb]
      · rcases hnew.2 with h1 | h1
        · rw [h1] at hle'; omega
        · simp only [heapNext] at hn₁ h1 hm2'
          addr_omega [ha, hi, ho, h1, hle', hn₁, hm2', hb]
  · -- `Err`: its payload, never `-1`
    obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000c1f8_spec
      (b8000c1f0_pc_not_taken h₃ (by rw [hsp₂]; exact htag)) (by
        rv_eval [k₃ .x2 (by decide), hsp₂]
        valid_access hst.valid [hb])
    have k₄ := b8000c1f8_keeps h₄
    have inv₄ := inv₃.same hpre (b8000c1f8_mem_same h₄) k₄
    obtain ⟨t, hr, hpc', hpres, hx10, hmt⟩ := exit hpre (b8000c1f8_pc h₄) inv₄
    obtain ⟨-, hheap', hmono, hframe⟩ := finish hpre inv₄ (ByteFrame.of_same hmt _)
    suffices hne : t.getReg .x10 ≠ 0xffffffffffffffff from
      ⟨t, hr₂.trans (hr₃.trans (hr₄.trans hr)), Or.inl ⟨hpc', hpres,
        hheap', hmono, fun h1 ↦ absurd h1 hne, hframe, fun h1 ↦ absurd h1 hne⟩⟩
    intro h1
    have herr := hpost.err (by rw [hout]; exact htag)
    rw [hout] at herr
    have := b8000c1f8_x10 h₄
    rw [k₃ .x2 (by decide), hsp₂, b8000c1f0_mem_same h₃, show s.getReg .x2 - 48 + 8 =
      t₁.getReg .x10 + 8 by rw [hout], hout, herr] at this
    rw [hx10, this] at h1
    cases h1

/-- From `0x8000c1d0`, the minimum capacity in `s0`, the larger of `2 * cap` and the sum in `a2`:
the larger of the two, then the call. -/
theorem least (hF : FinishGrowSpec) {s u : MachineState} (hpre : GrowPre s)
    (hpc : u.pc = 0x8000c1d0) (h : Inv s u (s.getMem nextAddr))
    (hmem : ∀ a, ¬ Within a (stackLo s 48) 48 → u.getMem a = s.getMem a)
    (hself : u.getReg .x10 = s.getReg .x10) (hcap : u.getReg .x11 = s.getMem (s.getReg .x10))
    (hal : u.getReg .x14 = s.getReg .x13) (hsz : u.getReg .x15 = s.getReg .x14)
    (hnc : (s.getReg .x11).toNat + (s.getReg .x12).toNat ≤ (u.getReg .x12).toNat)
    (hle : (s.getMem (s.getReg .x10)).toNat ≤ (u.getReg .x12).toNat) :
    ∃ t, Reaches Image.code u t ∧
      ((t.pc = returnAddress s ∧ Preserves s t ∧ GrowPost s t) ∨ Dead Image.code t) := by
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000c1d0_spec hpc trivial
  have k₁ := b8000c1d0_keeps h₁
  have inv₁ := h.same hpre (b8000c1d0_mem_same h₁) k₁
  have hm₁ (a : Word) (ha : ¬ Within a (stackLo s 48) 48) : t₁.getMem a = s.getMem a :=
    (b8000c1d0_mem_same h₁ a).trans (hmem a ha)
  by_cases hlt : (u.getReg .x12).toNat < (u.getReg .x8).toNat
  · obtain ⟨t, hr, ht⟩ := call hF hpre (b8000c1d0_pc_taken h₁ hlt) inv₁ hm₁
      (by rw [k₁ .x10 (by decide), hself]) (by rw [k₁ .x11 (by decide), hcap])
      (by rw [k₁ .x14 (by decide), hal]) (by rw [k₁ .x15 (by decide), hsz])
      (by rw [k₁ .x8 (by decide)]; omega) (by rw [k₁ .x8 (by decide)]; omega)
    exact ⟨t, hr₁.trans hr, ht⟩
  · obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000c1d4_spec
      (b8000c1d0_pc_not_taken h₁ (Nat.le_of_not_lt hlt)) trivial
    have k₂ := b8000c1d4_keeps h₂
    have inv₂ := inv₁.same hpre (b8000c1d4_mem_same h₂) k₂
    obtain ⟨t, hr, ht⟩ := call hF hpre (b8000c1d4_pc h₂) inv₂
      (fun a ha ↦ (b8000c1d4_mem_same h₂ a).trans (hm₁ a ha))
      (by rw [k₂ .x10 (by decide), k₁ .x10 (by decide), hself])
      (by rw [k₂ .x11 (by decide), k₁ .x11 (by decide), hcap])
      (by rw [k₂ .x14 (by decide), k₁ .x14 (by decide), hal])
      (by rw [k₂ .x15 (by decide), k₁ .x15 (by decide), hsz])
      (by rw [b8000c1d4_x8 h₂, k₁ .x12 (by decide)]; omega)
      (by rw [b8000c1d4_x8 h₂, k₁ .x12 (by decide)]; omega)
    exact ⟨t, hr₁.trans (hr₂.trans hr), ht⟩

/-- From `0x8000c1ac`, before the frame, the larger of `2 * cap` and the sum in `a2`. -/
theorem framed (hF : FinishGrowSpec) {s u : MachineState} (hpre : GrowPre s)
    (hpc : u.pc = 0x8000c1ac) (hmem : ∀ a, u.getMem a = s.getMem a)
    (hregs : ∀ r ∈ [Reg.x1, .x2, .x8, .x9, .x10, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25,
      .x26, .x27], u.getReg r = s.getReg r)
    (hcap : u.getReg .x11 = s.getMem (s.getReg .x10))
    (hal : u.getReg .x14 = s.getReg .x13) (hsz : u.getReg .x15 = s.getReg .x14)
    (hnc : (s.getReg .x11).toNat + (s.getReg .x12).toNat ≤ (u.getReg .x12).toNat)
    (hle : (s.getMem (s.getReg .x10)).toNat ≤ (u.getReg .x12).toNat) :
    ∃ t, Reaches Image.code u t ∧
      ((t.pc = returnAddress s ∧ Preserves s t ∧ GrowPost s t) ∨ Dead Image.code t) := by
  have hb := hpre.bounds
  have hsp : u.getReg .x2 = s.getReg .x2 := hregs .x2 (by decide)
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000c1ac_spec hpc (by
    rv_eval [hsp]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₁ := b8000c1ac_keeps h₁
  have hm₁ := b8000c1ac_frame h₁ (by rw [hsp]; addr_omega [hb])
  rw [hsp] at hm₁
  have inv₁ : Inv s t₁ (s.getMem nextAddr) := FnInv.init hpre.heap (stack48 hpre)
    (by rw [b8000c1ac_x2 h₁, hsp]; rfl)
    (by
      simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      rv_eval []
      have m8 := b8000c1ac_m_x2_n8 h₁
      have m16 := b8000c1ac_m_x2_n16 h₁
      have m24 := b8000c1ac_m_x2_n24 h₁
      rw [hsp, hregs .x1 (by decide)] at m8
      rw [hsp, hregs .x8 (by decide)] at m16
      rw [hsp, hregs .x9 (by decide)] at m24
      exact ⟨m8, m16, m24⟩)
    (fun r hr ↦ (k₁ r (mem_of_mem hr _)).trans (hregs r (mem_of_mem hr _)))
    (fun a ha ↦ (hm₁ a (by addr_omega [ha, hb])).trans (hmem a))
    (fun a ha ↦ (h₁.unaligned (by rv_eval [hsp]; and_intros <;> addr_omega [hb]) a ha).trans
      (hmem a)) (by decide)
  have hmem₁ (a : Word) (ha : ¬ Within a (stackLo s 48) 48) : t₁.getMem a = s.getMem a :=
    (hm₁ a (by addr_omega [ha, hb])).trans (hmem a)
  have rest (t₂ : MachineState) (hr₂ : Reaches Image.code t₁ t₂) (hpc₂ : t₂.pc = 0x8000c1d0)
      (hm : ∀ a, t₂.getMem a = t₁.getMem a) (hk : ∀ r ∈ [Reg.x2, .x9, .x10, .x11, .x12, .x14,
        .x15, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27], t₂.getReg r = t₁.getReg r) :
      ∃ t, Reaches Image.code u t ∧
        ((t.pc = returnAddress s ∧ Preserves s t ∧ GrowPost s t) ∨ Dead Image.code t) := by
    obtain ⟨t, hr, ht⟩ := least hF hpre hpc₂ (inv₁.same hpre hm hk)
      (fun a ha ↦ (hm a).trans (hmem₁ a ha))
      (by rw [hk .x10 (by decide), k₁ .x10 (by decide), hregs .x10 (by decide)])
      (by rw [hk .x11 (by decide), k₁ .x11 (by decide), hcap])
      (by rw [hk .x14 (by decide), k₁ .x14 (by decide), hal])
      (by rw [hk .x15 (by decide), k₁ .x15 (by decide), hsz])
      (by rw [hk .x12 (by decide), k₁ .x12 (by decide)]; exact hnc)
      (by rw [hk .x12 (by decide), k₁ .x12 (by decide)]; exact hle)
    exact ⟨t, hr₁.trans (hr₂.trans hr), ht⟩
  by_cases h1 : u.getReg .x15 = 1
  · obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000c1cc_spec (b8000c1ac_pc_taken h₁ h1) trivial
    exact rest t₂ hr₂ (b8000c1cc_pc h₂) (b8000c1cc_mem_same h₂)
      fun r hr ↦ b8000c1cc_keeps h₂ r (mem_of_mem hr _)
  · obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000c1c4_spec (b8000c1ac_pc_not_taken h₁ h1)
      trivial
    exact rest t₂ hr₂ (b8000c1c4_pc h₂) (b8000c1c4_mem_same h₂)
      fun r hr ↦ b8000c1c4_keeps h₂ r (mem_of_mem hr _)

/-- **`grow_amortized` meets its contract**, given `finish_grow`'s. -/
theorem grow_spec (hF : FinishGrowSpec) : GrowSpec := by
  intro s hpc hpre
  have hb := hpre.bounds
  have hsz := hpre.size
  have hraw := hpre.raw
  simp only [RawVecOk, Buf, vecPtr, vecCap] at hraw
  have hcapb : (s.getMem (s.getReg .x10)).toNat < 2 ^ 62 := by
    rcases hraw.2 with h0 | h0
    · rcases Nat.mul_eq_zero.mp h0 with h | h <;> omega
    · have := hpre.heap.hi
      have := Nat.le_mul_of_pos_right (s.getMem (s.getReg .x10)).toNat hsz
      simp only [heapNext, heapEnd] at *
      omega
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000c184_spec hpc trivial
  have k₁ := b8000c184_keeps h₁
  by_cases hov : (s.getReg .x12 + s.getReg .x11).toNat < (s.getReg .x12).toNat
  · -- the sum overflows: `0`
    obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000c194_spec (b8000c184_pc_not_taken h₁ hov)
      trivial
    have k₂ := b8000c194_keeps h₂
    have hm (a : Word) : t₂.getMem a = s.getMem a :=
      (b8000c194_mem_same h₂ a).trans (b8000c184_mem_same h₁ a)
    have hn : heapNext t₂ = heapNext s := by simp only [heapNext, hm]
    refine ⟨t₂, hr₁.trans hr₂, Or.inl ⟨by rw [b8000c194_pc h₂, k₁ .x1 (by decide)]; rfl,
      fun r hr ↦ (k₂ r (mem_of_mem hr _)).trans (k₁ r (mem_of_mem hr _)),
      ⟨hn ▸ hpre.heap.lo, hn ▸ hpre.heap.hi⟩, hn.ge, fun h0 ↦ ?_,
      ByteFrame.of_same hm _, fun h0 ↦ ?_⟩⟩ <;>
    · rw [b8000c194_x10 h₂] at h0
      cases h0
  have hreq : (s.getReg .x12 + s.getReg .x11).toNat = (s.getReg .x12).toNat + (s.getReg .x11).toNat := by
    rw [BitVec.toNat_add] at hov ⊢
    have := (s.getReg .x11).isLt
    omega
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000c19c_spec
    (b8000c184_pc_taken h₁ (Nat.le_of_not_lt hov)) (by
      rv_eval [k₁ .x10 (by decide)]
      valid_access hpre.self [hb])
  have k₂ := b8000c19c_keeps h₂
  have hm₂ (a : Word) : t₂.getMem a = s.getMem a :=
    (b8000c19c_mem_same h₂ a).trans (b8000c184_mem_same h₁ a)
  have hcap : t₂.getReg .x11 = s.getMem (s.getReg .x10) := by
    rw [b8000c19c_x11 h₂, k₁ .x10 (by decide), b8000c184_mem_same h₁]
  have h2c : (t₁.getMem (t₁.getReg .x10) * 2).toNat = 2 * (s.getMem (s.getReg .x10)).toNat := by
    rw [k₁ .x10 (by decide), b8000c184_mem_same h₁, BitVec.toNat_mul,
      show (2 : Word).toNat = 2 from rfl]
    omega
  have hx13 : t₁.getReg .x13 = s.getReg .x12 + s.getReg .x11 := b8000c184_x13 h₁
  have go (u : MachineState) (hr : Reaches Image.code s u) (hpcu : u.pc = 0x8000c1ac)
      (hm : ∀ a, u.getMem a = t₂.getMem a)
      (hk : ∀ r ∈ [Reg.x1, .x2, .x8, .x9, .x10, .x11, .x13, .x14, .x15, .x18, .x19, .x20, .x21,
        .x22, .x23, .x24, .x25, .x26, .x27], u.getReg r = t₂.getReg r)
      (hnc : (s.getReg .x11).toNat + (s.getReg .x12).toNat ≤ (u.getReg .x12).toNat)
      (hle : (s.getMem (s.getReg .x10)).toNat ≤ (u.getReg .x12).toNat) :
      ∃ t, Reaches Image.code s t ∧
        ((t.pc = returnAddress s ∧ Preserves s t ∧ GrowPost s t) ∨ Dead Image.code t) := by
    obtain ⟨t, hr', ht⟩ := framed hF hpre hpcu (fun a ↦ (hm a).trans (hm₂ a))
      (fun r hr'' ↦ by rw [hk r (mem_of_mem hr'' _), k₂ r (mem_of_mem hr'' _),
        k₁ r (mem_of_mem hr'' _)])
      (by rw [hk .x11 (by decide), hcap])
      (by rw [hk .x14 (by decide), k₂ .x14 (by decide), b8000c184_x14 h₁])
      (by rw [hk .x15 (by decide), k₂ .x15 (by decide), b8000c184_x15 h₁]) hnc hle
    exact ⟨t, hr.trans hr', ht⟩
  by_cases hlt : (t₁.getReg .x13).toNat < (t₁.getMem (t₁.getReg .x10) * 2).toNat
  · exact go t₂ (hr₁.trans hr₂) (b8000c19c_pc_taken h₂ hlt) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
      (by rw [b8000c19c_x12 h₂]; rw [hx13, hreq] at hlt; omega)
      (by rw [b8000c19c_x12 h₂, h2c]; omega)
  · obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000c1a8_spec
      (b8000c19c_pc_not_taken h₂ (Nat.le_of_not_lt hlt)) trivial
    have k₃ := b8000c1a8_keeps h₃
    exact go t₃ (hr₁.trans (hr₂.trans hr₃)) (b8000c1a8_pc h₃) (b8000c1a8_mem_same h₃)
      (fun r hr ↦ k₃ r (mem_of_mem hr _))
      (by rw [b8000c1a8_x12 h₃, k₂ .x13 (by decide), hx13, hreq]; omega)
      (by rw [b8000c1a8_x12 h₃, k₂ .x13 (by decide)]; rw [h2c] at hlt; omega)

end Rv64Verifier.Runtime.Grow
