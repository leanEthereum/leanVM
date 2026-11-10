import Rv64Verifier.Proofs.Runtime.Inv
import Rv64Verifier.Blocks.F43

/-!
# `RawVecInner::finish_grow`, at `0x8000c224`

```rust
let new_layout = layout_array(cap, elem_layout)?;         // else Err(CapacityOverflow)
let memory = if let Some((ptr, old_layout)) = current_memory {
    alloc.grow(ptr, old_layout, new_layout)                // a bump allocator: alloc + memcpy
} else {
    alloc.allocate(new_layout)                             // none for a zero size
};
memory.map_err(|_| AllocError { layout: new_layout }.into())
```

compiled (`Blocks/F43.lean`): `0x8000c224` saves `ra`, `s0`..`s7` in an 80-byte frame (`s0` = the
result, `s1` = the new size, `s4` = the tag, 1) and branches on the overflow check; `0x8000c278`
sets the overflow error. `0x8000c284` branches on the old capacity: nonzero, `0x8000c288` calls
`alloc`, `0x8000c2a8` checks for null (never) and `0x8000c2ac` calls `memcpy(new, old, old size)`,
joining `0x8000c2f0`; zero, `0x8000c2c4` branches on the new size: zero, `0x8000c2ec` takes the
pointer `align`; else `0x8000c2c8` calls `alloc` and `0x8000c2dc` checks for null. `0x8000c2f0`
writes the pointer and the tag `0`, `0x8000c2f8` and `0x8000c2fc` write the size (or the error's
payload, `0`), the tag, restore and return.
-/

namespace Rv64Verifier.Runtime.FinishGrow
open RiscvZkvm.Rv64 Rv64Verifier.Blocks.F43
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

def slots : List (Nat × Reg) :=
  [(8, .x1), (16, .x8), (24, .x9), (32, .x18), (40, .x19), (48, .x20), (56, .x21), (64, .x22),
    (72, .x23)]

def kept : List Reg := [.x24, .x25, .x26, .x27]

/-- What the function writes besides its frame: the result, and `memcpy`'s 16 bytes below the
frame. -/
@[rv_addr] def W (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x10) 24 ∨ Within a (stackLo s finishGrowStack) 16

abbrev Inv (s u : MachineState) (nx : Word) : Prop := FnInv s u 80 slots kept (W s) nx

theorem _root_.Rv64Verifier.Runtime.FinishGrowPre.bounds {s : MachineState}
    (h : FinishGrowPre s) :
    0x78000060 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ (s.getReg .x10).toNat % 8 = 0 ∧
      (s.getReg .x10).toNat + 24 ≤ 0xc0000008 := by
  have := h.stack.bounds (by decide) (by decide)
  have ha := h.stack.above
  have ho := ValidMemRange.bounds h.out (by decide)
  simp only [finishGrowStack, stackLo, heapEnd] at this ha
  rw [this.2.2.2] at ha
  omega

/-- The 80-byte frame lies above the heap. -/
theorem stack80 {s : MachineState} (h : FinishGrowPre s) : RtStack s 80 := by
  have hb := h.bounds
  have hst := h.stack
  have hn := hst.next
  have hro := hst.rodata
  refine ⟨⟨?_, hst.aligned⟩, by addr_omega [hb], by addr_omega [hb, hn], by addr_omega [hb, hro]⟩
  exact ValidMemRange.sub hst.valid (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])

theorem Inv.step {s u v : MachineState} {nx nx' : Word} {X : Word → Prop}
    (hpre : FinishGrowPre s) (h : Inv s u nx) (hX : ByteFrame u v X)
    (hXsub : ∀ a, X a → W s a ∨ Within a nextAddr 8 ∨ (heapNext s ≤ a.toNat ∧ a.toNat < nx'.toNat))
    (hnx : v.getMem nextAddr = nx') (hle : nx.toNat ≤ nx'.toNat) (hend : nx'.toNat ≤ heapEnd)
    (hr : ∀ r ∈ [Reg.x2, .x24, .x25, .x26, .x27], v.getReg r = u.getReg r) :
    Inv s v nx' := by
  have hb := hpre.bounds
  have hs := hpre.outStack
  exact FnInv.step h (stack80 hpre) (by decide) (Nat.le_refl _) (by decide)
    (fun a ha ha' ↦ by simp only [W] at ha; addr_omega [ha, ha', hs, hb]) hX hXsub hnx hle hend
    (hr _ (by decide)) fun r hr' ↦ hr r (mem_of_mem hr' _)

/-- A block that writes only the result, or nothing. -/
theorem Inv.out {s u v : MachineState} {nx : Word} {X : Word → Prop} (hpre : FinishGrowPre s)
    (h : Inv s u nx) (hX : ByteFrame u v X) (hXsub : ∀ a, X a → Within a (s.getReg .x10) 24)
    (hr : ∀ r ∈ [Reg.x2, .x24, .x25, .x26, .x27], v.getReg r = u.getReg r) :
    Inv s v nx := by
  have hb := hpre.bounds
  have ho := hpre.outFree
  have hnx : v.getMem nextAddr = nx :=
    (hX.getMem fun i hi hw ↦ by have := hXsub _ hw; addr_omega [this, ho, hi, hb]).trans h.next
  exact h.step hpre hX (fun a ha ↦ Or.inl (Or.inl (hXsub a ha))) hnx (Nat.le_refl _) h.fits hr

/-- A block that writes nothing. -/
theorem Inv.same {s u v : MachineState} {nx : Word} (hpre : FinishGrowPre s) (h : Inv s u nx)
    (hm : ∀ a, v.getMem a = u.getMem a) {l : List Reg} (hk : ∀ r ∈ l, v.getReg r = u.getReg r)
    (hl : ∀ r ∈ [Reg.x2, .x24, .x25, .x26, .x27], r ∈ l := by decide) : Inv s v nx :=
  h.out hpre (ByteFrame.of_same hm fun _ ↦ False) (fun _ h ↦ h.elim) fun r hr ↦ hk r (hl r hr)

/-- A call to `alloc`. -/
theorem Inv.alloc {s u v : MachineState} {nx : Word} (hpre : FinishGrowPre s) (h : Inv s u nx)
    (hpost : AllocPost u v) (hres : Preserves u v) : Inv s v (v.getMem nextAddr) := by
  have h1 := hpost.above
  have h2 := hpost.next
  have h3 := hpost.heap.hi
  have hn : heapNext u = nx.toNat := by simp only [heapNext, h.next]
  exact h.step hpre hpost.byteFrame (fun a ha ↦ Or.inr (Or.inl ha)) rfl
    (by simp only [heapNext] at h1 h2 hn; omega) (by simpa only [heapNext] using h3)
    fun r hr ↦ hres r (mem_of_mem hr _)

theorem Inv.saved {s u : MachineState} {nx : Word} (h : Inv s u nx) :
    u.getReg .x2 = s.getReg .x2 - 80 ∧ u.getMem (s.getReg .x2 - 8) = s.getReg .x1 ∧
      u.getMem (s.getReg .x2 - 16) = s.getReg .x8 ∧ u.getMem (s.getReg .x2 - 24) = s.getReg .x9 ∧
      u.getMem (s.getReg .x2 - 32) = s.getReg .x18 ∧
      u.getMem (s.getReg .x2 - 40) = s.getReg .x19 ∧ u.getMem (s.getReg .x2 - 48) = s.getReg .x20 ∧
      u.getMem (s.getReg .x2 - 56) = s.getReg .x21 ∧ u.getMem (s.getReg .x2 - 64) = s.getReg .x22 ∧
      u.getMem (s.getReg .x2 - 72) = s.getReg .x23 := by
  have hsp := h.sp
  have sl := h.slots
  simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true] at sl
  rv_eval [] at hsp sl
  exact ⟨hsp, sl⟩

/-- The epilogue: `s1` to `result + k` (`k` = 8 or 16), the tag `s4` to `result`, restore,
return. -/
theorem exit {s u : MachineState} {nx k : Word} (hpre : FinishGrowPre s) (hpc : u.pc = 0x8000c2fc)
    (h : Inv s u nx) (hout : u.getReg .x8 = s.getReg .x10) (hk : u.getReg .x10 = k)
    (hk' : k = 8 ∨ k = 16) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      t.getMem (s.getReg .x10) = u.getReg .x20 ∧ t.getMem (s.getReg .x10 + k) = u.getReg .x9 ∧
      (∀ a, a ≠ s.getReg .x10 → a ≠ s.getReg .x10 + k → t.getMem a = u.getMem a) ∧
      ByteFrame u t (Within · (s.getReg .x10) 24) := by
  have hb := hpre.bounds
  have hs := hpre.outStack
  have hk8 : k.toNat = 8 ∨ k.toNat = 16 := by rcases hk' with rfl | rfl <;> decide
  obtain ⟨hsp, sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9⟩ := h.saved
  obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b8000c2fc_spec hpc (by
    rv_eval [hsp, hout, hk]
    and_intros <;> first
      | addr_omega [hb, hs, hk8]
      | valid_access hpre.stack.valid [hb]
      | valid_access hpre.out [hb, hk8])
  have kk := b8000c2fc_keeps ht
  have pc := b8000c2fc_pc ht
  have x2 := b8000c2fc_x2 ht
  have x8 := b8000c2fc_x8 ht
  have x9 := b8000c2fc_x9 ht
  have x18 := b8000c2fc_x18 ht
  have x19 := b8000c2fc_x19 ht
  have x20 := b8000c2fc_x20 ht
  have x21 := b8000c2fc_x21 ht
  have x22 := b8000c2fc_x22 ht
  have x23 := b8000c2fc_x23 ht
  have m0 := b8000c2fc_m_x8_0 ht
  have m1 := b8000c2fc_m1 ht
  rv_eval [hsp, sl1, sl2, sl3, sl4, sl5, sl6, sl7, sl8, sl9, hout, hk]
    at pc x2 x8 x9 x18 x19 x20 x21 x22 x23 m0 m1
  have hfr : ∀ a, a ≠ s.getReg .x10 → a ≠ s.getReg .x10 + k → t.getMem a = u.getMem a :=
    fun a h1 h2 ↦ ht.frame a (by rv_eval [hout, hk]; exact ⟨h1, h2⟩)
  refine ⟨t, hr, pc.trans (returnAddress_eq s).symm, preserves_of x2 x8 x9 x18 x19 fun r hr' ↦ ?_,
    m0, m1, hfr, ByteFrame.of_dwords (fun a _ ha ↦ hfr a (fun h' ↦ ha (by addr_omega [h', hb]))
      (fun h' ↦ ha (by addr_omega [h', hb, hk8])))
      (fun a ha ↦ hfr a (fun h' ↦ ha (by addr_omega [h', hb]))
        (fun h' ↦ ha (by addr_omega [h', hb, hk8])))
      fun _ ha ↦ within_of_alignDown (by addr_omega [hb]) (by decide) ha⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact x20
  · exact x21
  · exact x22
  · exact x23
  all_goals exact (kk _ (by decide)).trans (h.kept _ (by decide))

/-- The end of a run: the heap and the contract's frame. -/
theorem finish {s u t : MachineState} {nx : Word} (hpre : FinishGrowPre s) (h : Inv s u nx)
    (hbt : ByteFrame u t (Within · (s.getReg .x10) 24)) :
    t.getMem nextAddr = nx ∧ HeapOk t ∧ heapNext s ≤ heapNext t ∧
      ByteFrame s t fun a ↦ Within a (s.getReg .x10) 24 ∨
        Within a (stackLo s finishGrowStack) finishGrowStack ∨ Within a nextAddr 8 ∨ Fresh s t a := by
  have hb := hpre.bounds
  have ho := hpre.outFree
  have hn : t.getMem nextAddr = nx :=
    (hbt.getMem fun i hi hw ↦ by addr_omega [hw, ho, hi, hb]).trans h.next
  have hlo := hpre.heap.lo
  have hm := h.mono
  have hf := h.fits
  have hnext : heapNext t = nx.toNat := by simp only [heapNext, hn]
  refine ⟨hn, ⟨by omega, by omega⟩, by omega, (h.frame hbt (fun a ha ↦ Or.inl ha) hn).mono ?_⟩
  intro a ha
  simp only [W] at ha
  rcases ha with (ha | ha) | ha | ha | ha
  · exact Or.inl ha
  · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
  · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr ha))

/-- From `0x8000c2f0`: the pointer `s2` to `result + 8`, the size `s1` to `result + 16`, `Ok`. -/
theorem tail {s u : MachineState} {nx : Word} (hpre : FinishGrowPre s) (hpc : u.pc = 0x8000c2f0)
    (h : Inv s u nx) (hout : u.getReg .x8 = s.getReg .x10) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      t.getMem (s.getReg .x10) = 0 ∧ t.getMem (s.getReg .x10 + 8) = u.getReg .x18 ∧
      t.getMem (s.getReg .x10 + 16) = u.getReg .x9 ∧ ByteFrame u t (Within · (s.getReg .x10) 24) := by
  have hb := hpre.bounds
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000c2f0_spec hpc (by
    rv_eval [hout]
    valid_access hpre.out [hb])
  have k₁ := b8000c2f0_keeps h₁
  have hm₁ := b8000c2f0_frame h₁ (by rw [hout]; addr_omega [hb])
  rw [hout] at hm₁
  have bf₁ := ByteFrame.of_memFrame hm₁ (by addr_omega [hb]) (by decide)
    (h₁.unaligned (by rv_eval [hout]; addr_omega [hb]))
  have inv₁ := h.out hpre bf₁ (fun a ha ↦ by addr_omega [ha, hb]) fun r hr ↦ k₁ r (mem_of_mem hr _)
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000c2f8_spec (b8000c2f0_pc h₁) trivial
  have k₂ := b8000c2f8_keeps h₂
  have inv₂ := inv₁.same hpre (b8000c2f8_mem_same h₂) k₂
  obtain ⟨t, hr, hpc', hpres, htag, h16, hfr, hbt⟩ := exit hpre (b8000c2f8_pc h₂) inv₂
    (by rw [k₂ .x8 (by decide), k₁ .x8 (by decide), hout]) (b8000c2f8_x10 h₂) (Or.inr rfl)
  have m8 := b8000c2f0_m_x8_8 h₁
  rw [hout] at m8
  refine ⟨t, hr₁.trans (hr₂.trans hr), hpc', hpres, ?_, ?_, ?_,
    ((bf₁.mono (w' := (Within · (s.getReg .x10) 24)) fun a ha ↦ by addr_omega [ha, hb]).trans
      (ByteFrame.of_same (b8000c2f8_mem_same h₂) _) fun _ h ↦ h).trans hbt fun _ h ↦ h⟩
  · rw [htag, k₂ .x20 (by decide), b8000c2f0_x20 h₁]
  · rw [hfr _ (by addr_omega [hb]) (by addr_omega [hb]), b8000c2f8_mem_same h₂, m8]
  · rw [h16, k₂ .x9 (by decide), k₁ .x9 (by decide)]

theorem toNat_mul_le {a b c : Word} (hab : a.toNat ≤ b.toNat) (hc : c.toNat * b.toNat < 2 ^ 64) : (a * c).toNat = a.toNat * c.toNat := by
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt]
  calc a.toNat * c.toNat ≤ b.toNat * c.toNat := Nat.mul_le_mul_right _ hab
    _ = c.toNat * b.toNat := Nat.mul_comm _ _
    _ < 2 ^ 64 := hc

/-- **`finish_grow` meets its contract**, given `alloc`'s and `memcpy`'s. -/
theorem finish_grow_spec (hA : AllocSpec) (hC : MemcpySpec 0x800126e4) : FinishGrowSpec := by
  intro s hpc hpre
  have hb := hpre.bounds
  have hal := hpre.align
  have hsz := hpre.size
  have hheap := hpre.heap
  have hlo := hheap.lo
  have hhi := hheap.hi
  have ho := hpre.outFree
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000c224_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₁ := b8000c224_keeps h₁
  have inv₁ : Inv s t₁ (s.getMem nextAddr) := FnInv.init hheap (stack80 hpre)
    (by rw [b8000c224_x2 h₁]; rfl)
    (by
      simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      rv_eval []
      exact ⟨b8000c224_m_x2_n8 h₁, b8000c224_m_x2_n16 h₁, b8000c224_m_x2_n24 h₁,
        b8000c224_m_x2_n32 h₁, b8000c224_m_x2_n40 h₁, b8000c224_m_x2_n48 h₁,
        b8000c224_m_x2_n56 h₁, b8000c224_m_x2_n64 h₁, b8000c224_m_x2_n72 h₁⟩)
    (fun r hr ↦ k₁ r (mem_of_mem hr _))
    ((b8000c224_frame h₁ (by addr_omega [hb])).mono fun a ha ↦ by addr_omega [ha, hb])
    (h₁.unaligned (by rv_eval []; and_intros <;> addr_omega [hb])) (by decide)
  have hx8 : t₁.getReg .x8 = s.getReg .x10 := b8000c224_x8 h₁
  have hx9 : t₁.getReg .x9 = s.getReg .x15 * s.getReg .x13 := b8000c224_x9 h₁
  have hpc₁ := h₁.pc
  rv_eval [] at hpc₁
  rcases eq_ite_cases hpc₁ with ⟨hfit, hpc₁⟩ | ⟨-, hpc₁⟩
  · obtain ⟨hmul, hle⟩ := layout_ok hfit (by omega)
    obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000c284_spec hpc₁ trivial
    have k₂ := b8000c284_keeps h₂
    have inv₂ := inv₁.same hpre (b8000c284_mem_same h₂) k₂
    have hx8₂ : t₂.getReg .x8 = s.getReg .x10 := (k₂ .x8 (by decide)).trans hx8
    have hx9₂ : t₂.getReg .x9 = s.getReg .x15 * s.getReg .x13 := (k₂ .x9 (by decide)).trans hx9
    have hreg₂ (r : Reg) (hr : r ∈ [Reg.x11, .x12, .x14, .x15]) : t₂.getReg r = s.getReg r := by
      rw [k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
    have hn₂ : heapNext t₂ = heapNext s := by simp only [heapNext, inv₂.next]
    have hheap₂ : HeapOk t₂ := ⟨hn₂ ▸ hlo, hn₂ ▸ hhi⟩
    -- the end, from a pointer `p` in `s2` at `0x8000c2f0`
    have fin (u : MachineState) (nx : Word) (hu : Inv s u nx) (hpcu : u.pc = 0x8000c2f0)
        (hx8u : u.getReg .x8 = s.getReg .x10)
        (hx9u : u.getReg .x9 = s.getReg .x15 * s.getReg .x13)
        (hbuf : ∀ t, heapNext t = nx.toNat →
          NewBuf s t (u.getReg .x18) ((s.getReg .x13).toNat * (s.getReg .x15).toNat)
            (s.getReg .x14).toNat)
        (hbytes : ∀ t, ByteFrame u t (Within · (s.getReg .x10) 24) →
          bytesAt t (u.getReg .x18) ((s.getReg .x11).toNat * (s.getReg .x15).toNat) =
            bytesAt s (s.getReg .x12) ((s.getReg .x11).toNat * (s.getReg .x15).toNat)) :
        ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
          FinishGrowPost s t := by
      obtain ⟨t, hr, hpc', hpres, htag, h8, -, hbt⟩ := tail hpre hpcu hu hx8u
      obtain ⟨hnt, hheap', hmono, hframe⟩ := finish hpre hu hbt
      refine ⟨t, hr, hpc', hpres, hheap', hmono, fun _ ↦ ?_, fun h0 ↦ (h0 htag).elim, hframe⟩
      rw [h8]
      exact ⟨hbuf t (by simp only [heapNext, hnt]), hbytes t hbt⟩
    by_cases hoc : t₁.getReg .x11 = 0
    · have hoc' : (s.getReg .x11).toNat = 0 := by
        rw [← k₁ .x11 (by decide), hoc]; rfl
      have hnil (t : MachineState) (p : Word) :
          bytesAt t p ((s.getReg .x11).toNat * (s.getReg .x15).toNat) =
            bytesAt s (s.getReg .x12) ((s.getReg .x11).toNat * (s.getReg .x15).toNat) := by
        simp only [hoc', Nat.zero_mul]; rfl
      obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000c2c4_spec (b8000c284_pc_taken h₂ hoc)
        trivial
      have k₃ := b8000c2c4_keeps h₃
      have inv₃ := inv₂.same hpre (b8000c2c4_mem_same h₃) k₃
      by_cases hz : t₂.getReg .x9 = 0
      · -- no bytes: the dangling pointer
        obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000c2ec_spec (b8000c2c4_pc_taken h₃ hz)
          trivial
        have k₄ := b8000c2ec_keeps h₄
        have inv₄ := inv₃.same hpre (b8000c2ec_mem_same h₄) k₄
        have hzn : (s.getReg .x13).toNat * (s.getReg .x15).toNat = 0 := by
          have := congrArg BitVec.toNat hz
          rw [hx9₂, hmul, show (0 : Word).toNat = 0 from rfl] at this
          rw [Nat.mul_comm]; exact this
        obtain ⟨t, hr, hpost⟩ := fin t₄ _ inv₄ (b8000c2ec_pc h₄)
          (by rw [k₄ .x8 (by decide), k₃ .x8 (by decide), hx8₂])
          (by rw [k₄ .x9 (by decide), k₃ .x9 (by decide), hx9₂])
          (fun t _ ↦ by
            rw [b8000c2ec_x18 h₄, k₃ .x14 (by decide), hreg₂ .x14 (by decide)]
            simp only [NewBuf, hzn, true_or, and_true]
            exact Nat.mod_self _)
          fun t _ ↦ hnil t _
        exact ⟨t, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr))), Or.inl hpost⟩
      · -- a new buffer, nothing to copy
        obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000c2c8_spec
          (b8000c2c4_pc_not_taken h₃ hz) trivial
        have k₄ := b8000c2c8_keeps h₄
        have inv₄ := inv₃.same hpre (b8000c2c8_mem_same h₄) k₄
        have hn₄ : heapNext t₄ = heapNext s := by simp only [heapNext, inv₄.next]
        have hx10₄ : t₄.getReg .x10 = s.getReg .x14 := by
          rw [b8000c2c8_x10 h₄, k₃ .x14 (by decide), hreg₂ .x14 (by decide)]
        have hx11₄ : t₄.getReg .x11 = s.getReg .x15 * s.getReg .x13 := by
          rw [b8000c2c8_x11 h₄, k₃ .x9 (by decide), hx9₂]
        obtain ⟨t₅, hr₅, ⟨hpc₅, hpres₅, hpost⟩ | hdead⟩ :=
          hA.call hr₄ (b8000c2c8_pc h₄) ⟨⟨hn₄ ▸ hlo, hn₄ ▸ hhi⟩, by rw [hx10₄]; exact hal⟩
        swap
        · exact ⟨t₅, hr₁.trans (hr₂.trans (hr₃.trans hr₅)), Or.inr hdead⟩
        have inv₅ := inv₄.alloc hpre hpost hpres₅
        have hpal := hpost.aligned
        have habove := hpost.above
        have hnext₅ := hpost.next
        rw [hx10₄] at hpal
        rw [hx11₄, hmul, hn₄] at *
        have hp0 : t₅.getReg .x10 ≠ 0 := fun h0 ↦ by
          rw [h0, show (0 : Word).toNat = 0 from rfl] at habove
          simp only [heapStart] at hlo
          omega
        obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000c2dc_spec
          (by rw [hpc₅, returnAddress_eq, b8000c2c8_x1 h₄]; decide) trivial
        have k₆ := b8000c2dc_keeps h₆
        have inv₆ := inv₅.same hpre (b8000c2dc_mem_same h₆) k₆
        obtain ⟨t, hr, hpost'⟩ := fin t₆ _ inv₆ (b8000c2dc_pc_taken h₆ hp0)
          (by rw [k₆ .x8 (by decide), hpres₅.reg .x8, k₄ .x8 (by decide), k₃ .x8 (by decide),
            hx8₂])
          (by rw [k₆ .x9 (by decide), hpres₅.reg .x9, k₄ .x9 (by decide), k₃ .x9 (by decide),
            hx9₂])
          (fun t ht ↦ by
            rw [b8000c2dc_x18 h₆]
            simp only [NewBuf, ht]
            refine ⟨hpal, Or.inr ⟨habove, ?_⟩⟩
            simp only [heapNext] at hnext₅
            rw [hnext₅, Nat.mul_comm])
          fun t _ ↦ hnil t _
        exact ⟨t, hr₁.trans (hr₂.trans (hr₃.trans (hr₅.trans (hr₆.trans hr)))), Or.inl hpost'⟩
    · -- grow: a new buffer, the old one's bytes copied
      have hoc' : 0 < (s.getReg .x11).toNat := by
        rw [← k₁ .x11 (by decide)]
        exact Nat.pos_of_ne_zero fun h0 ↦ hoc (BitVec.eq_of_toNat_eq h0)
      have hle' := hpre.le
      have hn0 : 0 < (s.getReg .x11).toNat * (s.getReg .x15).toNat := Nat.mul_pos hoc' hsz
      have hold : heapStart ≤ (s.getReg .x12).toNat ∧
          (s.getReg .x12).toNat + (s.getReg .x11).toNat * (s.getReg .x15).toNat ≤ heapNext s := by
        rcases hpre.old.2 with h0 | h0
        · omega
        · exact h0
      have hoz : (s.getReg .x11 * s.getReg .x15).toNat =
          (s.getReg .x11).toNat * (s.getReg .x15).toNat :=
        toNat_mul_le hle' (by omega)
      obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000c288_spec (b8000c284_pc_not_taken h₂ hoc)
        trivial
      have k₃ := b8000c288_keeps h₃
      have inv₃ := inv₂.same hpre (b8000c288_mem_same h₃) k₃
      have hn₃ : heapNext t₃ = heapNext s := by simp only [heapNext, inv₃.next]
      have hx10₃ : t₃.getReg .x10 = s.getReg .x14 := by
        rw [b8000c288_x10 h₃, hreg₂ .x14 (by decide)]
      have hx11₃ : t₃.getReg .x11 = s.getReg .x15 * s.getReg .x13 := by
        rw [b8000c288_x11 h₃, hx9₂]
      obtain ⟨t₄, hr₄, ⟨hpc₄, hpres₄, hpost⟩ | hdead⟩ :=
        hA.call hr₃ (b8000c288_pc h₃) ⟨⟨hn₃ ▸ hlo, hn₃ ▸ hhi⟩, by rw [hx10₃]; exact hal⟩
      swap
      · exact ⟨t₄, hr₁.trans (hr₂.trans hr₄), Or.inr hdead⟩
      have inv₄ := inv₃.alloc hpre hpost hpres₄
      have hpal := hpost.aligned
      rw [hx10₃] at hpal
      have hP1 : heapNext s ≤ (t₄.getReg .x10).toNat := hn₃ ▸ hpost.above
      have hP2 : (t₄.getMem nextAddr).toNat =
          (t₄.getReg .x10).toNat + (s.getReg .x13).toNat * (s.getReg .x15).toNat := by
        have := hpost.next
        rw [hx11₃, hmul, Nat.mul_comm] at this
        exact this
      have hP3 : (t₄.getMem nextAddr).toNat ≤ 0x78000000 := hpost.heap.hi
      have hS : 0x20000000 ≤ heapNext s := hlo
      have hp0 : t₄.getReg .x10 ≠ 0 := fun h0 ↦ by
        rw [h0, show (0 : Word).toNat = 0 from rfl] at hP1
        omega
      obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000c2a8_spec
        (by rw [hpc₄, returnAddress_eq, b8000c288_x1 h₃]; decide) trivial
      have k₅ := b8000c2a8_keeps h₅
      have inv₅ := inv₄.same hpre (b8000c2a8_mem_same h₅) k₅
      obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000c2ac_spec
        (b8000c2a8_pc_not_taken h₅ hp0) trivial
      have k₆ := b8000c2ac_keeps h₆
      have inv₆ := inv₅.same hpre (b8000c2ac_mem_same h₆) k₆
      have hd : t₆.getReg .x10 = t₄.getReg .x10 := by rw [k₆ .x10 (by decide), k₅ .x10 (by decide)]
      have hsrc : t₆.getReg .x11 = s.getReg .x12 := by
        rw [b8000c2ac_x11 h₆, k₅ .x19 (by decide), hpres₄.reg .x19, b8000c288_x19 h₃,
          hreg₂ .x12 (by decide)]
      have hlen : t₆.getReg .x12 = s.getReg .x11 * s.getReg .x15 := by
        rw [b8000c2ac_x12 h₆, k₅ .x23 (by decide), k₅ .x22 (by decide), hpres₄.reg .x23,
          hpres₄.reg .x22, b8000c288_x23 h₃, b8000c288_x22 h₃, hreg₂ .x11 (by decide),
          hreg₂ .x15 (by decide)]
      have hsp₆ : t₆.getReg .x2 = s.getReg .x2 - 80 := inv₆.saved.1
      have hcopy : (s.getReg .x11).toNat * (s.getReg .x15).toNat ≤
          (s.getReg .x13).toNat * (s.getReg .x15).toNat := Nat.mul_le_mul_right _ hle'
      have hst := hpre.stack
      have hab := hst.above
      have hold' := hold
      simp only [heapStart] at hold'
      have hsl : stackLo t₆ memcpyStack = s.getReg .x2 - 96 := by
        simp only [stackLo, hsp₆, memcpyStack]
        rw [Sym.sub_sub_lit]; rfl
      have hpre₆ : MemcpyPre t₆ := {
        dst := by rw [hd, hlen, hoz]; simp only [Mapped]; omega
        src := by rw [hsrc, hlen, hoz]; simp only [Mapped]; omega
        apart := by rw [hd, hsrc, hlen, hoz]; simp only [Apart]; omega
        stack := ⟨by
          rw [hsl]
          exact ValidMemRange.sub hst.valid (by addr_omega [hb]) (by addr_omega [hb])
            (by addr_omega [hb]), by rw [hsp₆]; addr_omega [hb]⟩
        dstStack := by rw [hd, hlen, hoz, hsl]; addr_omega [hb, hab, hP1, hP2, hP3, hcopy]
        srcStack := by rw [hsrc, hlen, hoz, hsl]; addr_omega [hb, hab, hold', hS, hhi] }
      obtain ⟨t₇, hr₇, ⟨hpc₇, hpres₇, hcp⟩ | hdead⟩ := hC.call hr₆ (b8000c2ac_pc h₆) hpre₆
      swap
      · exact ⟨t₇, hr₁.trans (hr₂.trans (hr₄.trans (hr₅.trans hr₇))), Or.inr hdead⟩
      have hcf := hcp.frame
      have hcb := hcp.bytes
      rw [hd, hlen, hoz, hsl] at hcf
      rw [hd, hsrc, hlen, hoz] at hcb
      have hnx8 := hst.next
      have inv₇ := inv₆.step hpre hcf (fun a ha ↦ by
          rcases ha with ha | ha
          · exact Or.inr (Or.inr ⟨by simp only [Within] at ha; omega,
              by simp only [Within] at ha; omega⟩)
          · exact Or.inl (Or.inr (by addr_omega [ha, hb])))
        ((hcf.getMem fun i hi ha ↦ by
          rcases ha with ha | ha
          · addr_omega [ha, hi, hP2, hP3, hcopy]
          · addr_omega [ha, hi, hnx8, hb]).trans inv₆.next)
        (Nat.le_refl _) inv₆.fits fun r hr ↦ hpres₇ r (mem_of_mem hr _)
      obtain ⟨t₈, hr₈, h₈⟩ := Sym.BlockSpec.reaches b8000c2c0_spec
        (by rw [hpc₇, returnAddress_eq, b8000c2ac_x1 h₆]; decide) trivial
      have k₈ := b8000c2c0_keeps h₈
      have inv₈ := inv₇.same hpre (b8000c2c0_mem_same h₈) k₈
      have hx18 : t₈.getReg .x18 = t₄.getReg .x10 := by
        rw [k₈ .x18 (by decide), hpres₇.reg .x18, b8000c2ac_x18 h₆, k₅ .x10 (by decide)]
      obtain ⟨t, hr, hpost'⟩ := fin t₈ _ inv₈ (b8000c2c0_pc h₈)
        (by rw [k₈ .x8 (by decide), hpres₇.reg .x8, k₆ .x8 (by decide), k₅ .x8 (by decide),
          hpres₄.reg .x8, k₃ .x8 (by decide), hx8₂])
        (by rw [k₈ .x9 (by decide), hpres₇.reg .x9, k₆ .x9 (by decide), k₅ .x9 (by decide),
          hpres₄.reg .x9, k₃ .x9 (by decide), hx9₂])
        (fun t ht ↦ by
          rw [hx18]
          simp only [NewBuf, ht]
          exact ⟨hpal, Or.inr ⟨hP1, hP2.ge⟩⟩)
        fun t hbt ↦ by
          have hoo := hpre.outOld
          have hm6 := inv₆.mem
          rw [hx18, hbt.bytesAt fun i hi ha ↦ by addr_omega [ha, hi, ho, hP1, hP2, hP3, hcopy, hb],
            (ByteFrame.of_same (b8000c2c0_mem_same h₈) fun _ ↦ False).bytesAt fun _ _ h ↦ h, hcb]
          refine hm6.bytesAt fun i hi ha ↦ ?_
          simp only [W] at ha
          rcases ha with (ha | ha) | ha | ha | ha
          · addr_omega [ha, hi, hoo, hb, hold', hhi]
          · addr_omega [ha, hi, hold', hab, hb, hhi]
          · addr_omega [ha, hi, hold', hab, hb, hhi]
          · addr_omega [ha, hi, hold', hhi]
          · addr_omega [ha.1, hi, hold', hhi]
      exact ⟨t, hr₁.trans (hr₂.trans (hr₄.trans (hr₅.trans (hr₇.trans (hr₈.trans hr))))),
        Or.inl hpost'⟩
  · -- `Err(CapacityOverflow)`
    obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000c278_spec hpc₁ trivial
    have k₂ := b8000c278_keeps h₂
    have inv₂ := inv₁.same hpre (b8000c278_mem_same h₂) k₂
    obtain ⟨t, hr, hpc', hpres, htag, h8, -, hbt⟩ := exit hpre (b8000c278_pc h₂) inv₂
      (by rw [k₂ .x8 (by decide), hx8]) (b8000c278_x10 h₂) (Or.inl rfl)
    obtain ⟨-, hheap', hmono, hframe⟩ := finish hpre inv₂ hbt
    refine ⟨t, hr₁.trans (hr₂.trans hr), Or.inl ⟨hpc', hpres, hheap', hmono, fun h0 ↦ ?_,
      fun _ ↦ by rw [h8, b8000c278_x9 h₂], hframe⟩⟩
    rw [htag, k₂ .x20 (by decide), b8000c224_x20 h₁] at h0
    cases h0

end Rv64Verifier.Runtime.FinishGrow
