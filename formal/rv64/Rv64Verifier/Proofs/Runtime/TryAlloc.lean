import Rv64Verifier.Proofs.Runtime.Contracts
import Rv64Verifier.Blocks.F0

/-!
# `RawVecInner::try_allocate_in` (uninitialized), at `0x80000024`

```rust
let layout = layout_array(capacity, elem_layout)?;      // else Err(CapacityOverflow)
if layout.size() == 0 { return Ok(Self::new_in(alloc, elem_layout.alignment())); }
let ptr = alloc.allocate(layout)?;                        // else Err(AllocError { layout })
Ok(Self { ptr, cap: capacity, alloc })
```

compiled (`Blocks/F0.lean`): `0x80000024` saves `ra`, `s0`..`s3` in a 48-byte frame, computes
`size * capacity` and branches on the overflow check; `0x80000060`, `0x80000064` write the
`CapacityOverflow` error; `0x8000006c` branches on a zero size to `0x800000a8` (`Ok`, capacity 0,
the dangling pointer `align`), else `0x80000070` calls `alloc`, `0x8000008c` branches on a null
pointer (never: `alloc` halts instead) and `0x80000090` writes the capacity and the pointer.
`0x800000b4` writes the tag, restores and returns.
-/

namespace Rv64Verifier.Runtime.TryAlloc
open RiscvZkvm.Rv64 Rv64Verifier.Blocks.F0
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The callee-saved registers the function never touches. -/
def kept : List Reg := [.x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

theorem mem_of_kept {r : Reg} (h : r ∈ kept) (l : List Reg)
    (hl : ∀ r ∈ kept, r ∈ l := by decide) : r ∈ l :=
  hl r h

/-- Inside the 48-byte frame: the saved registers, `NEXT = nx`, and memory changed only in the
result, the frame and `NEXT`. -/
structure Inv (s u : MachineState) (nx : Word) : Prop where
  sp : u.getReg .x2 = s.getReg .x2 - 48
  kept : ∀ r ∈ kept, u.getReg r = s.getReg r
  ra : u.getMem (s.getReg .x2 - 8) = s.getReg .x1
  s0 : u.getMem (s.getReg .x2 - 16) = s.getReg .x8
  s1 : u.getMem (s.getReg .x2 - 24) = s.getReg .x9
  s2 : u.getMem (s.getReg .x2 - 32) = s.getReg .x18
  s3 : u.getMem (s.getReg .x2 - 40) = s.getReg .x19
  mem : ∀ a, ¬ Within a (s.getReg .x10) 24 → ¬ Within a (stackLo s 48) 48 → a ≠ nextAddr →
    u.getMem a = s.getMem a
  unaligned : ∀ a, a.toNat % 8 ≠ 0 → u.getMem a = s.getMem a
  next : u.getMem nextAddr = nx

/-- `sp` and the result as numbers. -/
theorem _root_.Rv64Verifier.Runtime.TryAllocPre.bounds {al sz : Reg} {s : MachineState}
    (h : TryAllocPre al sz s) :
    0x78000030 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ (s.getReg .x10).toNat % 8 = 0 ∧
      (s.getReg .x10).toNat + 24 ≤ 0xc0000008 := by
  have := h.stack.bounds (by decide) (by decide)
  have ha := h.stack.above
  have ho := ValidMemRange.bounds h.out (by decide)
  simp only [tryAllocStack, stackLo, heapEnd] at this ha
  rw [this.2.2.2] at ha
  omega

/-- A step that writes only the result and `NEXT` and keeps `sp` and the untouched registers. -/
theorem Inv.step {s u v : MachineState} {nx nx' : Word} (hpre : TryAllocPre .x12 .x13 s)
    (h : Inv s u nx) (hm : ∀ a, ¬ Within a (s.getReg .x10) 24 → a ≠ nextAddr → v.getMem a = u.getMem a)
    (hu : ∀ a, a.toNat % 8 ≠ 0 → v.getMem a = u.getMem a) (hnx : v.getMem nextAddr = nx')
    (hr : ∀ r ∈ [Reg.x2, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27], v.getReg r = u.getReg r) :
    Inv s v nx' := by
  have hb := hpre.bounds
  have hs := hpre.outStack
  have hn := hpre.stack.next
  have hm' (a : Word) (h1 : (s.getReg .x2).toNat - 40 ≤ a.toNat) (h2 : a.toNat < (s.getReg .x2).toNat) :
      v.getMem a = u.getMem a :=
    hm a (by addr_omega [h1, h2, hb, hs]) (by addr_omega [h1, h2, hb, hn])
  exact {
    sp := (hr _ (by decide)).trans h.sp
    kept := fun r hr' ↦ (hr r (mem_of_kept hr' _)).trans (h.kept r hr')
    ra := (hm' _ (by addr_omega [hb]) (by addr_omega [hb])).trans h.ra
    s0 := (hm' _ (by addr_omega [hb]) (by addr_omega [hb])).trans h.s0
    s1 := (hm' _ (by addr_omega [hb]) (by addr_omega [hb])).trans h.s1
    s2 := (hm' _ (by addr_omega [hb]) (by addr_omega [hb])).trans h.s2
    s3 := (hm' _ (by addr_omega [hb]) (by addr_omega [hb])).trans h.s3
    mem := fun a h1 h2 h3 ↦ (hm a h1 h3).trans (h.mem a h1 h2 h3)
    unaligned := fun a ha ↦ (hu a ha).trans (h.unaligned a ha)
    next := hnx }

/-- A step that writes only the result. -/
theorem Inv.of_out {s u v : MachineState} {nx : Word} (hpre : TryAllocPre .x12 .x13 s)
    (h : Inv s u nx) (hm : ∀ a, ¬ Within a (s.getReg .x10) 24 → v.getMem a = u.getMem a)
    (hu : ∀ a, a.toNat % 8 ≠ 0 → v.getMem a = u.getMem a)
    (hr : ∀ r ∈ [Reg.x2, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27], v.getReg r = u.getReg r) :
    Inv s v nx := by
  have hb := hpre.bounds
  have ho := hpre.outFree
  exact h.step hpre (fun a h1 _ ↦ hm a h1) hu
    ((hm _ (by addr_omega [ho, hb])).trans h.next) hr

/-- The epilogue: the tag `a3` to the result, the registers restored, return. -/
theorem exit {s u : MachineState} {nx : Word} (hpre : TryAllocPre .x12 .x13 s) (hpc : u.pc = 0x800000b4)
    (h : Inv s u nx) (hout : u.getReg .x10 = s.getReg .x10) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      t.getMem (s.getReg .x10) = u.getReg .x13 ∧ MemFrame u t (s.getReg .x10) 8 ∧
      ∀ a, a.toNat % 8 ≠ 0 → t.getMem a = u.getMem a := by
  have hb := hpre.bounds
  have hs := hpre.outStack
  simp only [tryAllocStack] at hs
  obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b800000b4_spec hpc (by
    rv_eval [h.sp, hout]
    and_intros <;> first
      | addr_omega [hb, hs]
      | valid_access hpre.stack.valid [hb]
      | valid_access hpre.out [hb])
  have k := b800000b4_keeps ht
  have hm := b800000b4_frame ht (by rw [hout]; addr_omega [hb])
  rw [hout] at hm
  have pc := b800000b4_pc ht
  have x2 := b800000b4_x2 ht
  have x8 := b800000b4_x8 ht
  have x9 := b800000b4_x9 ht
  have x18 := b800000b4_x18 ht
  have x19 := b800000b4_x19 ht
  have m := b800000b4_m_x10_0 ht
  rv_eval [h.sp, h.ra, h.s0, h.s1, h.s2, h.s3, hout] at pc x2 x8 x9 x18 x19 m
  refine ⟨t, hr, pc.trans (returnAddress_eq s).symm, preserves_of x2 x8 x9 x18 x19
    fun r hr' ↦ (k r (mem_of_kept hr' _)).trans (h.kept r hr'), m, hm,
    ht.unaligned (by rv_eval [hout]; addr_omega [hb])⟩

/-- What the function's end shares: the heap, the frame, and the result's fields. -/
theorem finish {s u t : MachineState} {nx : Word} (hpre : TryAllocPre .x12 .x13 s)
    (h : Inv s u nx) (hheap : HeapOk u) (hmono : heapNext s ≤ heapNext u)
    (hm : MemFrame u t (s.getReg .x10) 8) (hu : ∀ a, a.toNat % 8 ≠ 0 → t.getMem a = u.getMem a)
    (hok : t.getMem (s.getReg .x10) = 0 → u.getMem (s.getReg .x10 + 8) = s.getReg .x11 ∧
      NewBuf s u (u.getMem (s.getReg .x10 + 16)) ((s.getReg .x11).toNat * (s.getReg .x13).toNat)
        (s.getReg .x12).toNat)
    (hdang : t.getMem (s.getReg .x10) = 0 → s.getReg .x11 = 0 →
      u.getMem (s.getReg .x10 + 16) = s.getReg .x12) :
    TryAllocPost .x12 .x13 s t := by
  have hb := hpre.bounds
  have ho := hpre.outFree
  have hn : t.getMem nextAddr = u.getMem nextAddr := hm _ (by addr_omega [ho, hb])
  have hnext : heapNext t = heapNext u := by simp only [heapNext, hn]
  have h8 : t.getMem (s.getReg .x10 + 8) = u.getMem (s.getReg .x10 + 8) := hm _ (by addr_omega [hb])
  have h16 : t.getMem (s.getReg .x10 + 16) = u.getMem (s.getReg .x10 + 16) :=
    hm _ (by addr_omega [hb])
  refine ⟨⟨hnext ▸ hheap.lo, hnext ▸ hheap.hi⟩, hnext ▸ hmono, fun h0 ↦ ?_, ?_,
    fun h0 hc ↦ h16.trans (hdang h0 hc)⟩
  · obtain ⟨hc, hp⟩ := hok h0
    refine ⟨by rw [h8, hc], ?_⟩
    rw [h16]
    simpa only [NewBuf, hnext] using hp
  · refine (ByteFrame.of_dwords (w := fun a ↦ Within a (s.getReg .x10) 24 ∨
      Within a (stackLo s tryAllocStack) tryAllocStack ∨ Within a nextAddr 8) ?_ ?_ ?_).mono ?_
    · intro a _ ha
      simp only [not_or] at ha
      exact (hm a fun h' ↦ ha.1 (by addr_omega [h', hb])).trans
        (h.mem a ha.1 ha.2.1 fun h' ↦ ha.2.2 (by addr_omega [h']))
    · exact fun a ha ↦ (hu a ha).trans (h.unaligned a ha)
    · have hsp := hpre.stack.aligned
      intro a ha
      rcases ha with ha | ha | ha
      · exact Or.inl (within_of_alignDown (by addr_omega [hb]) (by decide) ha)
      · exact Or.inr (Or.inl (within_of_alignDown (by addr_omega [hb]) (by decide) ha))
      · exact Or.inr (Or.inr (within_of_alignDown (by decide) (by decide) ha))
    · intro a ha
      rcases ha with ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))

/-- **`try_allocate_in` meets its contract**, given `alloc`'s. -/
theorem try_alloc_spec (hA : AllocSpec) : TryAllocSpec := by
  intro s hpc hpre
  have hb := hpre.bounds
  have hal := hpre.align
  have hsz := hpre.size
  have ho := hpre.outFree
  have hsn := hpre.stack.next
  have hheap := hpre.heap
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80000024_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₁ := b80000024_keeps h₁
  have hm₁ := b80000024_frame h₁ (by addr_omega [hb])
  have inv₁ : Inv s t₁ (s.getMem nextAddr) := {
    sp := b80000024_x2 h₁
    kept := fun r hr ↦ k₁ r (mem_of_kept hr _)
    ra := b80000024_m_x2_n8 h₁
    s0 := b80000024_m_x2_n16 h₁
    s1 := b80000024_m_x2_n24 h₁
    s2 := b80000024_m_x2_n32 h₁
    s3 := b80000024_m_x2_n40 h₁
    mem := fun a _ h2 _ ↦ hm₁ a (by addr_omega [h2, hb])
    unaligned := h₁.unaligned (by rv_eval []; and_intros <;> addr_omega [hb])
    next := hm₁ _ (by addr_omega [hsn, hb]) }
  have hpc₁ := h₁.pc
  rv_eval [] at hpc₁
  rcases eq_ite_cases hpc₁ with ⟨hfit, hpc₁⟩ | ⟨-, hpc₁⟩
  · -- the size fits
    obtain ⟨hmul, hle⟩ := layout_ok hfit (by omega)
    obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000006c_spec hpc₁ trivial
    have k₂ := b8000006c_keeps h₂
    have inv₂ := inv₁.of_out hpre (fun a _ ↦ b8000006c_mem_same h₂ a)
      (fun a _ ↦ b8000006c_mem_same h₂ a) fun r hr ↦ k₂ r (mem_of_mem hr _)
    have hx8 : t₁.getReg .x8 = s.getReg .x13 * s.getReg .x11 := b80000024_x8 h₁
    by_cases hz : t₁.getReg .x8 = 0
    · -- no bytes: `Ok`, capacity 0, the dangling pointer
      obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800000a8_spec (b8000006c_pc_taken h₂ hz) (by
        rv_eval [k₂ .x10 (by decide), k₁ .x10 (by decide)]
        and_intros <;> valid_access hpre.out [hb])
      have k₃ := b800000a8_keeps h₃
      have hx10 : t₂.getReg .x10 = s.getReg .x10 := by rw [k₂ .x10 (by decide), k₁ .x10 (by decide)]
      have hm₃ := b800000a8_frame h₃ (by rw [hx10]; addr_omega [hb])
      rw [hx10] at hm₃
      have inv₃ := inv₂.of_out hpre (fun a ha ↦ hm₃ a (by addr_omega [ha, hb]))
        (h₃.unaligned (by rv_eval [hx10]; and_intros <;> addr_omega [hb]))
        fun r hr ↦ k₃ r (mem_of_mem hr _)
      obtain ⟨t, hr, hpc', hpres, htag, hmt, hut⟩ := exit hpre (b800000a8_pc h₃) inv₃
        (by rw [k₃ .x10 (by decide), hx10])
      refine ⟨t, hr₁.trans (hr₂.trans (hr₃.trans hr)), Or.inl ⟨hpc', hpres, ?_⟩⟩
      have hn₃ : heapNext t₃ = heapNext s := by simp only [heapNext, inv₃.next]
      have m8 := b800000a8_m_x10_8 h₃
      have m16 := b800000a8_m_x10_16 h₃
      rw [hx10] at m8 m16
      rw [k₂ .x12 (by decide), k₁ .x12 (by decide)] at m16
      refine finish hpre inv₃ ⟨hn₃ ▸ hheap.lo, hn₃ ▸ hheap.hi⟩ hn₃.ge hmt hut (fun _ ↦ ?_)
        fun _ _ ↦ m16
      · rw [hx8] at hz
        have hc : (s.getReg .x11).toNat = 0 := by
          have := congrArg BitVec.toNat hz
          rw [hmul, show (0 : Word).toNat = 0 from rfl] at this
          rcases Nat.mul_eq_zero.mp this with h | h
          · omega
          · exact h
        refine ⟨by rw [m8]; exact (BitVec.eq_of_toNat_eq (by simp [hc])), ?_⟩
        rw [m16]
        simp only [NewBuf, hc, Nat.zero_mul, true_or, and_true]
        exact Nat.mod_self _
    · -- allocate
      obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80000070_spec
        (b8000006c_pc_not_taken h₂ hz) trivial
      have k₃ := b80000070_keeps h₃
      have inv₃ := inv₂.of_out hpre (fun a _ ↦ b80000070_mem_same h₃ a)
        (fun a _ ↦ b80000070_mem_same h₃ a) fun r hr ↦ k₃ r (mem_of_mem hr _)
      have hx10 : t₃.getReg .x10 = s.getReg .x12 := by
        rw [b80000070_x10 h₃, k₂ .x12 (by decide), k₁ .x12 (by decide)]
      have hx11 : t₃.getReg .x11 = s.getReg .x13 * s.getReg .x11 := by
        rw [b80000070_x11 h₃, k₂ .x8 (by decide), hx8]
      have hheap₃ : HeapOk t₃ := ⟨by simp only [heapNext, inv₃.next]; exact hheap.lo,
        by simp only [heapNext, inv₃.next]; exact hheap.hi⟩
      obtain ⟨t₄, hr₄, ⟨hpc₄, hpres₄, hpost⟩ | hdead⟩ :=
        hA.call hr₃ (b80000070_pc h₃) ⟨hheap₃, by rw [hx10]; exact hal⟩
      swap
      · exact ⟨t₄, hr₁.trans (hr₂.trans hr₄), Or.inr hdead⟩
      have hpal := hpost.aligned
      rw [hx10] at hpal
      have hp0 : t₄.getReg .x10 ≠ 0 := by
        intro h0
        have h1 := hpost.above
        have h2 := hheap₃.lo
        rw [h0, show (0 : Word).toNat = 0 from rfl] at h1
        simp only [heapStart] at h2
        omega
      have inv₄ := inv₃.step hpre (fun a _ ha ↦ hpost.mem a ha)
        (fun a ha ↦ hpost.mem a fun h' ↦ ha (by rw [h']; decide)) rfl
        fun r hr ↦ hpres₄ r (mem_of_mem hr _)
      obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000008c_spec
        (by rw [hpc₄, returnAddress_eq, b80000070_x1 h₃]; decide) trivial
      have k₅ := b8000008c_keeps h₅
      have inv₅ := inv₄.of_out hpre (fun a _ ↦ b8000008c_mem_same h₅ a)
        (fun a _ ↦ b8000008c_mem_same h₅ a) fun r hr ↦ k₅ r (mem_of_mem hr _)
      have hx18 : t₅.getReg .x18 = s.getReg .x10 := by
        rw [k₅ .x18 (by decide), hpres₄.reg .x18, b80000070_x18 h₃, k₂ .x10 (by decide),
          k₁ .x10 (by decide)]
      have hx9 : t₅.getReg .x9 = s.getReg .x11 := by
        rw [k₅ .x9 (by decide), hpres₄.reg .x9, b80000070_x9 h₃, k₂ .x11 (by decide),
          k₁ .x11 (by decide)]
      obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b80000090_spec
        (b8000008c_pc_not_taken h₅ hp0) (by
          rv_eval [hx18]
          and_intros <;> valid_access hpre.out [hb])
      have k₆ := b80000090_keeps h₆
      have hm₆ := b80000090_frame h₆ (by rw [hx18]; addr_omega [hb])
      rw [hx18] at hm₆
      have inv₆ := inv₅.of_out hpre (fun a ha ↦ hm₆ a (by addr_omega [ha, hb]))
        (h₆.unaligned (by rv_eval [hx18]; and_intros <;> addr_omega [hb]))
        fun r hr ↦ k₆ r (mem_of_mem hr _)
      obtain ⟨t, hr, hpc', hpres, htag, hmt, hut⟩ := exit hpre (b80000090_pc h₆) inv₆
        (by rw [b80000090_x10 h₆, hx18])
      refine ⟨t, hr₁.trans (hr₂.trans (hr₄.trans (hr₅.trans (hr₆.trans hr)))),
        Or.inl ⟨hpc', hpres, ?_⟩⟩
      have hn₆ : heapNext t₆ = heapNext t₄ := by simp only [heapNext, inv₆.next]
      have hn₃ : heapNext t₃ = heapNext s := by simp only [heapNext, inv₃.next]
      have hmono : heapNext s ≤ heapNext t₆ := by
        have := hpost.above
        have := hpost.next
        omega
      refine finish hpre inv₆ ⟨hn₆ ▸ hpost.heap.lo, hn₆ ▸ hpost.heap.hi⟩ hmono hmt hut (fun _ ↦ ?_)
        fun _ hc ↦ (hz (by rw [hx8, hc]; simp)).elim
      have m8 := b80000090_m_x18_8 h₆
      have m16 := b80000090_m_x18_16 h₆
      rw [hx18, hx9] at m8
      rw [hx18, k₅ .x10 (by decide)] at m16
      refine ⟨m8, ?_⟩
      rw [m16]
      refine ⟨hpal, Or.inr ⟨?_, ?_⟩⟩
      · have := hpost.above
        omega
      · rw [hn₆, hpost.next, hx11, hmul, Nat.mul_comm]
  · -- the size overflows: `Err(CapacityOverflow)`
    obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80000060_spec hpc₁ (by
      rv_eval [k₁ .x10 (by decide)]
      valid_access hpre.out [hb])
    have k₂ := b80000060_keeps h₂
    have hx10 : t₁.getReg .x10 = s.getReg .x10 := k₁ .x10 (by decide)
    have hm₂ := b80000060_frame h₂ (by rw [hx10]; addr_omega [hb])
    rw [hx10] at hm₂
    have inv₂ := inv₁.of_out hpre (fun a ha ↦ hm₂ a (by addr_omega [ha, hb]))
      (h₂.unaligned (by rv_eval [hx10]; addr_omega [hb])) fun r hr ↦ k₂ r (mem_of_mem hr _)
    obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80000064_spec (b80000060_pc h₂) trivial
    have k₃ := b80000064_keeps h₃
    have inv₃ := inv₂.of_out hpre (fun a _ ↦ b80000064_mem_same h₃ a)
      (fun a _ ↦ b80000064_mem_same h₃ a) fun r hr ↦ k₃ r (mem_of_mem hr _)
    obtain ⟨t, hr, hpc', hpres, htag, hmt, hut⟩ := exit hpre (b80000064_pc h₃) inv₃
      (by rw [k₃ .x10 (by decide), k₂ .x10 (by decide), hx10])
    refine ⟨t, hr₁.trans (hr₂.trans (hr₃.trans hr)), Or.inl ⟨hpc', hpres, ?_⟩⟩
    have hn₃ : heapNext t₃ = heapNext s := by simp only [heapNext, inv₃.next]
    refine finish hpre inv₃ ⟨hn₃ ▸ hheap.lo, hn₃ ▸ hheap.hi⟩ hn₃.ge hmt hut (fun h0 ↦ ?_)
      fun h0 _ ↦ ?_ <;> (rw [htag, b80000064_x13 h₃] at h0; cases h0)

end Rv64Verifier.Runtime.TryAlloc
