import Rv64Verifier.Proofs.Runtime.Inv
import Rv64Verifier.Proofs.Runtime.TryAlloc
import Rv64Verifier.Blocks.F7

/-!
# `RawVecInner::try_allocate_in`, at `0x800049ac`

As at `0x80000024` (`TryAlloc.lean`), with `a2` choosing `allocate_zeroed`: compiled
(`Blocks/F7.lean`), `0x800049ac` saves `ra`, `s0`..`s4` in a 48-byte frame (`s0` = the result) and
branches on the overflow check; `0x800049f0`, `0x800049f4` write the overflow error;
`0x800049fc` branches on a zero size to `0x80004a40` (`Ok`, capacity 0, the pointer `align`);
`0x80004a00` calls `alloc`; `0x80004a1c` branches on `a2`: zero goes to `0x80004a50` (a null
check, never taken) and `0x80004a54`, which writes the capacity and the pointer; otherwise
`0x80004a20` (the null check), `0x80004a24` calls `memset(ptr, 0, size)` and `0x80004a38` joins
`0x80004a54`. `0x80004a60` writes the tag, restores and returns.
-/

namespace Rv64Verifier.Runtime.TryAllocZeroed
open RiscvZkvm.Rv64 Rv64Verifier.Blocks.F7
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

def slots : List (Nat × Reg) := [(8, .x1), (16, .x8), (24, .x9), (32, .x18), (40, .x19), (48, .x20)]

def kept : List Reg := [.x21, .x22, .x23, .x24, .x25, .x26, .x27]

abbrev Inv (s u : MachineState) (nx : Word) : Prop :=
  FnInv s u 48 slots kept (fun a ↦ Within a (s.getReg .x10) 24) nx

abbrev Pre := TryAllocPre .x13 .x14

/-- A step whose writes stay in the result, `NEXT` and the heap allocated since entry. -/
theorem Inv.step {s u v : MachineState} {nx nx' : Word} {W : Word → Prop} (hpre : Pre s)
    (h : Inv s u nx) (hW : ByteFrame u v W)
    (hWsub : ∀ a, W a → Within a (s.getReg .x10) 24 ∨ Within a nextAddr 8 ∨
      (heapNext s ≤ a.toNat ∧ a.toNat < nx'.toNat))
    (hnx : v.getMem nextAddr = nx') (hle : nx.toNat ≤ nx'.toNat) (hend : nx'.toNat ≤ heapEnd)
    (hr : ∀ r ∈ [Reg.x2, .x21, .x22, .x23, .x24, .x25, .x26, .x27], v.getReg r = u.getReg r) :
    Inv s v nx' := by
  have hb := hpre.bounds
  have hs := hpre.outStack
  exact FnInv.step h hpre.stack (by decide) (Nat.le_refl _) (by decide)
    (fun a ha ha' ↦ by addr_omega [ha, ha', hs, hb]) hW hWsub hnx hle hend (hr _ (by decide))
    fun r hr' ↦ hr r (mem_of_mem hr' _)

/-- A block that writes only the result, or nothing. -/
theorem Inv.out {s u v : MachineState} {nx : Word} {W : Word → Prop} (hpre : Pre s)
    (h : Inv s u nx) (hW : ByteFrame u v W) (hWsub : ∀ a, W a → Within a (s.getReg .x10) 24)
    (hr : ∀ r ∈ [Reg.x2, .x21, .x22, .x23, .x24, .x25, .x26, .x27], v.getReg r = u.getReg r) :
    Inv s v nx := by
  have hb := hpre.bounds
  have ho := hpre.outFree
  have hnx : v.getMem nextAddr = nx :=
    (hW.getMem fun i hi hw ↦ by have := hWsub _ hw; addr_omega [this, ho, hi, hb]).trans h.next
  exact h.step hpre hW (fun a ha ↦ Or.inl (hWsub a ha)) hnx (Nat.le_refl _) h.fits hr

/-- A call to `alloc`. -/
theorem Inv.alloc {s u v : MachineState} {nx : Word} (hpre : Pre s) (h : Inv s u nx)
    (hpost : AllocPost u v) (hres : Preserves u v) : Inv s v (v.getMem nextAddr) := by
  have h1 := hpost.above
  have h2 := hpost.next
  have h3 := hpost.heap.hi
  have hn : heapNext u = nx.toNat := by simp only [heapNext, h.next]
  exact h.step hpre hpost.byteFrame (fun a ha ↦ Or.inr (Or.inl ha)) rfl
    (by simp only [heapNext] at h1 h2 hn; omega) (by simpa only [heapNext] using h3)
    fun r hr ↦ hres r (mem_of_mem hr _)

/-- The saved registers, in `rv_eval`'s form. -/
theorem Inv.saved {s u : MachineState} {nx : Word} (h : Inv s u nx) :
    u.getReg .x2 = s.getReg .x2 - 48 ∧ u.getMem (s.getReg .x2 - 8) = s.getReg .x1 ∧
      u.getMem (s.getReg .x2 - 16) = s.getReg .x8 ∧ u.getMem (s.getReg .x2 - 24) = s.getReg .x9 ∧
      u.getMem (s.getReg .x2 - 32) = s.getReg .x18 ∧
      u.getMem (s.getReg .x2 - 40) = s.getReg .x19 ∧ u.getMem (s.getReg .x2 - 48) = s.getReg .x20 := by
  have hsp := h.sp
  have sl := h.slots
  simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true] at sl
  rv_eval [] at hsp sl
  exact ⟨hsp, sl⟩

/-- The epilogue: the tag `a1` to the result, the registers restored, return. -/
theorem exit {s u : MachineState} {nx : Word} (hpre : Pre s) (hpc : u.pc = 0x80004a60)
    (h : Inv s u nx) (hout : u.getReg .x8 = s.getReg .x10) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      t.getMem (s.getReg .x10) = u.getReg .x11 ∧ MemFrame u t (s.getReg .x10) 8 ∧
      ByteFrame u t (Within · (s.getReg .x10) 8) := by
  have hb := hpre.bounds
  have hs := hpre.outStack
  obtain ⟨hsp, sl1, sl2, sl3, sl4, sl5, sl6⟩ := h.saved
  obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b80004a60_spec hpc (by
    rv_eval [hsp, hout]
    and_intros <;> first
      | addr_omega [hb, hs]
      | valid_access hpre.stack.valid [hb]
      | valid_access hpre.out [hb])
  have k := b80004a60_keeps ht
  have hm := b80004a60_frame ht (by rw [hout]; addr_omega [hb])
  rw [hout] at hm
  have pc := b80004a60_pc ht
  have x2 := b80004a60_x2 ht
  have x8 := b80004a60_x8 ht
  have x9 := b80004a60_x9 ht
  have x18 := b80004a60_x18 ht
  have x19 := b80004a60_x19 ht
  have x20 := b80004a60_x20 ht
  have m := b80004a60_m_x8_0 ht
  rv_eval [hsp, sl1, sl2, sl3, sl4, sl5, sl6, hout] at pc x2 x8 x9 x18 x19 x20 m
  have hu := ht.unaligned (by rv_eval [hout]; addr_omega [hb])
  refine ⟨t, hr, pc.trans (returnAddress_eq s).symm, preserves_of x2 x8 x9 x18 x19 fun r hr' ↦ ?_,
    m, hm, (ByteFrame.of_memFrame hm (by addr_omega [hb]) (by decide) hu)⟩
  rcases List.mem_cons.mp hr' with rfl | hr'
  · exact x20
  · exact (k r (mem_of_mem hr' _)).trans (h.kept r hr')

/-- The heap and the frame at the end. -/
theorem finish {s u t : MachineState} {nx : Word} (hpre : Pre s) (h : Inv s u nx)
    (hm : MemFrame u t (s.getReg .x10) 8) (hW : ByteFrame u t (Within · (s.getReg .x10) 8)) :
    HeapOk t ∧ heapNext s ≤ heapNext t ∧ heapNext t = nx.toNat ∧
      ByteFrame s t fun a ↦ Within a (s.getReg .x10) 24 ∨
        Within a (stackLo s tryAllocStack) tryAllocStack ∨ Within a nextAddr 8 ∨ Fresh s t a := by
  have hb := hpre.bounds
  have ho := hpre.outFree
  have hn : t.getMem nextAddr = nx := (hm _ (by addr_omega [ho, hb])).trans h.next
  have hnext : heapNext t = nx.toNat := by simp only [heapNext, hn]
  have hlo := hpre.heap.lo
  refine ⟨⟨by have := h.mono; omega, by have := h.fits; omega⟩, by have := h.mono; omega, hnext,
    h.frame hW (fun a ha ↦ by addr_omega [ha]) hn⟩

/-- From `0x80004a54`: the capacity `s3` and the pointer `a0` to the result, `Ok`, return. -/
theorem tail {s u : MachineState} {nx : Word} (hpre : Pre s) (hpc : u.pc = 0x80004a54)
    (h : Inv s u nx) (hout : u.getReg .x8 = s.getReg .x10) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      t.getMem (s.getReg .x10) = 0 ∧ t.getMem (s.getReg .x10 + 8) = u.getReg .x19 ∧
      t.getMem (s.getReg .x10 + 16) = u.getReg .x10 ∧ HeapOk t ∧ heapNext s ≤ heapNext t ∧
      heapNext t = nx.toNat ∧
      (ByteFrame s t fun a ↦ Within a (s.getReg .x10) 24 ∨
        Within a (stackLo s tryAllocStack) tryAllocStack ∨ Within a nextAddr 8 ∨ Fresh s t a) ∧
      ByteFrame u t (Within · (s.getReg .x10) 24) := by
  have hb := hpre.bounds
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80004a54_spec hpc (by
    rv_eval [hout]
    and_intros <;> valid_access hpre.out [hb])
  have k₁ := b80004a54_keeps h₁
  have hm₁ := b80004a54_frame h₁ (by rw [hout]; addr_omega [hb])
  rw [hout] at hm₁
  have bf₁ := ByteFrame.of_memFrame hm₁ (by addr_omega [hb]) (by decide)
    (h₁.unaligned (by rv_eval [hout]; and_intros <;> addr_omega [hb]))
  have inv₁ := h.out hpre bf₁ (fun a ha ↦ by addr_omega [ha, hb]) fun r hr ↦ k₁ r (mem_of_mem hr _)
  obtain ⟨t, hr, hpc', hpres, htag, hmt, hbt⟩ := exit hpre (b80004a54_pc h₁) inv₁
    (by rw [k₁ .x8 (by decide), hout])
  obtain ⟨hheap', hmono, hnext, hframe⟩ := finish hpre inv₁ hmt hbt
  have m8 := b80004a54_m_x8_8 h₁
  have m16 := b80004a54_m_x8_16 h₁
  rw [hout] at m8 m16
  refine ⟨t, hr₁.trans hr, hpc', hpres, by rw [htag, b80004a54_x11 h₁], ?_, ?_, hheap', hmono,
    hnext, hframe, (bf₁.mono (w' := (Within · (s.getReg .x10) 24)) fun a ha ↦ by
      addr_omega [ha, hb]).trans hbt fun a ha ↦ by addr_omega [ha]⟩
  · rw [hmt _ (by addr_omega [hb]), m8]
  · rw [hmt _ (by addr_omega [hb]), m16]

/-- **`try_allocate_in` (zeroed) meets its contract**, given `alloc`'s and `memset`'s. -/
theorem try_alloc_zeroed_spec (hA : AllocSpec) (hM : MemsetSpec 0x800126f4) :
    TryAllocZeroedSpec := by
  intro s hpc hpre
  have hb := hpre.bounds
  have hal := hpre.align
  have hsz := hpre.size
  have ho := hpre.outFree
  have hheap := hpre.heap
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800049ac_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k₁ := b800049ac_keeps h₁
  have inv₁ : Inv s t₁ (s.getMem nextAddr) := FnInv.init hheap hpre.stack
    (by rw [b800049ac_x2 h₁]; rfl)
    (by
      simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      rv_eval []
      exact ⟨b800049ac_m_x2_n8 h₁, b800049ac_m_x2_n16 h₁, b800049ac_m_x2_n24 h₁,
        b800049ac_m_x2_n32 h₁, b800049ac_m_x2_n40 h₁, b800049ac_m_x2_n48 h₁⟩)
    (fun r hr ↦ k₁ r (mem_of_mem hr _))
    ((b800049ac_frame h₁ (by addr_omega [hb])).mono fun a ha ↦ by addr_omega [ha, hb])
    (h₁.unaligned (by rv_eval []; and_intros <;> addr_omega [hb])) (by decide)
  have hx8 : t₁.getReg .x8 = s.getReg .x10 := b800049ac_x8 h₁
  have hx9 : t₁.getReg .x9 = s.getReg .x14 * s.getReg .x11 := b800049ac_x9 h₁
  have hpc₁ := h₁.pc
  rv_eval [] at hpc₁
  rcases eq_ite_cases hpc₁ with ⟨hfit, hpc₁⟩ | ⟨-, hpc₁⟩
  · obtain ⟨hmul, hle⟩ := layout_ok hfit (by omega)
    obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800049fc_spec hpc₁ trivial
    have k₂ := b800049fc_keeps h₂
    have inv₂ := inv₁.out hpre (ByteFrame.of_same (b800049fc_mem_same h₂) fun _ ↦ False)
      (fun _ h ↦ h.elim) fun r hr ↦ k₂ r (mem_of_mem hr _)
    have hx8₂ : t₂.getReg .x8 = s.getReg .x10 := (k₂ .x8 (by decide)).trans hx8
    by_cases hz : t₁.getReg .x9 = 0
    · -- no bytes: `Ok`, capacity 0, the dangling pointer
      obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80004a40_spec (b800049fc_pc_taken h₂ hz) (by
        rv_eval [hx8₂]
        and_intros <;> valid_access hpre.out [hb])
      have k₃ := b80004a40_keeps h₃
      have hm₃ := b80004a40_frame h₃ (by rw [hx8₂]; addr_omega [hb])
      rw [hx8₂] at hm₃
      have inv₃ := inv₂.out hpre (ByteFrame.of_memFrame hm₃ (by addr_omega [hb]) (by decide)
        (h₃.unaligned (by rv_eval [hx8₂]; and_intros <;> addr_omega [hb])))
        (fun a ha ↦ by addr_omega [ha, hb]) fun r hr ↦ k₃ r (mem_of_mem hr _)
      obtain ⟨t, hr, hpc', hpres, htag, hmt, hbt⟩ := exit hpre (b80004a40_pc h₃) inv₃
        (by rw [k₃ .x8 (by decide), hx8₂])
      obtain ⟨hheap', hmono, -, hframe⟩ := finish hpre inv₃ hmt hbt
      have hc : (s.getReg .x11).toNat = 0 := by
        have := congrArg BitVec.toNat hz
        rw [hx9, hmul, show (0 : Word).toNat = 0 from rfl] at this
        rcases Nat.mul_eq_zero.mp this with h | h
        · omega
        · exact h
      refine ⟨t, hr₁.trans (hr₂.trans (hr₃.trans hr)), Or.inl ⟨hpc', hpres, ⟨hheap', hmono,
        fun _ ↦ ⟨?_, ?_⟩, hframe⟩, fun _ _ ↦ by simp only [hc, Nat.zero_mul]; rfl⟩⟩
      · have m := b80004a40_m_x8_8 h₃
        rw [hx8₂] at m
        rw [hmt _ (by addr_omega [hb]), m]
        exact BitVec.eq_of_toNat_eq (by rw [hc]; rfl)
      · have m := b80004a40_m_x8_16 h₃
        rw [hx8₂, k₂ .x13 (by decide), k₁ .x13 (by decide)] at m
        rw [hmt _ (by addr_omega [hb]), m]
        simp only [NewBuf, hc, Nat.zero_mul, true_or, and_true]
        exact Nat.mod_self _
    · -- allocate
      obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80004a00_spec (b800049fc_pc_not_taken h₂ hz)
        trivial
      have k₃ := b80004a00_keeps h₃
      have inv₃ := inv₂.out hpre (ByteFrame.of_same (b80004a00_mem_same h₃) fun _ ↦ False)
        (fun _ h ↦ h.elim) fun r hr ↦ k₃ r (mem_of_mem hr _)
      have hx10₃ : t₃.getReg .x10 = s.getReg .x13 := by
        rw [b80004a00_x10 h₃, k₂ .x13 (by decide), k₁ .x13 (by decide)]
      have hx11₃ : t₃.getReg .x11 = s.getReg .x14 * s.getReg .x11 := by
        rw [b80004a00_x11 h₃, k₂ .x9 (by decide), hx9]
      have hn₃ : heapNext t₃ = heapNext s := by simp only [heapNext, inv₃.next]
      have hheap₃ : HeapOk t₃ := ⟨hn₃ ▸ hheap.lo, hn₃ ▸ hheap.hi⟩
      obtain ⟨t₄, hr₄, ⟨hpc₄, hpres₄, hpost⟩ | hdead⟩ :=
        hA.call hr₃ (b80004a00_pc h₃) ⟨hheap₃, by rw [hx10₃]; exact hal⟩
      swap
      · exact ⟨t₄, hr₁.trans (hr₂.trans hr₄), Or.inr hdead⟩
      have inv₄ := inv₃.alloc hpre hpost hpres₄
      have hpal := hpost.aligned
      rw [hx10₃] at hpal
      have hnext₄ := hpost.next
      rw [hx11₃, hmul] at hnext₄
      have habove := hpost.above
      have hfit₄ := hpost.heap.hi
      have hp0 : t₄.getReg .x10 ≠ 0 := by
        intro h0
        have h2 := hheap₃.lo
        rw [h0, show (0 : Word).toNat = 0 from rfl] at habove
        simp only [heapStart] at h2
        omega
      have hx20 : t₄.getReg .x20 = s.getReg .x12 := by
        rw [hpres₄.reg .x20, b80004a00_x20 h₃, k₂ .x12 (by decide), k₁ .x12 (by decide)]
      have hx19 : t₄.getReg .x19 = s.getReg .x11 := by
        rw [hpres₄.reg .x19, b80004a00_x19 h₃, k₂ .x11 (by decide), k₁ .x11 (by decide)]
      have hx8₄ : t₄.getReg .x8 = s.getReg .x10 := by
        rw [hpres₄.reg .x8, k₃ .x8 (by decide), hx8₂]
      obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80004a1c_spec
        (by rw [hpc₄, returnAddress_eq, b80004a00_x1 h₃]; decide) trivial
      have k₅ := b80004a1c_keeps h₅
      have inv₅ := inv₄.out hpre (ByteFrame.of_same (b80004a1c_mem_same h₅) fun _ ↦ False)
        (fun _ h ↦ h.elim) fun r hr ↦ k₅ r (mem_of_mem hr _)
      have hnx₄ : heapNext t₄ = (t₄.getMem nextAddr).toNat := rfl
      have hP1 : heapNext s ≤ (t₄.getReg .x10).toNat := hn₃ ▸ habove
      have hP2 : (t₄.getMem nextAddr).toNat =
          (t₄.getReg .x10).toNat + (s.getReg .x11).toNat * (s.getReg .x14).toNat := by
        rw [← hnx₄, hnext₄, Nat.mul_comm (s.getReg .x14).toNat]
      have hP3 : (t₄.getMem nextAddr).toNat ≤ 0x78000000 := hfit₄
      have hP4 : 0x20000000 ≤ heapNext s := hheap.lo
      -- the new buffer, as the contract states it
      have hbuf (t : MachineState) (ht : heapNext t = (t₄.getMem nextAddr).toNat) :
          NewBuf s t (t₄.getReg .x10) ((s.getReg .x11).toNat * (s.getReg .x14).toNat)
            (s.getReg .x13).toNat := by
        simp only [NewBuf, ht]
        exact ⟨hpal, Or.inr ⟨hP1, by omega⟩⟩
      by_cases hi : s.getReg .x12 = 0
      · -- uninitialized
        obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b80004a50_spec
          (b80004a1c_pc_taken h₅ (by rw [hx20]; exact hi)) trivial
        have k₆ := b80004a50_keeps h₆
        have inv₆ := inv₅.out hpre (ByteFrame.of_same (b80004a50_mem_same h₆) fun _ ↦ False)
          (fun _ h ↦ h.elim) fun r hr ↦ k₆ r (mem_of_mem hr _)
        obtain ⟨t, hr, hpc', hpres, htag, h8, h16, hheap', hmono, hnext, hframe, -⟩ :=
          tail hpre (b80004a50_pc_not_taken h₆ (by rw [k₅ .x10 (by decide)]; exact hp0)) inv₆
            (by rw [k₆ .x8 (by decide), k₅ .x8 (by decide), hx8₄])
        refine ⟨t, hr₁.trans (hr₂.trans (hr₄.trans (hr₅.trans (hr₆.trans hr)))),
          Or.inl ⟨hpc', hpres, ⟨hheap', hmono, fun _ ↦ ⟨?_, ?_⟩, hframe⟩, fun h' ↦ (h' hi).elim⟩⟩
        · rw [h8, k₆ .x19 (by decide), k₅ .x19 (by decide), hx19]
        · rw [h16, k₆ .x10 (by decide), k₅ .x10 (by decide)]
          exact hbuf t hnext
      · -- zeroed
        obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b80004a20_spec
          (b80004a1c_pc_not_taken h₅ (by rw [hx20]; exact hi)) trivial
        have k₆ := b80004a20_keeps h₆
        have inv₆ := inv₅.out hpre (ByteFrame.of_same (b80004a20_mem_same h₆) fun _ ↦ False)
          (fun _ h ↦ h.elim) fun r hr ↦ k₆ r (mem_of_mem hr _)
        obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80004a24_spec
          (b80004a20_pc_not_taken h₆ (by rw [k₅ .x10 (by decide)]; exact hp0)) trivial
        have k₇ := b80004a24_keeps h₇
        have inv₇ := inv₆.out hpre (ByteFrame.of_same (b80004a24_mem_same h₇) fun _ ↦ False)
          (fun _ h ↦ h.elim) fun r hr ↦ k₇ r (mem_of_mem hr _)
        have hp₇ : t₇.getReg .x10 = t₄.getReg .x10 := by
          rw [k₇ .x10 (by decide), k₆ .x10 (by decide), k₅ .x10 (by decide)]
        have hn₇ : (t₇.getReg .x12).toNat = (s.getReg .x11).toNat * (s.getReg .x14).toNat := by
          rw [b80004a24_x12 h₇, k₆ .x9 (by decide), k₅ .x9 (by decide), hpres₄.reg .x9,
            k₃ .x9 (by decide), k₂ .x9 (by decide), hx9, hmul, Nat.mul_comm]
        obtain ⟨t₈, hr₈, ⟨hpc₈, hpres₈, hset⟩ | hdead⟩ :=
          hM.call hr₇ (b80004a24_pc h₇) (show Mapped _ _ by
            rw [hp₇, hn₇]; simp only [Mapped]; omega)
        swap
        · exact ⟨t₈, hr₁.trans (hr₂.trans (hr₄.trans (hr₅.trans (hr₆.trans hr₈)))), Or.inr hdead⟩
        have hbf := hset.frame
        rw [hp₇, hn₇] at hbf
        have inv₈ := inv₇.step hpre hbf (fun a ha ↦ Or.inr (Or.inr ⟨by
            simp only [Within] at ha; omega, by simp only [Within] at ha; omega⟩))
          ((hbf.getMem fun i hi ha ↦ by addr_omega [ha, hi, hP2, hP3]).trans inv₇.next)
          (Nat.le_refl _) inv₇.fits fun r hr ↦ hpres₈ r (mem_of_mem hr _)
        obtain ⟨t₉, hr₉, h₉⟩ := Sym.BlockSpec.reaches b80004a38_spec
          (by rw [hpc₈, returnAddress_eq, b80004a24_x1 h₇]; decide) trivial
        have k₉ := b80004a38_keeps h₉
        have inv₉ := inv₈.out hpre (ByteFrame.of_same (b80004a38_mem_same h₉) fun _ ↦ False)
          (fun _ h ↦ h.elim) fun r hr ↦ k₉ r (mem_of_mem hr _)
        have hx10₉ : t₉.getReg .x10 = t₄.getReg .x10 := by
          rw [b80004a38_x10 h₉, hpres₈.reg .x18, b80004a24_x18 h₇, k₆ .x10 (by decide),
            k₅ .x10 (by decide)]
        obtain ⟨t, hr, hpc', hpres, htag, h8, h16, hheap', hmono, hnext, hframe, hbt⟩ :=
          tail hpre (b80004a38_pc h₉) inv₉ (by
            rw [k₉ .x8 (by decide), hpres₈.reg .x8, k₇ .x8 (by decide), k₆ .x8 (by decide),
              k₅ .x8 (by decide), hx8₄])
        refine ⟨t, hr₁.trans (hr₂.trans (hr₄.trans (hr₅.trans (hr₆.trans (hr₈.trans
          (hr₉.trans hr)))))), Or.inl ⟨hpc', hpres, ⟨hheap', hmono, fun _ ↦ ⟨?_, ?_⟩, hframe⟩,
          fun _ _ ↦ ?_⟩⟩
        · rw [h8, k₉ .x19 (by decide), hpres₈.reg .x19, k₇ .x19 (by decide), k₆ .x19 (by decide),
            k₅ .x19 (by decide), hx19]
        · rw [h16, hx10₉]
          exact hbuf t hnext
        · have hz8 := hset.bytes
          rw [hp₇, hn₇, b80004a24_x11 h₇, show BitVec.truncate 8 (0 : Word) = 0 from rfl] at hz8
          rw [h16, hx10₉, ← hz8]
          refine (hbt.bytesAt fun i hi ha ↦ ?_).trans
            ((ByteFrame.of_same (b80004a38_mem_same h₉) fun _ ↦ False).bytesAt fun _ _ h ↦ h)
          have ho' := ho
          simp only [Outside] at ho'
          addr_omega [ha, hi, ho', hP1, hP2, hP3]
  · -- `Err(CapacityOverflow)`
    obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800049f0_spec hpc₁ (by
      rv_eval [hx8]
      valid_access hpre.out [hb])
    have k₂ := b800049f0_keeps h₂
    have hm₂ := b800049f0_frame h₂ (by rw [hx8]; addr_omega [hb])
    rw [hx8] at hm₂
    have inv₂ := inv₁.out hpre (ByteFrame.of_memFrame hm₂ (by addr_omega [hb]) (by decide)
      (h₂.unaligned (by rv_eval [hx8]; addr_omega [hb]))) (fun a ha ↦ by addr_omega [ha, hb])
      fun r hr ↦ k₂ r (mem_of_mem hr _)
    obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800049f4_spec (b800049f0_pc h₂) trivial
    have k₃ := b800049f4_keeps h₃
    have inv₃ := inv₂.out hpre (ByteFrame.of_same (b800049f4_mem_same h₃) fun _ ↦ False)
      (fun _ h ↦ h.elim) fun r hr ↦ k₃ r (mem_of_mem hr _)
    obtain ⟨t, hr, hpc', hpres, htag, hmt, hbt⟩ := exit hpre (b800049f4_pc h₃) inv₃
      (by rw [k₃ .x8 (by decide), k₂ .x8 (by decide), hx8])
    obtain ⟨hheap', hmono, -, hframe⟩ := finish hpre inv₃ hmt hbt
    refine ⟨t, hr₁.trans (hr₂.trans (hr₃.trans hr)), Or.inl ⟨hpc', hpres, ⟨hheap', hmono,
      fun h0 ↦ ?_, hframe⟩, fun _ h0 ↦ ?_⟩⟩
    · rw [htag, b800049f4_x11 h₃] at h0; cases h0
    · rw [htag, b800049f4_x11 h₃] at h0; cases h0

end Rv64Verifier.Runtime.TryAllocZeroed
