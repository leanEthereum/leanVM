import Rv64Verifier.Proofs.Pcs.VsoKernelCall

/-!
# `verify_stacked_opening`'s level loop: level 0's rows, their buffer

At level `0` (`0x8000b2e0`) the rows' values go to a new `Vec<E>` of `n = s4` elements:
`try_allocate_in(S - 384, n, 0, 8, 24)` (`callTryAlloc24`), its `Err` to the trap at
`0x8000bfd4`, the `RawVec` moved to `S - 464` with length `0`, and `reserve(S - 464, n)`, which
has room and returns at once. `alloc0` reaches `0x8000b328` (`Alloc0`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- `try_allocate_in(S - 384, a1, _, 8, 24)`: a buffer of `a1` elements of `E`. -/
theorem callTryAlloc24 (hT : TryAllocZeroedSpec) {s t : MachineState} (hpre : VsoPre s)
    (hpc : t.pc = 0x800049ac) (hsp : t.getReg .x2 = s.getReg .x2 - 1040)
    (hx10 : t.getReg .x10 = s.getReg .x2 - 384) (hx13 : t.getReg .x13 = 8)
    (hx14 : t.getReg .x14 = 24) (hheap : HeapOk t) :
    ∃ v, Reaches Image.code t v ∧ (Dead Image.code v ∨ (v.pc = returnAddress t ∧
      Preserves t v ∧ HeapOk v ∧ heapNext t ≤ heapNext v ∧
      (v.getMem (s.getReg .x2 - 384) = 0 → v.getMem (s.getReg .x2 - 376) = t.getReg .x11 ∧
        NewBuf t v (v.getMem (s.getReg .x2 - 368)) ((t.getReg .x11).toNat * 24) 8) ∧
      DFrame t v fun a ↦ Within a (s.getReg .x2 - 384) 24 ∨
        Within a (s.getReg .x2 - 1088) 48 ∨ Within a nextAddr 8 ∨ Fresh t v a)) := by
  have hst := hpre.stack
  have hb := bounds hpre
  have hsl : stackLo t tryAllocStack = s.getReg .x2 - 1088 := by
    simp only [stackLo, tryAllocStack, hsp]; rv_eval []
  have hnx := hst.next
  have hab := hst.above
  simp only [vso_stack] at hnx hab
  have hpreT : TryAllocPre .x13 .x14 t := {
    heap := hheap
    out := by rw [hx10]; valid_sub hst.valid [hb]
    align := by rw [hx13]; decide
    size := by rw [hx14]; decide
    stack := hst.sub 1040 hsp (by decide) (by decide) (by decide) (by decide) (by decide)
    outFree := by
      rw [hx10]
      simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx, hb]⟩
    outStack := by rw [hx10, hsl]; addr_omega [hb] }
  obtain ⟨v, hr, ⟨hpc', hpres, hpost, -⟩ | hdead⟩ := hT.call (Reaches.refl t) hpc hpreT
  · have hok := hpost.ok
    have hfr := DFrame.of_byteFrame hpost.frame
    rw [hx10, hx14, hx13] at hok
    rw [hx10, hsl] at hfr
    refine ⟨v, hr, Or.inr ⟨hpc', hpres, hpost.heap, hpost.mono, fun h0 ↦ ?_, hfr⟩⟩
    obtain ⟨h1, h2⟩ := hok h0
    rw [show s.getReg .x2 - 384 + 8 = s.getReg .x2 - 376 by rv_eval []] at h1
    rw [show s.getReg .x2 - 384 + 16 = s.getReg .x2 - 368 by rv_eval [],
      show (24 : Word).toNat = 24 from rfl, show (8 : Word).toNat = 8 from rfl] at h2
    exact ⟨h1, h2⟩
  · exact ⟨v, hr, Or.inl hdead⟩

/-- What level 0's rows write before their loop: the `Result` at `S - 384`, the `Vec` at
`S - 464`, `try_allocate_in`'s stack, `NEXT` and the new buffer. -/
@[rv_addr] def A0W (s a r : MachineState) (y : Word) : Prop :=
  Within y (s.getReg .x2 - 384) 24 ∨ Within y (s.getReg .x2 - 464) 24 ∨
    Within y (s.getReg .x2 - 1088) 48 ∨ Within y nextAddr 8 ∨ Fresh a r y

/-- At `0x8000b328`, from `a` at `0x8000b2e0`: an empty `Vec<E>` at `S - 464` with room for
`n = a.x20` elements in a new buffer. -/
structure Alloc0 (s a r : MachineState) : Prop where
  pc : r.pc = 0x8000b328
  sp : r.getReg .x2 = s.getReg .x2 - 1040
  regs : ∀ q ∈ calleeSaved, r.getReg q = a.getReg q
  inv : InvR s r (r.getMem nextAddr)
  heap : HeapOk r
  mono : heapNext a ≤ heapNext r
  cap : r.getMem (s.getReg .x2 - 464) = a.getReg .x20
  buf : NewBuf a r (r.getMem (s.getReg .x2 - 456)) (24 * (a.getReg .x20).toNat) 8
  len : r.getMem (s.getReg .x2 - 448) = 0
  fr : DFrame a r (A0W s a r)

/-- **The rows' buffer**, from `0x8000b2e0` to `0x8000b328`, or a dead end. -/
theorem alloc0 (hT : TryAllocZeroedSpec) (hR : ReserveFastSpec 0x80008a10) {s a : MachineState}
    (hpre : VsoPre s) (hpc : a.pc = 0x8000b2e0) (hsp : a.getReg .x2 = s.getReg .x2 - 1040)
    (hinv : InvR s a (a.getMem nextAddr)) :
    ∃ r, Reaches Image.code a r ∧ (Dead Image.code r ∨ Alloc0 s a r) := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hah := hinv.heap hpre.heap
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000b2e0_spec hpc trivial
  have k₁ := b8000b2e0_keeps h₁
  have hm₁ := b8000b2e0_mem_same h₁
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 1040 := by rw [k₁ .x2 (by decide), hsp]
  have hn₁ : heapNext t₁ = heapNext a := by simp only [heapNext, hm₁]
  obtain ⟨t₂, hr₂, hv₂⟩ := callTryAlloc24 hT hpre (b8000b2e0_pc h₁) sp₁
    (by rw [b8000b2e0_x10 h₁, hsp]; rv_eval []) (b8000b2e0_x13 h₁) (b8000b2e0_x14 h₁)
    ⟨by rw [hn₁]; exact hah.lo, by rw [hn₁]; exact hah.hi⟩
  rcases hv₂ with hd | ⟨hpc₂, hpres₂, hheap₂, hmono₂, hok₂, X₂⟩
  · exact ⟨t₂, hr₁.trans hr₂, Or.inl hd⟩
  have sp₂ : t₂.getReg .x2 = s.getReg .x2 - 1040 := by rw [hpres₂ .x2 (by decide), sp₁]
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000b2fc_spec
    (by rw [hpc₂, returnAddress_eq, b8000b2e0_x1 h₁]; decide) (by
      rv_eval [sp₂]; valid_access hst.valid [hb])
  have q656 : t₂.getMem (t₂.getReg .x2 + 656) = t₂.getMem (s.getReg .x2 - 384) := by
    rw [sp₂]; rv_eval []
  by_cases hok : t₂.getMem (s.getReg .x2 - 384) = 0
  swap
  · have hpc₃ := b8000b2fc_pc_taken h₃ (by rw [q656]; exact hok)
    exact ⟨t₃, hr₁.trans (hr₂.trans hr₃),
      Or.inl (dead_of_fetch (by rw [hpc₃]; exact trap))⟩
  have hpc₃ := b8000b2fc_pc_not_taken h₃ (by rw [q656]; exact hok)
  obtain ⟨hcap, hnew⟩ := hok₂ hok
  rw [b8000b2e0_x11 h₁] at hcap hnew
  have k₃ := b8000b2fc_keeps h₃
  have hm₃ := b8000b2fc_mem_same h₃
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - 1040 := by rw [k₃ .x2 (by decide), sp₂]
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000b304_spec hpc₃ (by
    rv_eval [sp₃]; and_intros <;> valid_access hst.valid [hb])
  have k₄ := b8000b304_keeps h₄
  have f₄ := DFrame.of_memFrame (b8000b304_frame h₄ (by rw [sp₃]; addr_omega [hb]))
  rw [sp₃, show s.getReg .x2 - 1040 + 576 = s.getReg .x2 - 464 by rv_eval []] at f₄
  have m592 := b8000b304_m_x2_592 h₄
  have m584 := b8000b304_m_x2_584 h₄
  have m576 := b8000b304_m_x2_576 h₄
  rw [sp₃, show s.getReg .x2 - 1040 + 592 = s.getReg .x2 - 448 by rv_eval []] at m592
  rw [sp₃, show s.getReg .x2 - 1040 + 584 = s.getReg .x2 - 456 by rv_eval [],
    show s.getReg .x2 - 1040 + 672 = s.getReg .x2 - 368 by rv_eval [], hm₃] at m584
  rw [sp₃, show s.getReg .x2 - 1040 + 576 = s.getReg .x2 - 464 by rv_eval [],
    show s.getReg .x2 - 1040 + 664 = s.getReg .x2 - 376 by rv_eval [], hm₃, hcap] at m576
  have sp₄ : t₄.getReg .x2 = s.getReg .x2 - 1040 := by rw [k₄ .x2 (by decide), sp₃]
  have x10₄ : t₄.getReg .x10 = s.getReg .x2 - 464 := by
    rw [b8000b304_x10 h₄, sp₃]; rv_eval []
  have x11₄ : t₄.getReg .x11 = a.getReg .x20 := by
    rw [b8000b304_x11 h₄, k₃ .x20 (by decide), hpres₂ .x20 (by decide), k₁ .x20 (by decide)]
  obtain ⟨t₅, hr₅, ⟨hpc₅, hpres₅, -, hm₅⟩ | hd⟩ :=
    hR.call (Reaches.refl t₄) (b8000b304_pc h₄)
    ⟨by rw [x10₄]; valid_sub hst.valid [hb], by
      simp only [vecLen, vecCap]
      rw [x10₄, x11₄, show s.getReg .x2 - 464 + 16 = s.getReg .x2 - 448 by rv_eval [], m592,
        m576]
      simp⟩
  swap
  · exact ⟨t₅, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), Or.inl hd⟩
  have sp₅ : t₅.getReg .x2 = s.getReg .x2 - 1040 := by rw [hpres₅ .x2 (by decide), sp₄]
  -- `NEXT` is `try_allocate_in`'s
  have nx₄ : t₄.getMem nextAddr = t₂.getMem nextAddr := by
    rw [f₄ _ fun i hi hw ↦ by addr_omega [hw, hi, hb, hnx], hm₃]
  have hn₅ : heapNext t₅ = heapNext t₂ := by simp only [heapNext, hm₅, nx₄]
  have hh₂ := hheap₂.hi
  -- the frame
  have F : DFrame a t₅ (A0W s a t₅) := by
    intro y hy
    have h0 := hy 0 (by decide)
    simp only [A0W, add_ofNat_zero] at h0
    rw [hm₅, f₄ y fun i hi hw ↦ hy i hi (Or.inr (Or.inl hw)), hm₃,
      X₂ y fun i hi hw ↦ ?_, hm₁]
    simp only [Fresh, hn₁] at hw
    rcases hw with hw | hw | hw | hw
    · exact hy i hi (Or.inl hw)
    · exact hy i hi (Or.inr (Or.inr (Or.inl hw)))
    · exact hy i hi (Or.inr (Or.inr (Or.inr (Or.inl hw))))
    · exact hy i hi (Or.inr (Or.inr (Or.inr (Or.inr (by simp only [Fresh, hn₅]; exact hw)))))
  have hmono : heapNext a ≤ heapNext t₅ := by rw [hn₅, ← hn₁]; exact hmono₂
  have hheap₅ : HeapOk t₅ := ⟨by rw [hn₅]; exact hheap₂.lo, by rw [hn₅]; exact hh₂⟩
  refine ⟨t₅, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), Or.inr {
    pc := by rw [hpc₅, returnAddress_eq, b8000b304_x1 h₄]; decide
    sp := sp₅
    regs := fun q hq ↦ by
      rw [hpres₅ q hq, k₄ q (mem_of_calleeSaved hq _), k₃ q (mem_of_calleeSaved hq _),
        hpres₂ q hq, k₁ q (mem_of_calleeSaved hq _)]
    inv := Inv.step' hpre hinv F (fun y hy ↦ ?_) (fun y hy ↦ ?_) rfl hmono hheap₅.hi
      (sp₅.trans hsp.symm)
    heap := hheap₅
    mono := hmono
    cap := by rw [hm₅, m576]
    buf := by
      have := hnew
      simp only [NewBuf, hn₁] at this ⊢
      rw [hm₅, m584, hn₅, Nat.mul_comm]
      exact this
    len := by rw [hm₅, m592]
    fr := F }⟩
  · simp only [A0W] at hy
    rcases hy with hy | hy | hy | hy | ⟨hy1, hy2⟩
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [hy, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [hy, hb])))
    · exact Or.inr (Or.inl (in_stack hpre (by addr_omega [hy, hb])))
    · exact Or.inr (Or.inr (Or.inl hy))
    · exact Or.inr (Or.inr (Or.inr
        ⟨by have := hinv.mono; simp only [heapNext] at hy1; omega, hy2⟩))
  · simp only [A0W] at hy
    have hh := hheap₅.hi
    rcases hy with hy | hy | hy | hy | ⟨-, hy⟩
    · addr_omega [hy, hb]
    · addr_omega [hy, hb]
    · addr_omega [hy, hb]
    · addr_omega [hy, hb, hnx]
    · addr_omega [hy, hb, hh]

end Rv64Verifier.Proofs.Pcs.Vso
