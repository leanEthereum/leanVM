import Rv64Verifier.Proofs.Layout.ArithCalls

/-!
# `flushes_arith`: from the entry to the operands' first form

`0x8000547c` saves the registers, writes the empty `Flushes` at `sp' + 8` and calls `state_step`;
`0x800054d4` calls `alloc(8, 120)` (`B`, the operands' buffer), `0x800054e4` traps on null;
`0x800054e8` calls `col(B, o_a, 0)`.
-/

namespace Rv64Verifier.Layout.Arith
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F19 Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Layout.Limb (Held)

/-- The empty `Flushes`, `(0, 8, 0)` twice. -/
theorem fheld_empty {s u : MachineState} {hi : Nat}
    (h0 : u.getMem (s.getReg .x2 - 472) = 0) (h8 : u.getMem (s.getReg .x2 - 472 + 8) = 8)
    (h16 : u.getMem (s.getReg .x2 - 472 + 16) = 0) (h24 : u.getMem (s.getReg .x2 - 472 + 24) = 0)
    (h32 : u.getMem (s.getReg .x2 - 472 + 24 + 8) = 8)
    (h40 : u.getMem (s.getReg .x2 - 472 + 24 + 16) = 0) : FHeld s u {} hi := by
  have v1 : ∀ a : Word, u.getMem a = 0 → u.getMem (a + 8) = 8 → u.getMem (a + 16) = 0 →
      FormVecsOk u a ∧ formVecsOf u a = [] ∧ ∀ x, ¬ formVecsDeep u a x := by
    intro a g0 g8 g16
    refine ⟨⟨⟨?_, ?_⟩, fun i hi ↦ ?_, fun i hi ↦ ?_⟩, ?_, fun x hx ↦ ?_⟩
    · simp only [RawVecOk, Buf, vecPtr, vecCap, g0, g8]; exact ⟨by decide, Or.inl (by decide)⟩
    · simp only [vecLen, vecCap, g0, g16]; exact Nat.le_refl _
    · simp only [vecLen, g16] at hi; simp at hi
    · simp only [vecLen, g16] at hi; simp at hi
    · simp only [formVecsOf, vecLen, g16]; rfl
    · rcases hx with hx | ⟨i, hi, -⟩
      · simp only [formVecsBuf, vecCap, vecPtr, g0, g8, Within] at hx; simp at hx; omega
      · simp only [vecLen, g16] at hi; simp at hi
  obtain ⟨p1, p2, p3⟩ := v1 _ h0 h8 h16
  obtain ⟨q1, q2, q3⟩ := v1 _ h24 h32 h40
  refine ⟨⟨p1, q1, fun x _ hx ↦ q3 x hx, fun x _ hx ↦ p3 x hx, fun x _ hx ↦ ?_⟩, ?_,
    fun x hx ↦ ?_⟩
  · rcases hx with hx | hx
    · exact p3 x hx
    · exact q3 x hx
  · simp only [flushesOf, p2, q2]
  · exfalso
    rcases hx with hx | hx
    · exact p3 x hx
    · exact q3 x hx

/-- After `col(B, o_a, 0)`: the `Flushes` holds the state step, `B` the operands' first form. -/
structure AtB (s u : MachineState) (B : Word) : Prop extends Inv s u where
  pc : u.pc = 0x800054fc
  x9 : u.getReg .x9 = s.getReg .x12
  x18 : u.getReg .x18 = s.getReg .x11
  x19 : u.getReg .x19 = B
  bal : B.toNat % 8 = 0
  blo : heapNext s ≤ B.toNat
  bhi : B.toNat + 120 ≤ heapNext u
  fl : FHeld s u (({} : FlushesRust).stateStep 0 1) B.toNat
  b0 : Held u B (colRust 2 0) (B.toNat + 120) (heapNext u)

/-- The prologue, `state_step`, `alloc` and `col(B, o_a, 0)`. -/
theorem start (hS : StateStepSpec) (hA : AllocSpec) (hC : ColSpec) {s : MachineState}
    (hpc : s.pc = 0x8000547c) (hpre : FlushesArithPre s) :
    ∃ u B, Reaches Image.code s u ∧ (AtB s u B ∨ Dead Image.code u) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hheap := hpre.heap
  -- the prologue
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000547c_spec hpc (by
    rv_eval []
    and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₁ := b8000547c_keeps h₁
  have hm₁ := b8000547c_frame h₁ (by addr_omega [hsb])
  have hn₁ : heapNext t₁ = heapNext s := by
    simp only [heapNext]; rw [hm₁ _ (by addr_omega [hnx, hsb])]
  have c₁ : Inv s t₁ := {
    x2 := b8000547c_x2 h₁
    x8 := b8000547c_x8 h₁
    regs := fun r hr ↦ k₁ r (mem_of_mem hr _)
    ra := b8000547c_m_x2_n8 h₁
    s0 := b8000547c_m_x2_n16 h₁
    s1 := b8000547c_m_x2_n24 h₁
    s2 := b8000547c_m_x2_n32 h₁
    s3 := b8000547c_m_x2_n40 h₁
    s4 := b8000547c_m_x2_n48 h₁
    s5 := b8000547c_m_x2_n56 h₁
    s6 := b8000547c_m_x2_n64 h₁
    heap := ⟨hn₁ ▸ hheap.lo, hn₁ ▸ hheap.hi⟩
    mono := hn₁.ge
    rodata := RodataOk.dframe hpre.rodata hm₁.dframe fun x hx hw ↦ by addr_omega [hx, hw, hsb, hro]
    frame := hm₁.dframe.mono fun x hx ↦ Or.inl (by addr_omega [hx, hsb]) }
  have f₁ : FHeld s t₁ {} (heapNext s) := fheld_empty (b8000547c_m_x2_n472 h₁)
    (by have := b8000547c_m_x2_n464 h₁; rv_eval [] at this ⊢; exact this)
    (by have := b8000547c_m_x2_n456 h₁; rv_eval [] at this ⊢; exact this)
    (by have := b8000547c_m_x2_n448 h₁; rv_eval [] at this ⊢; exact this)
    (by have := b8000547c_m_x2_n440 h₁; rv_eval [] at this ⊢; exact this)
    (by have := b8000547c_m_x2_n432 h₁; rv_eval [] at this ⊢; exact this)
  have x10₁ : t₁.getReg .x10 = s.getReg .x2 - 472 := b8000547c_x10 h₁
  -- `state_step(sp' + 8)`
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hg₂, hv₂⟩ | hdead⟩ := hS.call hr₁ (b8000547c_pc h₁)
    (flushesPre hpre c₁ f₁ x10₁ (by decide) (by decide) (by decide))
  swap
  · exact ⟨t₂, 0, hr₂, Or.inr hdead⟩
  rw [x10₁] at hg₂ hv₂
  obtain ⟨c₂, f₂⟩ := afterGrow hpre c₁ f₁ (by rw [hn₁]) (by decide) hpres₂ hg₂
  rw [hv₂, f₁.val] at f₂
  -- `alloc(8, 120)`
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800054d4_spec
    (by rw [hpc₂, returnAddress_eq, b8000547c_x1 h₁]; decide) trivial
  have k₃ := b800054d4_keeps h₃
  have hm₃ := b800054d4_mem_same h₃
  have c₃ := c₂.same hpre hm₃ fun r hr ↦ k₃ r (mem_of_mem hr _)
  have hn₃ : heapNext t₃ = heapNext t₂ := by simp only [heapNext, hm₃]
  have f₃ := f₂.keep (DFrame.of_same hm₃ fun _ ↦ False) c₂.heap hn₃.ge (fun _ h ↦ h.elim)
    (fun _ _ h ↦ h) (by addr_omega [hsb])
  obtain ⟨t₄, hr₄, ⟨hpc₄, hpres₄, hpost₄⟩ | hdead⟩ := hA.call (hr₂.trans hr₃)
    (b800054d4_pc h₃) ⟨c₃.heap, by rw [b800054d4_x10 h₃]; decide⟩
  swap
  · exact ⟨t₄, 0, hr₄, Or.inr hdead⟩
  obtain ⟨B, hB⟩ : ∃ B, t₄.getReg .x10 = B := ⟨_, rfl⟩
  have hBal : B.toNat % 8 = 0 := by rw [← hB]; simpa [b800054d4_x10 h₃] using hpost₄.aligned
  have hBlo : heapNext t₃ ≤ B.toNat := by rw [← hB]; exact hpost₄.above
  have hBn : heapNext t₄ = B.toNat + 120 := by rw [hpost₄.next, hB, b800054d4_x11 h₃]; rfl
  have hh₄ := hpost₄.heap.hi
  have hh₂ := c₂.heap.hi
  have hlo₀ := hheap.lo
  have cm₂ := c₂.mono
  have hfn : DFrame t₃ t₄ fun x ↦ Within x nextAddr 8 :=
    fun a ha _ ↦ hpost₄.mem a fun h ↦ ha a (by rw [h]; addr_omega []) (by rw [h]; addr_omega [])
  have c₄ : Inv s t₄ := c₃.step hpre hfn (fun x h ↦ Or.inr (Or.inl h)) hpost₄.heap (by omega)
    (keepRegs_of hpres₄)
  have f₄ := f₃.keep hfn c₃.heap (by omega) (fun x h _ ↦ by addr_omega [h, hh₂])
    (fun x hx h ↦ by addr_omega [hx, h, hsb, hnx]) (by addr_omega [hsb])
  -- the null check
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b800054e4_spec
    (by rw [hpc₄, returnAddress_eq, b800054d4_x1 h₃]; decide) trivial
  have hB0 : t₄.getReg .x10 ≠ 0 := by
    rw [hB]; intro h; rw [h] at hBlo; simp only [heapStart] at hlo₀; simp at hBlo; omega
  have k₅ := b800054e4_keeps h₅
  have hm₅ := b800054e4_mem_same h₅
  have c₅ := c₄.same hpre hm₅ fun r hr ↦ k₅ r (mem_of_mem hr _)
  have hn₅ : heapNext t₅ = heapNext t₄ := by simp only [heapNext, hm₅]
  have f₅ := f₄.keep (DFrame.of_same hm₅ fun _ ↦ False) c₄.heap hn₅.ge (fun _ h ↦ h.elim)
    (fun _ _ h ↦ h) (by addr_omega [hsb])
  -- `col(B, o_a, 0)`
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b800054e8_spec (b800054e4_pc_not_taken h₅ hB0)
    trivial
  have k₆ := b800054e8_keeps h₆
  have hm₆ := b800054e8_mem_same h₆
  have c₆ := c₅.same hpre hm₆ fun r hr ↦ k₆ r (mem_of_mem hr _)
  have hn₆ : heapNext t₆ = heapNext t₅ := by simp only [heapNext, hm₆]
  have f₆ := f₅.keep (DFrame.of_same hm₆ fun _ ↦ False) c₅.heap hn₆.ge (fun _ h ↦ h.elim)
    (fun _ _ h ↦ h) (by addr_omega [hsb])
  have x10₆ : t₆.getReg .x10 = B := by rw [k₆ .x10 (by decide), k₅ .x10 (by decide), hB]
  have hn₆' : heapNext t₆ = B.toNat + 120 := by rw [hn₆, hn₅, hBn]
  obtain ⟨v, hrv, ⟨hpcv, hpresv, cv, hmv, bv, kv⟩ | hdead⟩ := colCall hC hpre c₆
    (hr₄.trans (hr₅.trans hr₆)) (b800054e8_pc h₆) x10₆
    (Or.inr ⟨by omega, by omega⟩) hBal (M := B.toNat) (by omega) (Or.inr (Nat.le_refl _))
  swap
  · exact ⟨v, 0, hrv, Or.inr hdead⟩
  rw [b800054e8_x11 h₆, b800054e8_x12 h₆, hn₆'] at bv
  refine ⟨v, B, hrv, Or.inl {
    toInv := cv
    pc := by rw [hpcv, returnAddress_eq, b800054e8_x1 h₆]; decide
    x9 := by rw [hpresv.reg .x9, k₆ .x9 (by decide), k₅ .x9 (by decide), hpres₄.reg .x9,
      k₃ .x9 (by decide), hpres₂.reg .x9, b8000547c_x9 h₁]
    x18 := by rw [hpresv.reg .x18, k₆ .x18 (by decide), k₅ .x18 (by decide), hpres₄.reg .x18,
      k₃ .x18 (by decide), hpres₂.reg .x18, b8000547c_x18 h₁]
    x19 := by rw [hpresv.reg .x19, b800054e8_x19 h₆, k₅ .x10 (by decide), hB]
    bal := hBal
    blo := by have := c₃.mono; omega
    bhi := by omega
    fl := kv.2 _ _ (f₆.mono (by omega)) (Nat.le_refl _)
    b0 := bv }⟩

end Rv64Verifier.Layout.Arith
