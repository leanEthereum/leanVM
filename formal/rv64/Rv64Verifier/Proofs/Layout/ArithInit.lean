import Rv64Verifier.Proofs.Layout.ArithSites

/-!
# `flushes_arith`: a product sum's first summand, `multiply` true

`0x80005658` (lane 0), `0x80005734` and `0x800058a8` (lanes 1 and 2, after moving the previous
lane's sum to `sp' + 344 + 24 (i - 1)`) call `prod(sp' + 104, va[0], vb[k], 0)`; `0x80005678`,
`0x80005764` and `0x800058d8` write the empty sum at `sp' + 80` and call `add_scaled`.
-/

namespace Rv64Verifier.Layout.Arith
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F19 Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Layout.Limb (Held held_empty)

theorem mulInit1 (hP : ProdSpec) (hA : AddScaledSpec) {s u0 z : MachineState} {L0 : Nat}
    {fl : FlushesRust}
    (hpre : FlushesArithPre s) (c : Inv s z)
    (hr : Reaches Image.code u0 z) (hpc : z.pc = 0x80005658)
    (f : FHeld s z fl L0) (hL0 : L0 ≤ heapNext z) :
    ∃ w, Reaches Image.code u0 w ∧ ((w.pc = 0x800056a4 ∧ Inv s w ∧ heapNext z ≤ heapNext w ∧
      w.getReg .x9 = s.getReg .x2 - 376 ∧ w.getReg .x18 = 0xa00000b0 ∧ w.getReg .x19 = 8 ∧
      FHeld s w fl L0 ∧
      Held w (s.getReg .x2 - 400) (({} : FormRust).add (prodRust 5 8 0)) (heapNext z)
        (heapNext w)) ∨ Dead Image.code w) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  have hhz := c.heap.hi
  obtain ⟨z₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80005658_spec hpc trivial
  have k₁ := b80005658_keeps h₁
  have hm₁ := b80005658_mem_same h₁
  have c₁ := c.same hpre hm₁ fun r hr ↦ k₁ r (mem_of_mem hr _)
  have K₁ := sameKeeps hpre c hm₁
  have hn₁ : heapNext z₁ = heapNext z := by simp only [heapNext, hm₁]
  have h10₁ : z₁.getReg .x10 = s.getReg .x2 - 376 := by rw [b80005658_x10 h₁, x2]; rv_eval []
  have f₁ := K₁.2 _ _ f (by omega)
  obtain ⟨z₂, hr₂, ⟨hpc₂, hp₂, hnew, hval⟩ | hd⟩ := hP.call (hr.trans hr₁) (b80005658_pc h₁)
    (colPre hpre c₁ h10₁ (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb]))
  swap
  · exact ⟨z₂, hr₂, Or.inr hd⟩
  rw [h10₁] at hnew hval
  obtain ⟨c₂, hn₂, b₂, K₂⟩ := afterNew hpre c₁ (M := heapNext z₁) (Or.inl (by addr_omega [hsb]))
    (Nat.le_refl _) (Or.inl (by addr_omega [hsb, hab])) (by simp only [colStack, powStack]; decide)
    hp₂ hnew
  rw [hval, b80005658_x11 h₁, b80005658_x12 h₁, b80005658_x13 h₁] at b₂
  have f₂ := K₂.2 _ _ f₁ (by omega)
  have x19₂ : z₂.getReg .x19 = 8 := by rw [hp₂.reg .x19, b80005658_x19 h₁]
  obtain ⟨z₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80005678_spec
    (by rw [hpc₂, returnAddress_eq, b80005658_x1 h₁]; decide)
    (by rv_eval [c₂.x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₃ := b80005678_keeps h₃
  have hm₃ := b80005678_frame h₃ (by addr_omega [hsb, c₂.x2])
  rw [c₂.x2] at hm₃
  obtain ⟨c₃, hn₃⟩ := c₂.block hpre hm₃ (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ k₃ r (mem_of_mem hr _)
  have K₃ := blockKeeps hpre c₂ hm₃ (by addr_omega [hsb]) (by addr_omega [hsb])
  have f₃ := K₃.2 _ _ f₂ (by omega)
  have bo := heldMono (K₃.1 _ _ _ _ b₂ (Nat.le_refl _) (Or.inl (by addr_omega [hsb]))
    (by addr_omega [hsb])) (l' := heapNext z) (h' := heapNext z₃) (by omega) (by omega)
  have ba : Held z₃ (s.getReg .x2 - 400) {} (heapNext z) (heapNext z) := held_empty
    (by have := b80005678_m_x2_80 h₃; rw [c₂.x2] at this; rv_eval [] at this ⊢; exact this)
    (by have := b80005678_m_x2_88 h₃; rw [c₂.x2, x19₂] at this; rv_eval [] at this ⊢; exact this)
    (by have := b80005678_m_x2_96 h₃; rw [c₂.x2] at this; rv_eval [] at this ⊢; exact this)
  obtain ⟨w, hr₄, ⟨hpc₄, hp₄, c₄, hn₄, b₄, K₄⟩ | hd⟩ := addCall hA hpre c₃ (hr₂.trans hr₃)
    (b80005678_pc h₃) (o := s.getReg .x2 - 400) (e := s.getReg .x2 - 376)
    (by rw [b80005678_x10 h₃, c₂.x2]; rv_eval [])
    (by rw [b80005678_x11 h₃, c₂.x2, vecPtr, hm₃ (s.getReg .x2 - 376 + 8) (by addr_omega [hsb])];
        rv_eval [])
    (by rw [b80005678_x12 h₃, c₂.x2, vecLen, hm₃ (s.getReg .x2 - 376 + 16) (by addr_omega [hsb])];
        rv_eval [])
    (by rw [b80005678_x13 h₃]) (by addr_omega [hsb])
    (by addr_omega [hsb]) ba bo c.mono (Nat.le_refl _) (by omega) (prodRust_terms _ _ _)
  swap
  · exact ⟨w, hr₄, Or.inr hd⟩
  refine ⟨w, hr₄, Or.inl ⟨by rw [hpc₄, returnAddress_eq, b80005678_x1 h₃]; decide, c₄, by omega,
    by rw [hp₄.reg .x9, k₃ .x9 (by decide), hp₂.reg .x9, b80005658_x9 h₁, x2]; rv_eval [],
    by rw [hp₄.reg .x18, b80005678_x18 h₃],
    by rw [hp₄.reg .x19, k₃ .x19 (by decide), x19₂],
    K₄.2 _ _ f₃ (by omega), heldMono b₄ (by omega) (Nat.le_refl _)⟩⟩

theorem mulInit2 (hP : ProdSpec) (hA : AddScaledSpec) {s u0 z : MachineState} {L0 : Nat}
    {fl : FlushesRust} {g : FormRust} {Lp : Nat}
    (hpre : FlushesArithPre s) (c : Inv s z)
    (hr : Reaches Image.code u0 z) (hpc : z.pc = 0x80005734)
    (h9 : z.getReg .x9 = s.getReg .x2 - 376) (h18 : z.getReg .x18 = 0xa00000b0)
    (h19 : z.getReg .x19 = 8)
    (f : FHeld s z fl L0) (hL0 : L0 ≤ heapNext z)
    (bs : Held z (s.getReg .x2 - 400) g Lp (heapNext z)) :
    ∃ w, Reaches Image.code u0 w ∧ ((w.pc = 0x80005788 ∧ Inv s w ∧ heapNext z ≤ heapNext w ∧
      w.getReg .x9 = s.getReg .x2 - 376 ∧ w.getReg .x18 = 0xa00000b0 ∧ w.getReg .x19 = 8 ∧
      FHeld s w fl L0 ∧
      Held w (s.getReg .x2 - 400) (({} : FormRust).add (prodRust 5 9 0)) (heapNext z)
        (heapNext w) ∧
      Held w (s.getReg .x2 - 136) g Lp (heapNext z)) ∨ Dead Image.code w) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  have hhz := c.heap.hi
  obtain ⟨z₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80005734_spec hpc
    (by rv_eval [x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₁ := b80005734_keeps h₁
  have hm₁ := b80005734_frame h₁ (by addr_omega [hsb, x2])
  rw [x2] at hm₁
  obtain ⟨c₁, hn₁⟩ := c.block hpre hm₁ (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ k₁ r (mem_of_mem hr _)
  have K₁ := blockKeeps hpre c hm₁ (by addr_omega [hsb]) (by addr_omega [hsb])
  have res₁ := moveHeld (e := s.getReg .x2 - 136) bs hm₁.dframe c.heap hn₁.ge
    (fun x hx _ ↦ by addr_omega [hx, hsb, hab, hhz])
    (by have := b80005734_m_x2_344 h₁; rw [x2] at this; rv_eval [] at this ⊢; exact this)
    (by have := b80005734_m_x2_352 h₁; rw [x2] at this; rv_eval [] at this ⊢; exact this)
    (by have := b80005734_m_x2_360 h₁; rw [x2] at this; rv_eval [] at this ⊢; exact this)
  have h10₁ : z₁.getReg .x10 = s.getReg .x2 - 376 := by rw [b80005734_x10 h₁, h9]
  have f₁ := K₁.2 _ _ f (by omega)
  obtain ⟨z₂, hr₂, ⟨hpc₂, hp₂, hnew, hval⟩ | hd⟩ := hP.call (hr.trans hr₁) (b80005734_pc h₁)
    (colPre hpre c₁ h10₁ (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb]))
  swap
  · exact ⟨z₂, hr₂, Or.inr hd⟩
  rw [h10₁] at hnew hval
  obtain ⟨c₂, hn₂, b₂, K₂⟩ := afterNew hpre c₁ (M := heapNext z₁) (Or.inl (by addr_omega [hsb]))
    (Nat.le_refl _) (Or.inl (by addr_omega [hsb, hab])) (by simp only [colStack, powStack]; decide)
    hp₂ hnew
  rw [hval, b80005734_x11 h₁, b80005734_x12 h₁, b80005734_x13 h₁] at b₂
  have f₂ := K₂.2 _ _ f₁ (by omega)
  have res₂ := K₂.1 _ _ _ _ res₁ (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  have x19₂ : z₂.getReg .x19 = 8 := by rw [hp₂.reg .x19, k₁ .x19 (by decide), h19]
  obtain ⟨z₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80005764_spec
    (by rw [hpc₂, returnAddress_eq, b80005734_x1 h₁]; decide)
    (by rv_eval [c₂.x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₃ := b80005764_keeps h₃
  have hm₃ := b80005764_frame h₃ (by addr_omega [hsb, c₂.x2])
  rw [c₂.x2] at hm₃
  obtain ⟨c₃, hn₃⟩ := c₂.block hpre hm₃ (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ k₃ r (mem_of_mem hr _)
  have K₃ := blockKeeps hpre c₂ hm₃ (by addr_omega [hsb]) (by addr_omega [hsb])
  have f₃ := K₃.2 _ _ f₂ (by omega)
  have bo := heldMono (K₃.1 _ _ _ _ b₂ (Nat.le_refl _) (Or.inl (by addr_omega [hsb]))
    (by addr_omega [hsb])) (l' := heapNext z) (h' := heapNext z₃) (by omega) (by omega)
  have ba : Held z₃ (s.getReg .x2 - 400) {} (heapNext z) (heapNext z) := held_empty
    (by have := b80005764_m_x2_80 h₃; rw [c₂.x2] at this; rv_eval [] at this ⊢; exact this)
    (by have := b80005764_m_x2_88 h₃; rw [c₂.x2, x19₂] at this; rv_eval [] at this ⊢; exact this)
    (by have := b80005764_m_x2_96 h₃; rw [c₂.x2] at this; rv_eval [] at this ⊢; exact this)
  have res₃ := K₃.1 _ _ _ _ res₂ (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  obtain ⟨w, hr₄, ⟨hpc₄, hp₄, c₄, hn₄, b₄, K₄⟩ | hd⟩ := addCall hA hpre c₃ (hr₂.trans hr₃)
    (b80005764_pc h₃) (o := s.getReg .x2 - 400) (e := s.getReg .x2 - 376)
    (by rw [b80005764_x10 h₃, c₂.x2]; rv_eval [])
    (by rw [b80005764_x11 h₃, c₂.x2, vecPtr, hm₃ (s.getReg .x2 - 376 + 8) (by addr_omega [hsb])];
        rv_eval [])
    (by rw [b80005764_x12 h₃, c₂.x2, vecLen, hm₃ (s.getReg .x2 - 376 + 16) (by addr_omega [hsb])];
        rv_eval [])
    (by rw [b80005764_x13 h₃, hp₂.reg .x18, k₁ .x18 (by decide), h18]) (by addr_omega [hsb])
    (by addr_omega [hsb]) ba bo c.mono (Nat.le_refl _) (by omega) (prodRust_terms _ _ _)
  swap
  · exact ⟨w, hr₄, Or.inr hd⟩
  refine ⟨w, hr₄, Or.inl ⟨by rw [hpc₄, returnAddress_eq, b80005764_x1 h₃]; decide, c₄, by omega,
    by rw [hp₄.reg .x9, k₃ .x9 (by decide), hp₂.reg .x9, k₁ .x9 (by decide), h9],
    by rw [hp₄.reg .x18, k₃ .x18 (by decide), hp₂.reg .x18, k₁ .x18 (by decide), h18],
    by rw [hp₄.reg .x19, k₃ .x19 (by decide), x19₂],
    K₄.2 _ _ f₃ (by omega), heldMono b₄ (by omega) (Nat.le_refl _),
    K₄.1 _ _ _ _ res₃ (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])⟩⟩

theorem mulInit3 (hP : ProdSpec) (hA : AddScaledSpec) {s u0 z : MachineState} {L0 : Nat}
    {fl : FlushesRust} {g : FormRust} {Lp : Nat} {g0 : FormRust}
    (hpre : FlushesArithPre s) (c : Inv s z)
    (hr : Reaches Image.code u0 z) (hpc : z.pc = 0x800058a8)
    (h9 : z.getReg .x9 = s.getReg .x2 - 376) (h18 : z.getReg .x18 = 0xa00000b0)
    (h19 : z.getReg .x19 = 8)
    (f : FHeld s z fl L0) (hL0 : L0 ≤ heapNext z)
    (bs : Held z (s.getReg .x2 - 400) g Lp (heapNext z))
    (r0 : Held z (s.getReg .x2 - 136) g0 L0 (heapNext z)) :
    ∃ w, Reaches Image.code u0 w ∧ ((w.pc = 0x800058fc ∧ Inv s w ∧ heapNext z ≤ heapNext w ∧
      w.getReg .x9 = s.getReg .x2 - 376 ∧ w.getReg .x18 = 0xa00000b0 ∧ w.getReg .x19 = 8 ∧
      FHeld s w fl L0 ∧
      Held w (s.getReg .x2 - 400) (({} : FormRust).add (prodRust 5 10 0)) (heapNext z)
        (heapNext w) ∧
      Held w (s.getReg .x2 - 136) g0 L0 (heapNext z) ∧
      Held w (s.getReg .x2 - 112) g Lp (heapNext z)) ∨ Dead Image.code w) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  have hhz := c.heap.hi
  obtain ⟨z₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800058a8_spec hpc
    (by rv_eval [x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₁ := b800058a8_keeps h₁
  have hm₁ := b800058a8_frame h₁ (by addr_omega [hsb, x2])
  rw [x2] at hm₁
  obtain ⟨c₁, hn₁⟩ := c.block hpre hm₁ (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ k₁ r (mem_of_mem hr _)
  have K₁ := blockKeeps hpre c hm₁ (by addr_omega [hsb]) (by addr_omega [hsb])
  have res₁ := moveHeld (e := s.getReg .x2 - 112) bs hm₁.dframe c.heap hn₁.ge
    (fun x hx _ ↦ by addr_omega [hx, hsb, hab, hhz])
    (by have := b800058a8_m_x2_368 h₁; rw [x2] at this; rv_eval [] at this ⊢; exact this)
    (by have := b800058a8_m_x2_376 h₁; rw [x2] at this; rv_eval [] at this ⊢; exact this)
    (by have := b800058a8_m_x2_384 h₁; rw [x2] at this; rv_eval [] at this ⊢; exact this)
  have h10₁ : z₁.getReg .x10 = s.getReg .x2 - 376 := by rw [b800058a8_x10 h₁, h9]
  have f₁ := K₁.2 _ _ f (by omega)
  have r0₁ := K₁.1 _ _ _ _ r0 (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  obtain ⟨z₂, hr₂, ⟨hpc₂, hp₂, hnew, hval⟩ | hd⟩ := hP.call (hr.trans hr₁) (b800058a8_pc h₁)
    (colPre hpre c₁ h10₁ (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb]))
  swap
  · exact ⟨z₂, hr₂, Or.inr hd⟩
  rw [h10₁] at hnew hval
  obtain ⟨c₂, hn₂, b₂, K₂⟩ := afterNew hpre c₁ (M := heapNext z₁) (Or.inl (by addr_omega [hsb]))
    (Nat.le_refl _) (Or.inl (by addr_omega [hsb, hab])) (by simp only [colStack, powStack]; decide)
    hp₂ hnew
  rw [hval, b800058a8_x11 h₁, b800058a8_x12 h₁, b800058a8_x13 h₁] at b₂
  have f₂ := K₂.2 _ _ f₁ (by omega)
  have r0₂ := K₂.1 _ _ _ _ r0₁ (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  have res₂ := K₂.1 _ _ _ _ res₁ (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  have x19₂ : z₂.getReg .x19 = 8 := by rw [hp₂.reg .x19, k₁ .x19 (by decide), h19]
  obtain ⟨z₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800058d8_spec
    (by rw [hpc₂, returnAddress_eq, b800058a8_x1 h₁]; decide)
    (by rv_eval [c₂.x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₃ := b800058d8_keeps h₃
  have hm₃ := b800058d8_frame h₃ (by addr_omega [hsb, c₂.x2])
  rw [c₂.x2] at hm₃
  obtain ⟨c₃, hn₃⟩ := c₂.block hpre hm₃ (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ k₃ r (mem_of_mem hr _)
  have K₃ := blockKeeps hpre c₂ hm₃ (by addr_omega [hsb]) (by addr_omega [hsb])
  have f₃ := K₃.2 _ _ f₂ (by omega)
  have bo := heldMono (K₃.1 _ _ _ _ b₂ (Nat.le_refl _) (Or.inl (by addr_omega [hsb]))
    (by addr_omega [hsb])) (l' := heapNext z) (h' := heapNext z₃) (by omega) (by omega)
  have ba : Held z₃ (s.getReg .x2 - 400) {} (heapNext z) (heapNext z) := held_empty
    (by have := b800058d8_m_x2_80 h₃; rw [c₂.x2] at this; rv_eval [] at this ⊢; exact this)
    (by have := b800058d8_m_x2_88 h₃; rw [c₂.x2, x19₂] at this; rv_eval [] at this ⊢; exact this)
    (by have := b800058d8_m_x2_96 h₃; rw [c₂.x2] at this; rv_eval [] at this ⊢; exact this)
  have r0₃ := K₃.1 _ _ _ _ r0₂ (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  have res₃ := K₃.1 _ _ _ _ res₂ (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  obtain ⟨w, hr₄, ⟨hpc₄, hp₄, c₄, hn₄, b₄, K₄⟩ | hd⟩ := addCall hA hpre c₃ (hr₂.trans hr₃)
    (b800058d8_pc h₃) (o := s.getReg .x2 - 400) (e := s.getReg .x2 - 376)
    (by rw [b800058d8_x10 h₃, c₂.x2]; rv_eval [])
    (by rw [b800058d8_x11 h₃, c₂.x2, vecPtr, hm₃ (s.getReg .x2 - 376 + 8) (by addr_omega [hsb])];
        rv_eval [])
    (by rw [b800058d8_x12 h₃, c₂.x2, vecLen, hm₃ (s.getReg .x2 - 376 + 16) (by addr_omega [hsb])];
        rv_eval [])
    (by rw [b800058d8_x13 h₃, hp₂.reg .x18, k₁ .x18 (by decide), h18]) (by addr_omega [hsb])
    (by addr_omega [hsb]) ba bo c.mono (Nat.le_refl _) (by omega) (prodRust_terms _ _ _)
  swap
  · exact ⟨w, hr₄, Or.inr hd⟩
  refine ⟨w, hr₄, Or.inl ⟨by rw [hpc₄, returnAddress_eq, b800058d8_x1 h₃]; decide, c₄, by omega,
    by rw [hp₄.reg .x9, k₃ .x9 (by decide), hp₂.reg .x9, k₁ .x9 (by decide), h9],
    by rw [hp₄.reg .x18, k₃ .x18 (by decide), hp₂.reg .x18, k₁ .x18 (by decide), h18],
    by rw [hp₄.reg .x19, k₃ .x19 (by decide), x19₂],
    K₄.2 _ _ f₃ (by omega), heldMono b₄ (by omega) (Nat.le_refl _),
    K₄.1 _ _ _ _ r0₃ (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb]),
    K₄.1 _ _ _ _ res₃ (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])⟩⟩

end Rv64Verifier.Layout.Arith
