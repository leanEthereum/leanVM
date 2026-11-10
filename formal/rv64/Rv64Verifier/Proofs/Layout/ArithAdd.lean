import Rv64Verifier.Proofs.Layout.ArithEnd

/-!
# `flushes_arith`: the sums, `multiply` false

Lane `i`: `col(sp' + 320, va[i], 0)`, `col(sp' + 80, vb[i], 0)`, `add_scaled(sp' + 320, sp' + 80,
ONE)`, the sum moved to `sp' + 152 + 24 i`; the last lane jumps to the `memcpy` from `sp' + 152`.
-/

namespace Rv64Verifier.Layout.Arith
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F19 Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Layout.Limb (Held)

theorem colRust_terms (i e : ℕ) : (colRust i e).terms ≠ [] := List.cons_ne_nil _ _
/-- Lane 0. -/
theorem addLane0 (hC : ColSpec) (hA : AddScaledSpec) {s u0 z : MachineState} {L : Nat}
    {fl : FlushesRust} (hpre : FlushesArithPre s) (c : Inv s z)
    (hr : Reaches Image.code u0 z)
    (hpc : z.pc = 0x80004b34) (h10 : z.getReg .x10 = s.getReg .x2 - 160) (h11 : z.getReg .x11 = 5)
    (h12 : z.getReg .x12 = 0) (h1 : z.getReg .x1 = 0x80005a08)
    (f : FHeld s z fl L) (hL : L ≤ heapNext z) :
    ∃ w, Reaches Image.code u0 w ∧ ((Inv s w ∧ L ≤ heapNext w ∧ w.pc = 0x80004b34 ∧
      w.getReg .x10 = s.getReg .x2 - 160 ∧ w.getReg .x11 = 6 ∧ w.getReg .x12 = 0 ∧
      w.getReg .x1 = 0x80005aa8 ∧ w.getReg .x9 = 0xa00000b0 ∧
      FHeld s w fl L ∧
      Held w (s.getReg .x2 - 328) ((colRust 5 0).add (colRust 8 0)) L (heapNext w)) ∨
      Dead Image.code w) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hm₀ := c.mono
  obtain ⟨t₁, hr₁, ⟨hpc₁, hp₁, c₁, hn₁, b₁, K₁⟩ | hd⟩ := colCall hC hpre c hr hpc h10
    (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb]) (Nat.le_refl _)
    (Or.inl (by addr_omega [hsb, hab]))
  swap
  · exact ⟨t₁, hr₁, Or.inr hd⟩
  rw [h11, h12] at b₁
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80005a08_spec
    (by rw [hpc₁, returnAddress_eq, h1]; decide) trivial
  have k₂ := b80005a08_keeps h₂
  have hm₂ := b80005a08_mem_same h₂
  have c₂ := c₁.same hpre hm₂ fun r hr ↦ k₂ r (mem_of_mem hr _)
  have K₂ := sameKeeps hpre c₁ hm₂
  have hn₂ : heapNext t₂ = heapNext t₁ := by simp only [heapNext, hm₂]
  obtain ⟨t₃, hr₃, ⟨hpc₃, hp₃, c₃, hn₃, b₃, K₃⟩ | hd⟩ := colCall hC hpre c₂ (hr₁.trans hr₂)
    (b80005a08_pc h₂) (o := s.getReg .x2 - 400) (by rw [b80005a08_x10 h₂, c₁.x2]; rv_eval [])
    (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb]) (Nat.le_refl _)
    (Or.inl (by addr_omega [hsb, hab]))
  swap
  · exact ⟨t₃, hr₃, Or.inr hd⟩
  rw [b80005a08_x11 h₂, b80005a08_x12 h₂] at b₃
  have b₁₃ := K₃.1 _ _ _ _ (K₂.1 _ _ _ _ b₁ (by omega) (Or.inl (by addr_omega [hsb]))
    (Or.inr (Or.inl rfl))) (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  have f₃ := K₃.2 _ _ (K₂.2 _ _ (K₁.2 _ _ f hL) (by omega)) (by omega)
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80005a1c_spec
    (by rw [hpc₃, returnAddress_eq, b80005a08_x1 h₂]; decide)
    (by rv_eval [c₃.x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₄ := b80005a1c_keeps h₄
  have hm₄ := b80005a1c_mem_same h₄
  have c₄ := c₃.same hpre hm₄ fun r hr ↦ k₄ r (mem_of_mem hr _)
  have K₄ := sameKeeps hpre c₃ hm₄
  have hn₄ : heapNext t₄ = heapNext t₃ := by simp only [heapNext, hm₄]
  have ba := K₄.1 _ _ _ _ b₁₃ (by omega) (Or.inl (by addr_omega [hsb])) (Or.inr (Or.inl rfl))
  have bo := heldMono (K₄.1 _ _ _ _ b₃ (by omega) (Or.inl (by addr_omega [hsb]))
    (Or.inr (Or.inl rfl))) (l' := heapNext t₁) (h' := heapNext t₄) (by omega) (by omega)
  obtain ⟨t₅, hr₅, ⟨hpc₅, hp₅, c₅, hn₅, b₅, K₅⟩ | hd⟩ := addCall hA hpre c₄ (hr₃.trans hr₄)
    (b80005a1c_pc h₄) (o := s.getReg .x2 - 160) (e := s.getReg .x2 - 400)
    (by rw [b80005a1c_x10 h₄, c₃.x2]; rv_eval [])
    (by rw [b80005a1c_x11 h₄, c₃.x2, vecPtr, hm₄]; rv_eval [])
    (by rw [b80005a1c_x12 h₄, c₃.x2, vecLen, hm₄]; rv_eval [])
    (by rw [b80005a1c_x13 h₄])
    (by addr_omega [hsb]) (by addr_omega [hsb]) ba bo (by omega) (by omega) (by omega)
    (colRust_terms _ _)
  swap
  · exact ⟨t₅, hr₅, Or.inr hd⟩
  have f₅ := K₅.2 _ _ (K₄.2 _ _ f₃ (by omega)) (by omega)
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b80005a3c_spec
    (by rw [hpc₅, returnAddress_eq, b80005a1c_x1 h₄]; decide)
    (by rv_eval [c₅.x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₆ := b80005a3c_keeps h₆
  have hm₆ := b80005a3c_frame h₆ (by addr_omega [hsb, c₅.x2])
  rw [c₅.x2] at hm₆
  obtain ⟨c₆, hn₆⟩ := c₅.block hpre hm₆ (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ k₆ r (mem_of_mem hr _)
  have K₆ := blockKeeps hpre c₅ hm₆ (by addr_omega [hsb]) (by addr_omega [hsb])
  have hres := moveHeld (e := s.getReg .x2 - 328) b₅ hm₆.dframe c₅.heap hn₆.ge
    (fun x hx _ ↦ by addr_omega [hx, hsb, hab, c₅.heap.hi])
    (by have := b80005a3c_m_x2_152 h₆; rw [c₅.x2] at this; rv_eval [] at this ⊢; exact this)
    (by have := b80005a3c_m_x2_160 h₆; rw [c₅.x2] at this; rv_eval [] at this ⊢; exact this)
    (by have := b80005a3c_m_x2_168 h₆; rw [c₅.x2] at this; rv_eval [] at this ⊢; exact this)
  refine ⟨t₆, hr₅.trans hr₆, Or.inl ⟨c₆, by omega, b80005a3c_pc h₆,
    by rw [b80005a3c_x10 h₆, c₅.x2]; rv_eval [],
    b80005a3c_x11 h₆, b80005a3c_x12 h₆, b80005a3c_x1 h₆,
    by rw [k₆ .x9 (by decide), hp₅.reg .x9, b80005a1c_x9 h₄],
    K₆.2 _ _ f₅ (by omega),
    heldMono hres (by omega) (by omega)⟩⟩

/-- Lane 1. -/
theorem addLane1 (hC : ColSpec) (hA : AddScaledSpec) {s u0 z : MachineState} {L : Nat}
    {fl : FlushesRust} {g0 : FormRust} (hpre : FlushesArithPre s) (c : Inv s z)
    (hr : Reaches Image.code u0 z)
    (hpc : z.pc = 0x80004b34) (h10 : z.getReg .x10 = s.getReg .x2 - 160) (h11 : z.getReg .x11 = 6)
    (h12 : z.getReg .x12 = 0) (h1 : z.getReg .x1 = 0x80005aa8)
    (h9 : z.getReg .x9 = 0xa00000b0)
    (f : FHeld s z fl L) (hL : L ≤ heapNext z)
    (r0 : Held z (s.getReg .x2 - 328) g0 L (heapNext z)) :
    ∃ w, Reaches Image.code u0 w ∧ ((Inv s w ∧ L ≤ heapNext w ∧ w.pc = 0x80004b34 ∧
      w.getReg .x10 = s.getReg .x2 - 160 ∧ w.getReg .x11 = 7 ∧ w.getReg .x12 = 0 ∧
      w.getReg .x1 = 0x80005b40 ∧ w.getReg .x9 = 0xa00000b0 ∧
      FHeld s w fl L ∧
      Held w (s.getReg .x2 - 328) g0 L (heapNext w) ∧
      Held w (s.getReg .x2 - 304) ((colRust 6 0).add (colRust 9 0)) L (heapNext w)) ∨
      Dead Image.code w) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hm₀ := c.mono
  obtain ⟨t₁, hr₁, ⟨hpc₁, hp₁, c₁, hn₁, b₁, K₁⟩ | hd⟩ := colCall hC hpre c hr hpc h10
    (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb]) (Nat.le_refl _)
    (Or.inl (by addr_omega [hsb, hab]))
  swap
  · exact ⟨t₁, hr₁, Or.inr hd⟩
  rw [h11, h12] at b₁
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80005aa8_spec
    (by rw [hpc₁, returnAddress_eq, h1]; decide) trivial
  have k₂ := b80005aa8_keeps h₂
  have hm₂ := b80005aa8_mem_same h₂
  have c₂ := c₁.same hpre hm₂ fun r hr ↦ k₂ r (mem_of_mem hr _)
  have K₂ := sameKeeps hpre c₁ hm₂
  have hn₂ : heapNext t₂ = heapNext t₁ := by simp only [heapNext, hm₂]
  obtain ⟨t₃, hr₃, ⟨hpc₃, hp₃, c₃, hn₃, b₃, K₃⟩ | hd⟩ := colCall hC hpre c₂ (hr₁.trans hr₂)
    (b80005aa8_pc h₂) (o := s.getReg .x2 - 400) (by rw [b80005aa8_x10 h₂, c₁.x2]; rv_eval [])
    (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb]) (Nat.le_refl _)
    (Or.inl (by addr_omega [hsb, hab]))
  swap
  · exact ⟨t₃, hr₃, Or.inr hd⟩
  rw [b80005aa8_x11 h₂, b80005aa8_x12 h₂] at b₃
  have b₁₃ := K₃.1 _ _ _ _ (K₂.1 _ _ _ _ b₁ (by omega) (Or.inl (by addr_omega [hsb]))
    (Or.inr (Or.inl rfl))) (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  have r0₃ := K₃.1 _ _ _ _ (K₂.1 _ _ _ _ (K₁.1 _ _ _ _ r0 (Nat.le_refl _)
    (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])) (by omega) (Or.inl (by addr_omega [hsb]))
    (Or.inr (Or.inl rfl))) (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  have f₃ := K₃.2 _ _ (K₂.2 _ _ (K₁.2 _ _ f hL) (by omega)) (by omega)
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80005abc_spec
    (by rw [hpc₃, returnAddress_eq, b80005aa8_x1 h₂]; decide)
    (by rv_eval [c₃.x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₄ := b80005abc_keeps h₄
  have hm₄ := b80005abc_mem_same h₄
  have c₄ := c₃.same hpre hm₄ fun r hr ↦ k₄ r (mem_of_mem hr _)
  have K₄ := sameKeeps hpre c₃ hm₄
  have hn₄ : heapNext t₄ = heapNext t₃ := by simp only [heapNext, hm₄]
  have ba := K₄.1 _ _ _ _ b₁₃ (by omega) (Or.inl (by addr_omega [hsb])) (Or.inr (Or.inl rfl))
  have bo := heldMono (K₄.1 _ _ _ _ b₃ (by omega) (Or.inl (by addr_omega [hsb]))
    (Or.inr (Or.inl rfl))) (l' := heapNext t₁) (h' := heapNext t₄) (by omega) (by omega)
  obtain ⟨t₅, hr₅, ⟨hpc₅, hp₅, c₅, hn₅, b₅, K₅⟩ | hd⟩ := addCall hA hpre c₄ (hr₃.trans hr₄)
    (b80005abc_pc h₄) (o := s.getReg .x2 - 160) (e := s.getReg .x2 - 400)
    (by rw [b80005abc_x10 h₄, c₃.x2]; rv_eval [])
    (by rw [b80005abc_x11 h₄, c₃.x2, vecPtr, hm₄]; rv_eval [])
    (by rw [b80005abc_x12 h₄, c₃.x2, vecLen, hm₄]; rv_eval [])
    (by rw [b80005abc_x13 h₄, hp₃.reg .x9, k₂ .x9 (by decide), hp₁.reg .x9, h9])
    (by addr_omega [hsb]) (by addr_omega [hsb]) ba bo (by omega) (by omega) (by omega)
    (colRust_terms _ _)
  swap
  · exact ⟨t₅, hr₅, Or.inr hd⟩
  have r0₅ := K₅.1 _ _ _ _ (K₄.1 _ _ _ _ r0₃ (by omega) (Or.inl (by addr_omega [hsb]))
    (Or.inr (Or.inl rfl))) (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  have f₅ := K₅.2 _ _ (K₄.2 _ _ f₃ (by omega)) (by omega)
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b80005ad4_spec
    (by rw [hpc₅, returnAddress_eq, b80005abc_x1 h₄]; decide)
    (by rv_eval [c₅.x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₆ := b80005ad4_keeps h₆
  have hm₆ := b80005ad4_frame h₆ (by addr_omega [hsb, c₅.x2])
  rw [c₅.x2] at hm₆
  obtain ⟨c₆, hn₆⟩ := c₅.block hpre hm₆ (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ k₆ r (mem_of_mem hr _)
  have K₆ := blockKeeps hpre c₅ hm₆ (by addr_omega [hsb]) (by addr_omega [hsb])
  have hres := moveHeld (e := s.getReg .x2 - 304) b₅ hm₆.dframe c₅.heap hn₆.ge
    (fun x hx _ ↦ by addr_omega [hx, hsb, hab, c₅.heap.hi])
    (by have := b80005ad4_m_x2_176 h₆; rw [c₅.x2] at this; rv_eval [] at this ⊢; exact this)
    (by have := b80005ad4_m_x2_184 h₆; rw [c₅.x2] at this; rv_eval [] at this ⊢; exact this)
    (by have := b80005ad4_m_x2_192 h₆; rw [c₅.x2] at this; rv_eval [] at this ⊢; exact this)
  refine ⟨t₆, hr₅.trans hr₆, Or.inl ⟨c₆, by omega, b80005ad4_pc h₆,
    by rw [b80005ad4_x10 h₆, c₅.x2]; rv_eval [],
    b80005ad4_x11 h₆, b80005ad4_x12 h₆, b80005ad4_x1 h₆,
    by rw [k₆ .x9 (by decide), hp₅.reg .x9, k₄ .x9 (by decide), hp₃.reg .x9,
      k₂ .x9 (by decide), hp₁.reg .x9, h9],
    K₆.2 _ _ f₅ (by omega),
    heldMono (K₆.1 _ _ _ _ r0₅ (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb]))
      (Nat.le_refl _) (by omega),
    heldMono hres (by omega) (by omega)⟩⟩

/-- Lane 2. -/
theorem addLane2 (hC : ColSpec) (hA : AddScaledSpec) {s u0 z : MachineState} {L : Nat}
    {fl : FlushesRust} {g0 g1 : FormRust} (hpre : FlushesArithPre s) (c : Inv s z)
    (hr : Reaches Image.code u0 z)
    (hpc : z.pc = 0x80004b34) (h10 : z.getReg .x10 = s.getReg .x2 - 160) (h11 : z.getReg .x11 = 7)
    (h12 : z.getReg .x12 = 0) (h1 : z.getReg .x1 = 0x80005b40)
    (h9 : z.getReg .x9 = 0xa00000b0)
    (f : FHeld s z fl L) (hL : L ≤ heapNext z)
    (r0 : Held z (s.getReg .x2 - 328) g0 L (heapNext z))
    (r1 : Held z (s.getReg .x2 - 304) g1 L (heapNext z)) :
    ∃ w, Reaches Image.code u0 w ∧ ((Inv s w ∧ L ≤ heapNext w ∧ w.pc = 0x80005bc8 ∧
      w.getReg .x11 = s.getReg .x2 - 328 ∧
      FHeld s w fl L ∧
      Held w (s.getReg .x2 - 328) g0 L (heapNext w) ∧
      Held w (s.getReg .x2 - 304) g1 L (heapNext w) ∧
      Held w (s.getReg .x2 - 280) ((colRust 7 0).add (colRust 10 0)) L (heapNext w)) ∨
      Dead Image.code w) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hm₀ := c.mono
  obtain ⟨t₁, hr₁, ⟨hpc₁, hp₁, c₁, hn₁, b₁, K₁⟩ | hd⟩ := colCall hC hpre c hr hpc h10
    (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb]) (Nat.le_refl _)
    (Or.inl (by addr_omega [hsb, hab]))
  swap
  · exact ⟨t₁, hr₁, Or.inr hd⟩
  rw [h11, h12] at b₁
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80005b40_spec
    (by rw [hpc₁, returnAddress_eq, h1]; decide) trivial
  have k₂ := b80005b40_keeps h₂
  have hm₂ := b80005b40_mem_same h₂
  have c₂ := c₁.same hpre hm₂ fun r hr ↦ k₂ r (mem_of_mem hr _)
  have K₂ := sameKeeps hpre c₁ hm₂
  have hn₂ : heapNext t₂ = heapNext t₁ := by simp only [heapNext, hm₂]
  obtain ⟨t₃, hr₃, ⟨hpc₃, hp₃, c₃, hn₃, b₃, K₃⟩ | hd⟩ := colCall hC hpre c₂ (hr₁.trans hr₂)
    (b80005b40_pc h₂) (o := s.getReg .x2 - 400) (by rw [b80005b40_x10 h₂, c₁.x2]; rv_eval [])
    (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb]) (Nat.le_refl _)
    (Or.inl (by addr_omega [hsb, hab]))
  swap
  · exact ⟨t₃, hr₃, Or.inr hd⟩
  rw [b80005b40_x11 h₂, b80005b40_x12 h₂] at b₃
  have b₁₃ := K₃.1 _ _ _ _ (K₂.1 _ _ _ _ b₁ (by omega) (Or.inl (by addr_omega [hsb]))
    (Or.inr (Or.inl rfl))) (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  have r0₃ := K₃.1 _ _ _ _ (K₂.1 _ _ _ _ (K₁.1 _ _ _ _ r0 (Nat.le_refl _)
    (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])) (by omega) (Or.inl (by addr_omega [hsb]))
    (Or.inr (Or.inl rfl))) (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  have r1₃ := K₃.1 _ _ _ _ (K₂.1 _ _ _ _ (K₁.1 _ _ _ _ r1 (Nat.le_refl _)
    (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])) (by omega) (Or.inl (by addr_omega [hsb]))
    (Or.inr (Or.inl rfl))) (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  have f₃ := K₃.2 _ _ (K₂.2 _ _ (K₁.2 _ _ f hL) (by omega)) (by omega)
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80005b54_spec
    (by rw [hpc₃, returnAddress_eq, b80005b40_x1 h₂]; decide)
    (by rv_eval [c₃.x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₄ := b80005b54_keeps h₄
  have hm₄ := b80005b54_mem_same h₄
  have c₄ := c₃.same hpre hm₄ fun r hr ↦ k₄ r (mem_of_mem hr _)
  have K₄ := sameKeeps hpre c₃ hm₄
  have hn₄ : heapNext t₄ = heapNext t₃ := by simp only [heapNext, hm₄]
  have ba := K₄.1 _ _ _ _ b₁₃ (by omega) (Or.inl (by addr_omega [hsb])) (Or.inr (Or.inl rfl))
  have bo := heldMono (K₄.1 _ _ _ _ b₃ (by omega) (Or.inl (by addr_omega [hsb]))
    (Or.inr (Or.inl rfl))) (l' := heapNext t₁) (h' := heapNext t₄) (by omega) (by omega)
  obtain ⟨t₅, hr₅, ⟨hpc₅, hp₅, c₅, hn₅, b₅, K₅⟩ | hd⟩ := addCall hA hpre c₄ (hr₃.trans hr₄)
    (b80005b54_pc h₄) (o := s.getReg .x2 - 160) (e := s.getReg .x2 - 400)
    (by rw [b80005b54_x10 h₄, c₃.x2]; rv_eval [])
    (by rw [b80005b54_x11 h₄, c₃.x2, vecPtr, hm₄]; rv_eval [])
    (by rw [b80005b54_x12 h₄, c₃.x2, vecLen, hm₄]; rv_eval [])
    (by rw [b80005b54_x13 h₄, hp₃.reg .x9, k₂ .x9 (by decide), hp₁.reg .x9, h9])
    (by addr_omega [hsb]) (by addr_omega [hsb]) ba bo (by omega) (by omega) (by omega)
    (colRust_terms _ _)
  swap
  · exact ⟨t₅, hr₅, Or.inr hd⟩
  have r0₅ := K₅.1 _ _ _ _ (K₄.1 _ _ _ _ r0₃ (by omega) (Or.inl (by addr_omega [hsb]))
    (Or.inr (Or.inl rfl))) (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  have r1₅ := K₅.1 _ _ _ _ (K₄.1 _ _ _ _ r1₃ (by omega) (Or.inl (by addr_omega [hsb]))
    (Or.inr (Or.inl rfl))) (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  have f₅ := K₅.2 _ _ (K₄.2 _ _ f₃ (by omega)) (by omega)
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b80005b6c_spec
    (by rw [hpc₅, returnAddress_eq, b80005b54_x1 h₄]; decide)
    (by rv_eval [c₅.x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₆ := b80005b6c_keeps h₆
  have hm₆ := b80005b6c_frame h₆ (by addr_omega [hsb, c₅.x2])
  rw [c₅.x2] at hm₆
  obtain ⟨c₆, hn₆⟩ := c₅.block hpre hm₆ (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ k₆ r (mem_of_mem hr _)
  have K₆ := blockKeeps hpre c₅ hm₆ (by addr_omega [hsb]) (by addr_omega [hsb])
  have hres := moveHeld (e := s.getReg .x2 - 280) b₅ hm₆.dframe c₅.heap hn₆.ge
    (fun x hx _ ↦ by addr_omega [hx, hsb, hab, c₅.heap.hi])
    (by have := b80005b6c_m_x2_200 h₆; rw [c₅.x2] at this; rv_eval [] at this ⊢; exact this)
    (by have := b80005b6c_m_x2_208 h₆; rw [c₅.x2] at this; rv_eval [] at this ⊢; exact this)
    (by have := b80005b6c_m_x2_216 h₆; rw [c₅.x2] at this; rv_eval [] at this ⊢; exact this)
  refine ⟨t₆, hr₅.trans hr₆, Or.inl ⟨c₆, by omega, b80005b6c_pc h₆,
    by rw [b80005b6c_x11 h₆, c₅.x2]; rv_eval [],
    K₆.2 _ _ f₅ (by omega),
    heldMono (K₆.1 _ _ _ _ r0₅ (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb]))
      (Nat.le_refl _) (by omega),
    heldMono (K₆.1 _ _ _ _ r1₅ (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb]))
      (Nat.le_refl _) (by omega),
    heldMono hres (by omega) (by omega)⟩⟩

end Rv64Verifier.Layout.Arith
