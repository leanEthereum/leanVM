import Rv64Verifier.Proofs.Layout.LimbBlocks

/-!
# `flushes_keccak`'s `limb` closure: one summand into the sum

The sum is `(a3, a4, a0)` (`Acc`); a site copies the summand's buffer and length to `sp' + 128`,
stores the sum at `sp' + 96` and calls `add_scaled`.
-/

namespace Rv64Verifier.Layout.Limb
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F13 Rv64Verifier.Model.LayoutMirror

/-- The empty `Form`, `(0, 8, 0)`. -/
theorem held_empty {v : MachineState} {e : Word} {lo hi : Nat} (h0 : v.getMem e = 0)
    (h8 : v.getMem (e + 8) = 8) (h16 : v.getMem (e + 16) = 0) : Held v e {} lo hi where
  ok := ⟨⟨by simp only [RawVecOk, Buf, vecPtr, vecCap, h0, h8]; exact ⟨by decide, Or.inl (by decide)⟩,
    by simp only [vecLen, vecCap, h0, h16]; exact Nat.le_refl _⟩, fun i hi ↦ by
      simp only [vecLen, h16] at hi; simp at hi⟩
  val := by simp only [formOf, vecLen, h16]; rfl
  buf := fun x hx ↦ by simp only [formBuf, vecPtr, vecCap, h0, h8] at hx; addr_omega [hx]

/-- The sum in `(a3, a4, a0)`: the words at `sp' + 96`, or the empty form. -/
def Acc (s z : MachineState) (H : Nat) (f : FormRust) : Prop :=
  (Held z (s.getReg .x2 - 112) f H (heapNext z) ∧ z.getReg .x13 = z.getMem (s.getReg .x2 - 112) ∧
    z.getReg .x14 = z.getMem (s.getReg .x2 - 104) ∧ z.getReg .x10 = z.getMem (s.getReg .x2 - 96)) ∨
  (f = {} ∧ z.getReg .x13 = 0 ∧ z.getReg .x14 = 8 ∧ z.getReg .x10 = 0)

/-- What a summing step keeps of the forms held below `H` in the locals under `sp' + 96`. -/
def KeepsBelow (s z v : MachineState) (H : Nat) : Prop :=
  ∀ e f l, Held z e f l H → (s.getReg .x2).toNat - 208 ≤ e.toNat →
    e.toNat + 24 ≤ (s.getReg .x2).toNat - 112 → Held v e f l H

/-- A site: the summand at `sp' + o - 8` into the sum, back at `T`. -/
theorem site (hA : AddScaledSpec) {s z : MachineState} (hpre : LimbPre s) (c : Inv s z)
    {H : Nat} (hH : heapNext s ≤ H) (hHz : H ≤ heapNext z) {o : Word} {r : Reg} {P M T : Word}
    (hcopy : Sym.BlockSpec Image.code P 5 (fun s ↦ Sym.Oblig.all s (copyE o M).obl) (copyE o M).Holds)
    (hstore : Sym.BlockSpec Image.code M 11 (fun s ↦ Sym.Oblig.all s (storeE r T).obl)
      (storeE r T).Holds)
    (hpc : z.pc = P) (x18 : z.getReg .x18 = s.getReg .x2 - 80) (ho : o = 32 ∨ o = 56)
    {f g : FormRust} (acc : Acc s z H f) (hg : g.terms ≠ [])
    (bg : Held z (s.getReg .x2 - 208 + (o - 8)) g (heapNext s) H) :
    ∃ v, Reaches Image.code z v ∧ ((v.pc = T &&& 0xfffffffffffffffe ∧ Inv s v ∧
      heapNext z ≤ heapNext v ∧
      (∀ r ∈ [Reg.x9, .x18, .x19, .x20, .x21, .x22], v.getReg r = z.getReg r) ∧
      Held v (s.getReg .x2 - 112) (f.add g) H (heapNext v) ∧ KeepsBelow s z v H) ∨
      Dead Image.code v) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  have hon : o.toNat = 32 ∨ o.toNat = 56 := by rcases ho with rfl | rfl <;> decide
  obtain ⟨z₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches hcopy hpc (by
    rv_eval [x2, x18]; and_intros <;> valid_access hpre.stack.valid [hsb, hon])
  have k₁ := h₁.keeps (rs := [.x1, .x2, .x8, .x9, .x10, .x13, .x14, .x18, .x19, .x20, .x21, .x22,
    .x23, .x24, .x25, .x26, .x27]) (by rcases ho with rfl | rfl <;> rfl)
  have hm₁ : MemFrame z z₁ (s.getReg .x2 - 80) 16 := h₁.memFrame (by
    simp only [copyE, List.mem_cons, List.not_mem_nil, or_false]
    rintro k (rfl | rfl) <;> rv_eval [x18] <;> addr_omega [hsb])
  have m₁0 := h₁.mem_eq 1 (by simp [copyE]) (a := s.getReg .x2 - 80)
    (v := z.getMem (s.getReg .x2 - 208 + o)) (by rv_eval [x18]) (by rv_eval [x2])
  have m₁8 := h₁.mem_eq 0 (by simp [copyE]) (a := s.getReg .x2 - 72)
    (v := z.getMem (s.getReg .x2 - 208 + (o + 8))) (by rv_eval [x18]) (by rv_eval [x2])
  have c₁ := c.block hpre hm₁ (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ k₁ r (mem_of_mem hr _)
  have hmono₁ : heapNext z₁ = heapNext z := by
    simp only [heapNext]; rw [hm₁ _ (by addr_omega [hnx, hsb])]
  have bg₁ := bg.block hpre c hm₁ (by addr_omega [hsb]) (by addr_omega [hsb])
    (by addr_omega [hsb, hon]) (by addr_omega [hsb, hon])
  have x2₁ : z₁.getReg .x2 = s.getReg .x2 - 208 := c₁.x2
  obtain ⟨u, hr₂, h₂⟩ := Sym.BlockSpec.reaches hstore (h₁.pc_eq rfl) (by
    rv_eval [x2₁]; and_intros <;> valid_access hpre.stack.valid [hsb])
  have k₂ := h₂.keeps (rs := [.x2, .x8, .x9, .x14, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25,
    .x26, .x27]) (by cases r <;> rfl)
  have hm₂ : MemFrame z₁ u (s.getReg .x2 - 112) 32 := h₂.memFrame (by
    simp only [storeE, List.mem_cons, List.not_mem_nil, or_false]
    rintro k (rfl | rfl | rfl | rfl) <;> rv_eval [x2₁] <;> addr_omega [hsb])
  have c₂ := c₁.block hpre hm₂ (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ k₂ r (mem_of_mem hr _)
  have hmono₂ : heapNext u = heapNext z₁ := by
    simp only [heapNext]; rw [hm₂ _ (by addr_omega [hnx, hsb])]
  have m₂96 := h₂.mem_eq 3 (by simp [storeE]) (a := s.getReg .x2 - 112) (v := z₁.getReg .x13)
    (by rv_eval [x2₁]) (by rv_eval [])
  have m₂104 := h₂.mem_eq 2 (by simp [storeE]) (a := s.getReg .x2 - 104) (v := z₁.getReg .x14)
    (by rv_eval [x2₁]) (by rv_eval [])
  have m₂112 := h₂.mem_eq 1 (by simp [storeE]) (a := s.getReg .x2 - 96) (v := z₁.getReg .x10)
    (by rv_eval [x2₁]) (by rv_eval [])
  have bg₂ := bg₁.block hpre c₁ hm₂ (by addr_omega [hsb]) (by addr_omega [hsb])
    (by addr_omega [hsb, hon]) (by addr_omega [hsb, hon])
  -- the sum, stored
  have ba : Held u (s.getReg .x2 - 112) f H (heapNext u) := by
    rw [hmono₂, hmono₁]
    rcases acc with ⟨b, a13, a14, a10⟩ | ⟨rfl, a13, a14, a10⟩
    · have b₁ := b.block hpre c hm₁ (by addr_omega [hsb]) (by addr_omega [hsb])
        (by addr_omega [hsb]) (by addr_omega [hsb])
      rw [← hmono₁] at b₁ ⊢
      refine b₁.blockMove hpre c₁ hm₂ (by addr_omega [hsb]) (by addr_omega [hsb]) ?_ ?_ ?_
      · rw [m₂96, k₁ .x13 (by decide), a13, hm₁ _ (by addr_omega [hsb])]
      · rw [show s.getReg .x2 - 112 + 8 = s.getReg .x2 - 104 by addr_omega [hsb], m₂104,
          k₁ .x14 (by decide), a14, hm₁ _ (by addr_omega [hsb])]
      · rw [show s.getReg .x2 - 112 + 16 = s.getReg .x2 - 96 by addr_omega [hsb], m₂112,
          k₁ .x10 (by decide), a10, hm₁ _ (by addr_omega [hsb])]
    · refine held_empty ?_ ?_ ?_
      · rw [m₂96, k₁ .x13 (by decide), a13]
      · rw [show s.getReg .x2 - 112 + 8 = s.getReg .x2 - 104 by addr_omega [hsb], m₂104,
          k₁ .x14 (by decide), a14]
      · rw [show s.getReg .x2 - 112 + 16 = s.getReg .x2 - 96 by addr_omega [hsb], m₂112,
          k₁ .x10 (by decide), a10]
  have hHu : H ≤ heapNext u := by rw [hmono₂, hmono₁]; exact hHz
  have y11 : u.getReg .x11 = vecPtr u (s.getReg .x2 - 208 + (o - 8)) := by
    rw [h₂.reg_eq (v := z₁.getMem (z₁.getReg .x2 + 128)) .x11 rfl (by rv_eval []), x2₁,
      show s.getReg .x2 - 208 + 128 = s.getReg .x2 - 80 by addr_omega [hsb], m₁0, vecPtr,
      hm₂ _ (by addr_omega [hsb, hon]), hm₁ _ (by addr_omega [hsb, hon])]
    congr 1; addr_omega [hsb, hon]
  have y12 : u.getReg .x12 = vecLen u (s.getReg .x2 - 208 + (o - 8)) := by
    rw [h₂.reg_eq (v := z₁.getMem (z₁.getReg .x2 + 136)) .x12 rfl (by rv_eval []), x2₁,
      show s.getReg .x2 - 208 + 136 = s.getReg .x2 - 72 by addr_omega [hsb], m₁8, vecLen,
      hm₂ _ (by addr_omega [hsb, hon]), hm₁ _ (by addr_omega [hsb, hon])]
    congr 1; addr_omega [hsb, hon]
  have y10 : u.getReg .x10 = s.getReg .x2 - 112 := by
    rw [h₂.reg_eq (v := z₁.getReg .x2 + 96) .x10 rfl (by rv_eval []), x2₁]; addr_omega [hsb]
  obtain ⟨v, hr₃, ⟨hpc₃, hp₃, c₃, hv₃, b₃, kp₃⟩ | hd⟩ := addCall hA hpre c₂ (hr₁.trans hr₂)
    (h₂.pc_eq rfl) y10 y11 y12 (h₂.reg_eq .x13 rfl (by rv_eval [])) ba bg₂ hH hHu hg
  swap
  · exact ⟨v, hr₃, Or.inr hd⟩
  refine ⟨v, hr₃, Or.inl ⟨by rw [hpc₃, returnAddress, h₂.reg_eq (v := T) .x1 rfl (by rv_eval [])]; rfl,
    c₃, by rw [hmono₂, hmono₁] at hv₃; exact hv₃, fun r hr ↦ by
      rw [hp₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)],
    b₃, fun e f' l b he₁ he₂ ↦ ?_⟩⟩
  have b₁ := b.block hpre c hm₁ (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb, he₂])
    (by addr_omega [hsb, he₂])
  exact kp₃ e f' l (b₁.block hpre c₁ hm₂ (by addr_omega [hsb]) (by addr_omega [hsb])
    (by addr_omega [hsb, he₂]) (by addr_omega [hsb, he₂])) he₁ (by omega) (by addr_omega [hsb, he₂])

end Rv64Verifier.Layout.Limb
