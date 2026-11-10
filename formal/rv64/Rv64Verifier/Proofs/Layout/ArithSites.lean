import Rv64Verifier.Proofs.Layout.ArithAdd

/-!
# `flushes_arith`: one summand of a product sum, `multiply` true

A site reads the sum's header from `sp' + 80` into three saved registers, calls `prod(sp' + 104,
a, b, 0)`, stores the header back unchanged and calls `add_scaled(sp' + 80, sp' + 104, ONE)`.
-/

namespace Rv64Verifier.Layout.Arith
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F19 Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Layout.Limb (Held)

theorem prodRust_terms (a b e : ℕ) : (prodRust a b e).terms ≠ [] := List.cons_ne_nil _ _

theorem slot_mono {s : MachineState} {M M' : Nat} {e : Word} (h : Slot s M e) (hM : M ≤ M') :
    Slot s M' e :=
  h.imp id fun h ↦ ⟨h.1, Nat.le_trans h.2 hM⟩

/-- The sum's header survives `prod`'s writes. -/
theorem sum_kept {s u v : MachineState} (hpre : FlushesArithPre s) (c : Inv s u) {n : Nat}
    (hn : n ≤ 1744) (hhv : heapNext v ≤ heapEnd)
    (hf : DFrame u v fun a ↦ Within a (s.getReg .x2 - 376) 24 ∨ Within a (stackLo u n) n ∨
      Within a nextAddr 8 ∨ Fresh u v a) {a : Word}
    (ha : (s.getReg .x2).toNat - 400 ≤ a.toNat ∧ a.toNat + 8 ≤ (s.getReg .x2).toNat - 376) :
    v.getMem a = u.getMem a := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  refine hf.getMem_of (fun x hx hw ↦ ?_) (by addr_omega [hsb, ha])
  rcases hw with h | h | h | h
  · addr_omega [hx, h, hsb, ha]
  · simp only [stackLo] at h; rw [x2] at h; addr_omega [hx, h, hsb, ha, hn]
  · addr_omega [hx, h, hsb, hnx, ha]
  · simp only [Fresh] at h; addr_omega [hx, h, hsb, hab, hhv, ha]

theorem mulSite_800056a4 (hP : ProdSpec) (hA : AddScaledSpec) {s u0 z : MachineState} {L : Nat}
    {f : FormRust} (hpre : FlushesArithPre s) (c : Inv s z) (hr : Reaches Image.code u0 z)
    (hpc : z.pc = 0x800056a4) (h9 : z.getReg .x9 = s.getReg .x2 - 376)
    (h18 : z.getReg .x18 = 0xa00000b0) (bs : Held z (s.getReg .x2 - 400) f L (heapNext z))
    (hL : heapNext s ≤ L) (hLz : L ≤ heapNext z) :
    ∃ w, Reaches Image.code u0 w ∧ ((w.pc = 0x800056ec ∧ Inv s w ∧ heapNext z ≤ heapNext w ∧
      w.getReg .x9 = z.getReg .x9 ∧ w.getReg .x18 = z.getReg .x18 ∧ w.getReg .x19 = z.getReg .x19 ∧
      Held w (s.getReg .x2 - 400) (f.add (prodRust 6 10 0)) L (heapNext w) ∧
      Keeps s z w (s.getReg .x2 - 400) 48 L) ∨ Dead Image.code w) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  obtain ⟨z₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800056a4_spec hpc
    (by rv_eval [x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₁ := b800056a4_keeps h₁
  have hm₁ := b800056a4_mem_same h₁
  have c₁ := c.same hpre hm₁ fun r hr ↦ k₁ r (mem_of_mem hr _)
  have K₁ := sameKeeps hpre c hm₁
  have hn₁ : heapNext z₁ = heapNext z := by simp only [heapNext, hm₁]
  have h10₁ : z₁.getReg .x10 = s.getReg .x2 - 376 := by rw [b800056a4_x10 h₁, h9]
  obtain ⟨z₂, hr₂, ⟨hpc₂, hp₂, hnew, hval⟩ | hd⟩ := hP.call (hr.trans hr₁) (b800056a4_pc h₁)
    (colPre hpre c₁ h10₁ (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb]))
  swap
  · exact ⟨z₂, hr₂, Or.inr hd⟩
  rw [h10₁] at hnew hval
  obtain ⟨c₂, hn₂, b₂, K₂⟩ := afterNew hpre c₁ (M := heapNext z₁) (Or.inl (by addr_omega [hsb]))
    (Nat.le_refl _) (Or.inl (by addr_omega [hsb, hab])) (by simp only [colStack, powStack]; decide)
    hp₂ hnew
  rw [hval, b800056a4_x11 h₁, b800056a4_x12 h₁, b800056a4_x13 h₁] at b₂
  have bs₂ := K₂.1 _ _ _ _ (K₁.1 _ _ _ _ bs (by omega) (Or.inl (by addr_omega [hsb]))
    (Or.inr (Or.inl rfl))) (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  obtain ⟨z₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800056c8_spec
    (by rw [hpc₂, returnAddress_eq, b800056a4_x1 h₁]; decide)
    (by rv_eval [c₂.x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₃ := b800056c8_keeps h₃
  have hm₃ := b800056c8_frame h₃ (by addr_omega [hsb, c₂.x2])
  rw [c₂.x2] at hm₃
  obtain ⟨c₃, hn₃⟩ := c₂.block hpre hm₃ (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ k₃ r (mem_of_mem hr _)
  have K₃ := blockKeeps hpre c₂ hm₃ (by addr_omega [hsb]) (by addr_omega [hsb])
  have bs₃ := moveHeld (e := s.getReg .x2 - 400) bs₂ hm₃.dframe c₂.heap hn₃.ge
    (fun x hx _ ↦ by addr_omega [hx, hsb, hab, c.heap.hi])
    (by
      have e1 := b800056c8_m_x2_80 h₃
      have e2 := b800056a4_x20 h₁
      rw [c₂.x2] at e1; rw [x2] at e2
      rv_eval [] at e1 e2 ⊢
      rw [e1, hp₂.reg .x20, e2, sum_kept hpre c₁ (by simp only [colStack, powStack]; decide)
        hnew.heap.hi hnew.frame (by addr_omega [hsb]), hm₁])
    (by
      have e1 := b800056c8_m_x2_88 h₃
      have e2 := b800056a4_x21 h₁
      rw [c₂.x2] at e1; rw [x2] at e2
      rv_eval [] at e1 e2 ⊢
      rw [e1, hp₂.reg .x21, e2, sum_kept hpre c₁ (by simp only [colStack, powStack]; decide)
        hnew.heap.hi hnew.frame (by addr_omega [hsb]), hm₁])
    (by
      have e1 := b800056c8_m_x2_96 h₃
      have e2 := b800056a4_x22 h₁
      rw [c₂.x2] at e1; rw [x2] at e2
      rv_eval [] at e1 e2 ⊢
      rw [e1, hp₂.reg .x22, e2, sum_kept hpre c₁ (by simp only [colStack, powStack]; decide)
        hnew.heap.hi hnew.frame (by addr_omega [hsb]), hm₁])
  have bo := heldMono (K₃.1 _ _ _ _ b₂ (Nat.le_refl _) (Or.inl (by addr_omega [hsb]))
    (by addr_omega [hsb])) (l' := heapNext z) (h' := heapNext z₃) (by omega) (by omega)
  obtain ⟨w, hr₄, ⟨hpc₄, hp₄, c₄, hn₄, b₄, K₄⟩ | hd⟩ := addCall hA hpre c₃ (hr₂.trans hr₃)
    (b800056c8_pc h₃) (o := s.getReg .x2 - 400) (e := s.getReg .x2 - 376)
    (by rw [b800056c8_x10 h₃, c₂.x2]; rv_eval [])
    (by rw [b800056c8_x11 h₃, c₂.x2, vecPtr, hm₃ (s.getReg .x2 - 376 + 8) (by addr_omega [hsb])];
        rv_eval [])
    (by rw [b800056c8_x12 h₃, c₂.x2, vecLen, hm₃ (s.getReg .x2 - 376 + 16) (by addr_omega [hsb])];
        rv_eval [])
    (by rw [b800056c8_x13 h₃, hp₂.reg .x18, k₁ .x18 (by decide), h18]) (by addr_omega [hsb])
    (by addr_omega [hsb]) bs₃ bo hL (by omega) (by omega) (prodRust_terms _ _ _)
  swap
  · exact ⟨w, hr₄, Or.inr hd⟩
  have hhz := c.heap.hi
  refine ⟨w, hr₄, Or.inl ⟨by rw [hpc₄, returnAddress_eq, b800056c8_x1 h₃]; decide, c₄, by omega,
    by rw [hp₄.reg .x9, k₃ .x9 (by decide), hp₂.reg .x9, k₁ .x9 (by decide)],
    by rw [hp₄.reg .x18, k₃ .x18 (by decide), hp₂.reg .x18, k₁ .x18 (by decide)],
    by rw [hp₄.reg .x19, k₃ .x19 (by decide), hp₂.reg .x19, k₁ .x19 (by decide)],
    b₄, fun e g l h b hh hs hap ↦ ?_, fun fl hi b hh ↦ ?_⟩⟩
  · have hs' : Loc s e ∨ (heapStart ≤ e.toNat ∧ e.toNat + 24 ≤ L) := hs
    have hap' : Apart e 24 (s.getReg .x2 - 400) 24 := by
      rcases hs' with h' | h' <;> addr_omega [hap, hsb, h', hhz, hLz]
    have hap'' : Apart e 24 (s.getReg .x2 - 376) 24 := by
      rcases hs' with h' | h' <;> addr_omega [hap, hsb, h', hhz, hLz]
    exact K₄.1 _ _ _ _ (K₃.1 _ _ _ _ (K₂.1 _ _ _ _ (K₁.1 _ _ _ _ b (by omega)
      (slot_mono hs (by omega)) (Or.inr (Or.inl rfl))) (by omega) (slot_mono hs (by omega)) hap'')
      (by omega) (slot_mono hs (by omega))
      (by rcases hs' with h' | h' <;> addr_omega [hap, hsb, h', hhz, hLz])) hh hs hap'
  · exact K₄.2 _ _ (K₃.2 _ _ (K₂.2 _ _ (K₁.2 _ _ b (by omega)) (by omega)) (by omega)) hh

theorem mulSite_800056ec (hP : ProdSpec) (hA : AddScaledSpec) {s u0 z : MachineState} {L : Nat}
    {f : FormRust} (hpre : FlushesArithPre s) (c : Inv s z) (hr : Reaches Image.code u0 z)
    (hpc : z.pc = 0x800056ec) (h9 : z.getReg .x9 = s.getReg .x2 - 376)
    (h18 : z.getReg .x18 = 0xa00000b0) (bs : Held z (s.getReg .x2 - 400) f L (heapNext z))
    (hL : heapNext s ≤ L) (hLz : L ≤ heapNext z) :
    ∃ w, Reaches Image.code u0 w ∧ ((w.pc = 0x80005734 ∧ Inv s w ∧ heapNext z ≤ heapNext w ∧
      w.getReg .x9 = z.getReg .x9 ∧ w.getReg .x18 = z.getReg .x18 ∧ w.getReg .x19 = z.getReg .x19 ∧
      Held w (s.getReg .x2 - 400) (f.add (prodRust 7 9 0)) L (heapNext w) ∧
      Keeps s z w (s.getReg .x2 - 400) 48 L) ∨ Dead Image.code w) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  obtain ⟨z₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800056ec_spec hpc
    (by rv_eval [x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₁ := b800056ec_keeps h₁
  have hm₁ := b800056ec_mem_same h₁
  have c₁ := c.same hpre hm₁ fun r hr ↦ k₁ r (mem_of_mem hr _)
  have K₁ := sameKeeps hpre c hm₁
  have hn₁ : heapNext z₁ = heapNext z := by simp only [heapNext, hm₁]
  have h10₁ : z₁.getReg .x10 = s.getReg .x2 - 376 := by rw [b800056ec_x10 h₁, h9]
  obtain ⟨z₂, hr₂, ⟨hpc₂, hp₂, hnew, hval⟩ | hd⟩ := hP.call (hr.trans hr₁) (b800056ec_pc h₁)
    (colPre hpre c₁ h10₁ (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb]))
  swap
  · exact ⟨z₂, hr₂, Or.inr hd⟩
  rw [h10₁] at hnew hval
  obtain ⟨c₂, hn₂, b₂, K₂⟩ := afterNew hpre c₁ (M := heapNext z₁) (Or.inl (by addr_omega [hsb]))
    (Nat.le_refl _) (Or.inl (by addr_omega [hsb, hab])) (by simp only [colStack, powStack]; decide)
    hp₂ hnew
  rw [hval, b800056ec_x11 h₁, b800056ec_x12 h₁, b800056ec_x13 h₁] at b₂
  have bs₂ := K₂.1 _ _ _ _ (K₁.1 _ _ _ _ bs (by omega) (Or.inl (by addr_omega [hsb]))
    (Or.inr (Or.inl rfl))) (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  obtain ⟨z₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80005710_spec
    (by rw [hpc₂, returnAddress_eq, b800056ec_x1 h₁]; decide)
    (by rv_eval [c₂.x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₃ := b80005710_keeps h₃
  have hm₃ := b80005710_frame h₃ (by addr_omega [hsb, c₂.x2])
  rw [c₂.x2] at hm₃
  obtain ⟨c₃, hn₃⟩ := c₂.block hpre hm₃ (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ k₃ r (mem_of_mem hr _)
  have K₃ := blockKeeps hpre c₂ hm₃ (by addr_omega [hsb]) (by addr_omega [hsb])
  have bs₃ := moveHeld (e := s.getReg .x2 - 400) bs₂ hm₃.dframe c₂.heap hn₃.ge
    (fun x hx _ ↦ by addr_omega [hx, hsb, hab, c.heap.hi])
    (by
      have e1 := b80005710_m_x2_80 h₃
      have e2 := b800056ec_x20 h₁
      rw [c₂.x2] at e1; rw [x2] at e2
      rv_eval [] at e1 e2 ⊢
      rw [e1, hp₂.reg .x20, e2, sum_kept hpre c₁ (by simp only [colStack, powStack]; decide)
        hnew.heap.hi hnew.frame (by addr_omega [hsb]), hm₁])
    (by
      have e1 := b80005710_m_x2_88 h₃
      have e2 := b800056ec_x21 h₁
      rw [c₂.x2] at e1; rw [x2] at e2
      rv_eval [] at e1 e2 ⊢
      rw [e1, hp₂.reg .x21, e2, sum_kept hpre c₁ (by simp only [colStack, powStack]; decide)
        hnew.heap.hi hnew.frame (by addr_omega [hsb]), hm₁])
    (by
      have e1 := b80005710_m_x2_96 h₃
      have e2 := b800056ec_x22 h₁
      rw [c₂.x2] at e1; rw [x2] at e2
      rv_eval [] at e1 e2 ⊢
      rw [e1, hp₂.reg .x22, e2, sum_kept hpre c₁ (by simp only [colStack, powStack]; decide)
        hnew.heap.hi hnew.frame (by addr_omega [hsb]), hm₁])
  have bo := heldMono (K₃.1 _ _ _ _ b₂ (Nat.le_refl _) (Or.inl (by addr_omega [hsb]))
    (by addr_omega [hsb])) (l' := heapNext z) (h' := heapNext z₃) (by omega) (by omega)
  obtain ⟨w, hr₄, ⟨hpc₄, hp₄, c₄, hn₄, b₄, K₄⟩ | hd⟩ := addCall hA hpre c₃ (hr₂.trans hr₃)
    (b80005710_pc h₃) (o := s.getReg .x2 - 400) (e := s.getReg .x2 - 376)
    (by rw [b80005710_x10 h₃, c₂.x2]; rv_eval [])
    (by rw [b80005710_x11 h₃, c₂.x2, vecPtr, hm₃ (s.getReg .x2 - 376 + 8) (by addr_omega [hsb])];
        rv_eval [])
    (by rw [b80005710_x12 h₃, c₂.x2, vecLen, hm₃ (s.getReg .x2 - 376 + 16) (by addr_omega [hsb])];
        rv_eval [])
    (by rw [b80005710_x13 h₃, hp₂.reg .x18, k₁ .x18 (by decide), h18]) (by addr_omega [hsb])
    (by addr_omega [hsb]) bs₃ bo hL (by omega) (by omega) (prodRust_terms _ _ _)
  swap
  · exact ⟨w, hr₄, Or.inr hd⟩
  have hhz := c.heap.hi
  refine ⟨w, hr₄, Or.inl ⟨by rw [hpc₄, returnAddress_eq, b80005710_x1 h₃]; decide, c₄, by omega,
    by rw [hp₄.reg .x9, k₃ .x9 (by decide), hp₂.reg .x9, k₁ .x9 (by decide)],
    by rw [hp₄.reg .x18, k₃ .x18 (by decide), hp₂.reg .x18, k₁ .x18 (by decide)],
    by rw [hp₄.reg .x19, k₃ .x19 (by decide), hp₂.reg .x19, k₁ .x19 (by decide)],
    b₄, fun e g l h b hh hs hap ↦ ?_, fun fl hi b hh ↦ ?_⟩⟩
  · have hs' : Loc s e ∨ (heapStart ≤ e.toNat ∧ e.toNat + 24 ≤ L) := hs
    have hap' : Apart e 24 (s.getReg .x2 - 400) 24 := by
      rcases hs' with h' | h' <;> addr_omega [hap, hsb, h', hhz, hLz]
    have hap'' : Apart e 24 (s.getReg .x2 - 376) 24 := by
      rcases hs' with h' | h' <;> addr_omega [hap, hsb, h', hhz, hLz]
    exact K₄.1 _ _ _ _ (K₃.1 _ _ _ _ (K₂.1 _ _ _ _ (K₁.1 _ _ _ _ b (by omega)
      (slot_mono hs (by omega)) (Or.inr (Or.inl rfl))) (by omega) (slot_mono hs (by omega)) hap'')
      (by omega) (slot_mono hs (by omega))
      (by rcases hs' with h' | h' <;> addr_omega [hap, hsb, h', hhz, hLz])) hh hs hap'
  · exact K₄.2 _ _ (K₃.2 _ _ (K₂.2 _ _ (K₁.2 _ _ b (by omega)) (by omega)) (by omega)) hh

theorem mulSite_80005788 (hP : ProdSpec) (hA : AddScaledSpec) {s u0 z : MachineState} {L : Nat}
    {f : FormRust} (hpre : FlushesArithPre s) (c : Inv s z) (hr : Reaches Image.code u0 z)
    (hpc : z.pc = 0x80005788) (h9 : z.getReg .x9 = s.getReg .x2 - 376)
    (h18 : z.getReg .x18 = 0xa00000b0) (bs : Held z (s.getReg .x2 - 400) f L (heapNext z))
    (hL : heapNext s ≤ L) (hLz : L ≤ heapNext z) :
    ∃ w, Reaches Image.code u0 w ∧ ((w.pc = 0x800057d0 ∧ Inv s w ∧ heapNext z ≤ heapNext w ∧
      w.getReg .x9 = z.getReg .x9 ∧ w.getReg .x18 = z.getReg .x18 ∧ w.getReg .x19 = z.getReg .x19 ∧
      Held w (s.getReg .x2 - 400) (f.add (prodRust 6 8 0)) L (heapNext w) ∧
      Keeps s z w (s.getReg .x2 - 400) 48 L) ∨ Dead Image.code w) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  obtain ⟨z₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80005788_spec hpc
    (by rv_eval [x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₁ := b80005788_keeps h₁
  have hm₁ := b80005788_mem_same h₁
  have c₁ := c.same hpre hm₁ fun r hr ↦ k₁ r (mem_of_mem hr _)
  have K₁ := sameKeeps hpre c hm₁
  have hn₁ : heapNext z₁ = heapNext z := by simp only [heapNext, hm₁]
  have h10₁ : z₁.getReg .x10 = s.getReg .x2 - 376 := by rw [b80005788_x10 h₁, h9]
  obtain ⟨z₂, hr₂, ⟨hpc₂, hp₂, hnew, hval⟩ | hd⟩ := hP.call (hr.trans hr₁) (b80005788_pc h₁)
    (colPre hpre c₁ h10₁ (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb]))
  swap
  · exact ⟨z₂, hr₂, Or.inr hd⟩
  rw [h10₁] at hnew hval
  obtain ⟨c₂, hn₂, b₂, K₂⟩ := afterNew hpre c₁ (M := heapNext z₁) (Or.inl (by addr_omega [hsb]))
    (Nat.le_refl _) (Or.inl (by addr_omega [hsb, hab])) (by simp only [colStack, powStack]; decide)
    hp₂ hnew
  rw [hval, b80005788_x11 h₁, b80005788_x12 h₁, b80005788_x13 h₁] at b₂
  have bs₂ := K₂.1 _ _ _ _ (K₁.1 _ _ _ _ bs (by omega) (Or.inl (by addr_omega [hsb]))
    (Or.inr (Or.inl rfl))) (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  obtain ⟨z₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800057ac_spec
    (by rw [hpc₂, returnAddress_eq, b80005788_x1 h₁]; decide)
    (by rv_eval [c₂.x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₃ := b800057ac_keeps h₃
  have hm₃ := b800057ac_frame h₃ (by addr_omega [hsb, c₂.x2])
  rw [c₂.x2] at hm₃
  obtain ⟨c₃, hn₃⟩ := c₂.block hpre hm₃ (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ k₃ r (mem_of_mem hr _)
  have K₃ := blockKeeps hpre c₂ hm₃ (by addr_omega [hsb]) (by addr_omega [hsb])
  have bs₃ := moveHeld (e := s.getReg .x2 - 400) bs₂ hm₃.dframe c₂.heap hn₃.ge
    (fun x hx _ ↦ by addr_omega [hx, hsb, hab, c.heap.hi])
    (by
      have e1 := b800057ac_m_x2_80 h₃
      have e2 := b80005788_x20 h₁
      rw [c₂.x2] at e1; rw [x2] at e2
      rv_eval [] at e1 e2 ⊢
      rw [e1, hp₂.reg .x20, e2, sum_kept hpre c₁ (by simp only [colStack, powStack]; decide)
        hnew.heap.hi hnew.frame (by addr_omega [hsb]), hm₁])
    (by
      have e1 := b800057ac_m_x2_88 h₃
      have e2 := b80005788_x21 h₁
      rw [c₂.x2] at e1; rw [x2] at e2
      rv_eval [] at e1 e2 ⊢
      rw [e1, hp₂.reg .x21, e2, sum_kept hpre c₁ (by simp only [colStack, powStack]; decide)
        hnew.heap.hi hnew.frame (by addr_omega [hsb]), hm₁])
    (by
      have e1 := b800057ac_m_x2_96 h₃
      have e2 := b80005788_x22 h₁
      rw [c₂.x2] at e1; rw [x2] at e2
      rv_eval [] at e1 e2 ⊢
      rw [e1, hp₂.reg .x22, e2, sum_kept hpre c₁ (by simp only [colStack, powStack]; decide)
        hnew.heap.hi hnew.frame (by addr_omega [hsb]), hm₁])
  have bo := heldMono (K₃.1 _ _ _ _ b₂ (Nat.le_refl _) (Or.inl (by addr_omega [hsb]))
    (by addr_omega [hsb])) (l' := heapNext z) (h' := heapNext z₃) (by omega) (by omega)
  obtain ⟨w, hr₄, ⟨hpc₄, hp₄, c₄, hn₄, b₄, K₄⟩ | hd⟩ := addCall hA hpre c₃ (hr₂.trans hr₃)
    (b800057ac_pc h₃) (o := s.getReg .x2 - 400) (e := s.getReg .x2 - 376)
    (by rw [b800057ac_x10 h₃, c₂.x2]; rv_eval [])
    (by rw [b800057ac_x11 h₃, c₂.x2, vecPtr, hm₃ (s.getReg .x2 - 376 + 8) (by addr_omega [hsb])];
        rv_eval [])
    (by rw [b800057ac_x12 h₃, c₂.x2, vecLen, hm₃ (s.getReg .x2 - 376 + 16) (by addr_omega [hsb])];
        rv_eval [])
    (by rw [b800057ac_x13 h₃, hp₂.reg .x18, k₁ .x18 (by decide), h18]) (by addr_omega [hsb])
    (by addr_omega [hsb]) bs₃ bo hL (by omega) (by omega) (prodRust_terms _ _ _)
  swap
  · exact ⟨w, hr₄, Or.inr hd⟩
  have hhz := c.heap.hi
  refine ⟨w, hr₄, Or.inl ⟨by rw [hpc₄, returnAddress_eq, b800057ac_x1 h₃]; decide, c₄, by omega,
    by rw [hp₄.reg .x9, k₃ .x9 (by decide), hp₂.reg .x9, k₁ .x9 (by decide)],
    by rw [hp₄.reg .x18, k₃ .x18 (by decide), hp₂.reg .x18, k₁ .x18 (by decide)],
    by rw [hp₄.reg .x19, k₃ .x19 (by decide), hp₂.reg .x19, k₁ .x19 (by decide)],
    b₄, fun e g l h b hh hs hap ↦ ?_, fun fl hi b hh ↦ ?_⟩⟩
  · have hs' : Loc s e ∨ (heapStart ≤ e.toNat ∧ e.toNat + 24 ≤ L) := hs
    have hap' : Apart e 24 (s.getReg .x2 - 400) 24 := by
      rcases hs' with h' | h' <;> addr_omega [hap, hsb, h', hhz, hLz]
    have hap'' : Apart e 24 (s.getReg .x2 - 376) 24 := by
      rcases hs' with h' | h' <;> addr_omega [hap, hsb, h', hhz, hLz]
    exact K₄.1 _ _ _ _ (K₃.1 _ _ _ _ (K₂.1 _ _ _ _ (K₁.1 _ _ _ _ b (by omega)
      (slot_mono hs (by omega)) (Or.inr (Or.inl rfl))) (by omega) (slot_mono hs (by omega)) hap'')
      (by omega) (slot_mono hs (by omega))
      (by rcases hs' with h' | h' <;> addr_omega [hap, hsb, h', hhz, hLz])) hh hs hap'
  · exact K₄.2 _ _ (K₃.2 _ _ (K₂.2 _ _ (K₁.2 _ _ b (by omega)) (by omega)) (by omega)) hh

theorem mulSite_800057d0 (hP : ProdSpec) (hA : AddScaledSpec) {s u0 z : MachineState} {L : Nat}
    {f : FormRust} (hpre : FlushesArithPre s) (c : Inv s z) (hr : Reaches Image.code u0 z)
    (hpc : z.pc = 0x800057d0) (h9 : z.getReg .x9 = s.getReg .x2 - 376)
    (h18 : z.getReg .x18 = 0xa00000b0) (bs : Held z (s.getReg .x2 - 400) f L (heapNext z))
    (hL : heapNext s ≤ L) (hLz : L ≤ heapNext z) :
    ∃ w, Reaches Image.code u0 w ∧ ((w.pc = 0x80005818 ∧ Inv s w ∧ heapNext z ≤ heapNext w ∧
      w.getReg .x9 = z.getReg .x9 ∧ w.getReg .x18 = z.getReg .x18 ∧ w.getReg .x19 = z.getReg .x19 ∧
      Held w (s.getReg .x2 - 400) (f.add (prodRust 6 10 0)) L (heapNext w) ∧
      Keeps s z w (s.getReg .x2 - 400) 48 L) ∨ Dead Image.code w) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  obtain ⟨z₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800057d0_spec hpc
    (by rv_eval [x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₁ := b800057d0_keeps h₁
  have hm₁ := b800057d0_mem_same h₁
  have c₁ := c.same hpre hm₁ fun r hr ↦ k₁ r (mem_of_mem hr _)
  have K₁ := sameKeeps hpre c hm₁
  have hn₁ : heapNext z₁ = heapNext z := by simp only [heapNext, hm₁]
  have h10₁ : z₁.getReg .x10 = s.getReg .x2 - 376 := by rw [b800057d0_x10 h₁, h9]
  obtain ⟨z₂, hr₂, ⟨hpc₂, hp₂, hnew, hval⟩ | hd⟩ := hP.call (hr.trans hr₁) (b800057d0_pc h₁)
    (colPre hpre c₁ h10₁ (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb]))
  swap
  · exact ⟨z₂, hr₂, Or.inr hd⟩
  rw [h10₁] at hnew hval
  obtain ⟨c₂, hn₂, b₂, K₂⟩ := afterNew hpre c₁ (M := heapNext z₁) (Or.inl (by addr_omega [hsb]))
    (Nat.le_refl _) (Or.inl (by addr_omega [hsb, hab])) (by simp only [colStack, powStack]; decide)
    hp₂ hnew
  rw [hval, b800057d0_x11 h₁, b800057d0_x12 h₁, b800057d0_x13 h₁] at b₂
  have bs₂ := K₂.1 _ _ _ _ (K₁.1 _ _ _ _ bs (by omega) (Or.inl (by addr_omega [hsb]))
    (Or.inr (Or.inl rfl))) (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  obtain ⟨z₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800057f4_spec
    (by rw [hpc₂, returnAddress_eq, b800057d0_x1 h₁]; decide)
    (by rv_eval [c₂.x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₃ := b800057f4_keeps h₃
  have hm₃ := b800057f4_frame h₃ (by addr_omega [hsb, c₂.x2])
  rw [c₂.x2] at hm₃
  obtain ⟨c₃, hn₃⟩ := c₂.block hpre hm₃ (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ k₃ r (mem_of_mem hr _)
  have K₃ := blockKeeps hpre c₂ hm₃ (by addr_omega [hsb]) (by addr_omega [hsb])
  have bs₃ := moveHeld (e := s.getReg .x2 - 400) bs₂ hm₃.dframe c₂.heap hn₃.ge
    (fun x hx _ ↦ by addr_omega [hx, hsb, hab, c.heap.hi])
    (by
      have e1 := b800057f4_m_x2_80 h₃
      have e2 := b800057d0_x20 h₁
      rw [c₂.x2] at e1; rw [x2] at e2
      rv_eval [] at e1 e2 ⊢
      rw [e1, hp₂.reg .x20, e2, sum_kept hpre c₁ (by simp only [colStack, powStack]; decide)
        hnew.heap.hi hnew.frame (by addr_omega [hsb]), hm₁])
    (by
      have e1 := b800057f4_m_x2_88 h₃
      have e2 := b800057d0_x21 h₁
      rw [c₂.x2] at e1; rw [x2] at e2
      rv_eval [] at e1 e2 ⊢
      rw [e1, hp₂.reg .x21, e2, sum_kept hpre c₁ (by simp only [colStack, powStack]; decide)
        hnew.heap.hi hnew.frame (by addr_omega [hsb]), hm₁])
    (by
      have e1 := b800057f4_m_x2_96 h₃
      have e2 := b800057d0_x22 h₁
      rw [c₂.x2] at e1; rw [x2] at e2
      rv_eval [] at e1 e2 ⊢
      rw [e1, hp₂.reg .x22, e2, sum_kept hpre c₁ (by simp only [colStack, powStack]; decide)
        hnew.heap.hi hnew.frame (by addr_omega [hsb]), hm₁])
  have bo := heldMono (K₃.1 _ _ _ _ b₂ (Nat.le_refl _) (Or.inl (by addr_omega [hsb]))
    (by addr_omega [hsb])) (l' := heapNext z) (h' := heapNext z₃) (by omega) (by omega)
  obtain ⟨w, hr₄, ⟨hpc₄, hp₄, c₄, hn₄, b₄, K₄⟩ | hd⟩ := addCall hA hpre c₃ (hr₂.trans hr₃)
    (b800057f4_pc h₃) (o := s.getReg .x2 - 400) (e := s.getReg .x2 - 376)
    (by rw [b800057f4_x10 h₃, c₂.x2]; rv_eval [])
    (by rw [b800057f4_x11 h₃, c₂.x2, vecPtr, hm₃ (s.getReg .x2 - 376 + 8) (by addr_omega [hsb])];
        rv_eval [])
    (by rw [b800057f4_x12 h₃, c₂.x2, vecLen, hm₃ (s.getReg .x2 - 376 + 16) (by addr_omega [hsb])];
        rv_eval [])
    (by rw [b800057f4_x13 h₃, hp₂.reg .x18, k₁ .x18 (by decide), h18]) (by addr_omega [hsb])
    (by addr_omega [hsb]) bs₃ bo hL (by omega) (by omega) (prodRust_terms _ _ _)
  swap
  · exact ⟨w, hr₄, Or.inr hd⟩
  have hhz := c.heap.hi
  refine ⟨w, hr₄, Or.inl ⟨by rw [hpc₄, returnAddress_eq, b800057f4_x1 h₃]; decide, c₄, by omega,
    by rw [hp₄.reg .x9, k₃ .x9 (by decide), hp₂.reg .x9, k₁ .x9 (by decide)],
    by rw [hp₄.reg .x18, k₃ .x18 (by decide), hp₂.reg .x18, k₁ .x18 (by decide)],
    by rw [hp₄.reg .x19, k₃ .x19 (by decide), hp₂.reg .x19, k₁ .x19 (by decide)],
    b₄, fun e g l h b hh hs hap ↦ ?_, fun fl hi b hh ↦ ?_⟩⟩
  · have hs' : Loc s e ∨ (heapStart ≤ e.toNat ∧ e.toNat + 24 ≤ L) := hs
    have hap' : Apart e 24 (s.getReg .x2 - 400) 24 := by
      rcases hs' with h' | h' <;> addr_omega [hap, hsb, h', hhz, hLz]
    have hap'' : Apart e 24 (s.getReg .x2 - 376) 24 := by
      rcases hs' with h' | h' <;> addr_omega [hap, hsb, h', hhz, hLz]
    exact K₄.1 _ _ _ _ (K₃.1 _ _ _ _ (K₂.1 _ _ _ _ (K₁.1 _ _ _ _ b (by omega)
      (slot_mono hs (by omega)) (Or.inr (Or.inl rfl))) (by omega) (slot_mono hs (by omega)) hap'')
      (by omega) (slot_mono hs (by omega))
      (by rcases hs' with h' | h' <;> addr_omega [hap, hsb, h', hhz, hLz])) hh hs hap'
  · exact K₄.2 _ _ (K₃.2 _ _ (K₂.2 _ _ (K₁.2 _ _ b (by omega)) (by omega)) (by omega)) hh

theorem mulSite_80005818 (hP : ProdSpec) (hA : AddScaledSpec) {s u0 z : MachineState} {L : Nat}
    {f : FormRust} (hpre : FlushesArithPre s) (c : Inv s z) (hr : Reaches Image.code u0 z)
    (hpc : z.pc = 0x80005818) (h9 : z.getReg .x9 = s.getReg .x2 - 376)
    (h18 : z.getReg .x18 = 0xa00000b0) (bs : Held z (s.getReg .x2 - 400) f L (heapNext z))
    (hL : heapNext s ≤ L) (hLz : L ≤ heapNext z) :
    ∃ w, Reaches Image.code u0 w ∧ ((w.pc = 0x80005860 ∧ Inv s w ∧ heapNext z ≤ heapNext w ∧
      w.getReg .x9 = z.getReg .x9 ∧ w.getReg .x18 = z.getReg .x18 ∧ w.getReg .x19 = z.getReg .x19 ∧
      Held w (s.getReg .x2 - 400) (f.add (prodRust 7 9 0)) L (heapNext w) ∧
      Keeps s z w (s.getReg .x2 - 400) 48 L) ∨ Dead Image.code w) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  obtain ⟨z₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80005818_spec hpc
    (by rv_eval [x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₁ := b80005818_keeps h₁
  have hm₁ := b80005818_mem_same h₁
  have c₁ := c.same hpre hm₁ fun r hr ↦ k₁ r (mem_of_mem hr _)
  have K₁ := sameKeeps hpre c hm₁
  have hn₁ : heapNext z₁ = heapNext z := by simp only [heapNext, hm₁]
  have h10₁ : z₁.getReg .x10 = s.getReg .x2 - 376 := by rw [b80005818_x10 h₁, h9]
  obtain ⟨z₂, hr₂, ⟨hpc₂, hp₂, hnew, hval⟩ | hd⟩ := hP.call (hr.trans hr₁) (b80005818_pc h₁)
    (colPre hpre c₁ h10₁ (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb]))
  swap
  · exact ⟨z₂, hr₂, Or.inr hd⟩
  rw [h10₁] at hnew hval
  obtain ⟨c₂, hn₂, b₂, K₂⟩ := afterNew hpre c₁ (M := heapNext z₁) (Or.inl (by addr_omega [hsb]))
    (Nat.le_refl _) (Or.inl (by addr_omega [hsb, hab])) (by simp only [colStack, powStack]; decide)
    hp₂ hnew
  rw [hval, b80005818_x11 h₁, b80005818_x12 h₁, b80005818_x13 h₁] at b₂
  have bs₂ := K₂.1 _ _ _ _ (K₁.1 _ _ _ _ bs (by omega) (Or.inl (by addr_omega [hsb]))
    (Or.inr (Or.inl rfl))) (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  obtain ⟨z₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000583c_spec
    (by rw [hpc₂, returnAddress_eq, b80005818_x1 h₁]; decide)
    (by rv_eval [c₂.x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₃ := b8000583c_keeps h₃
  have hm₃ := b8000583c_frame h₃ (by addr_omega [hsb, c₂.x2])
  rw [c₂.x2] at hm₃
  obtain ⟨c₃, hn₃⟩ := c₂.block hpre hm₃ (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ k₃ r (mem_of_mem hr _)
  have K₃ := blockKeeps hpre c₂ hm₃ (by addr_omega [hsb]) (by addr_omega [hsb])
  have bs₃ := moveHeld (e := s.getReg .x2 - 400) bs₂ hm₃.dframe c₂.heap hn₃.ge
    (fun x hx _ ↦ by addr_omega [hx, hsb, hab, c.heap.hi])
    (by
      have e1 := b8000583c_m_x2_80 h₃
      have e2 := b80005818_x20 h₁
      rw [c₂.x2] at e1; rw [x2] at e2
      rv_eval [] at e1 e2 ⊢
      rw [e1, hp₂.reg .x20, e2, sum_kept hpre c₁ (by simp only [colStack, powStack]; decide)
        hnew.heap.hi hnew.frame (by addr_omega [hsb]), hm₁])
    (by
      have e1 := b8000583c_m_x2_88 h₃
      have e2 := b80005818_x21 h₁
      rw [c₂.x2] at e1; rw [x2] at e2
      rv_eval [] at e1 e2 ⊢
      rw [e1, hp₂.reg .x21, e2, sum_kept hpre c₁ (by simp only [colStack, powStack]; decide)
        hnew.heap.hi hnew.frame (by addr_omega [hsb]), hm₁])
    (by
      have e1 := b8000583c_m_x2_96 h₃
      have e2 := b80005818_x22 h₁
      rw [c₂.x2] at e1; rw [x2] at e2
      rv_eval [] at e1 e2 ⊢
      rw [e1, hp₂.reg .x22, e2, sum_kept hpre c₁ (by simp only [colStack, powStack]; decide)
        hnew.heap.hi hnew.frame (by addr_omega [hsb]), hm₁])
  have bo := heldMono (K₃.1 _ _ _ _ b₂ (Nat.le_refl _) (Or.inl (by addr_omega [hsb]))
    (by addr_omega [hsb])) (l' := heapNext z) (h' := heapNext z₃) (by omega) (by omega)
  obtain ⟨w, hr₄, ⟨hpc₄, hp₄, c₄, hn₄, b₄, K₄⟩ | hd⟩ := addCall hA hpre c₃ (hr₂.trans hr₃)
    (b8000583c_pc h₃) (o := s.getReg .x2 - 400) (e := s.getReg .x2 - 376)
    (by rw [b8000583c_x10 h₃, c₂.x2]; rv_eval [])
    (by rw [b8000583c_x11 h₃, c₂.x2, vecPtr, hm₃ (s.getReg .x2 - 376 + 8) (by addr_omega [hsb])];
        rv_eval [])
    (by rw [b8000583c_x12 h₃, c₂.x2, vecLen, hm₃ (s.getReg .x2 - 376 + 16) (by addr_omega [hsb])];
        rv_eval [])
    (by rw [b8000583c_x13 h₃, hp₂.reg .x18, k₁ .x18 (by decide), h18]) (by addr_omega [hsb])
    (by addr_omega [hsb]) bs₃ bo hL (by omega) (by omega) (prodRust_terms _ _ _)
  swap
  · exact ⟨w, hr₄, Or.inr hd⟩
  have hhz := c.heap.hi
  refine ⟨w, hr₄, Or.inl ⟨by rw [hpc₄, returnAddress_eq, b8000583c_x1 h₃]; decide, c₄, by omega,
    by rw [hp₄.reg .x9, k₃ .x9 (by decide), hp₂.reg .x9, k₁ .x9 (by decide)],
    by rw [hp₄.reg .x18, k₃ .x18 (by decide), hp₂.reg .x18, k₁ .x18 (by decide)],
    by rw [hp₄.reg .x19, k₃ .x19 (by decide), hp₂.reg .x19, k₁ .x19 (by decide)],
    b₄, fun e g l h b hh hs hap ↦ ?_, fun fl hi b hh ↦ ?_⟩⟩
  · have hs' : Loc s e ∨ (heapStart ≤ e.toNat ∧ e.toNat + 24 ≤ L) := hs
    have hap' : Apart e 24 (s.getReg .x2 - 400) 24 := by
      rcases hs' with h' | h' <;> addr_omega [hap, hsb, h', hhz, hLz]
    have hap'' : Apart e 24 (s.getReg .x2 - 376) 24 := by
      rcases hs' with h' | h' <;> addr_omega [hap, hsb, h', hhz, hLz]
    exact K₄.1 _ _ _ _ (K₃.1 _ _ _ _ (K₂.1 _ _ _ _ (K₁.1 _ _ _ _ b (by omega)
      (slot_mono hs (by omega)) (Or.inr (Or.inl rfl))) (by omega) (slot_mono hs (by omega)) hap'')
      (by omega) (slot_mono hs (by omega))
      (by rcases hs' with h' | h' <;> addr_omega [hap, hsb, h', hhz, hLz])) hh hs hap'
  · exact K₄.2 _ _ (K₃.2 _ _ (K₂.2 _ _ (K₁.2 _ _ b (by omega)) (by omega)) (by omega)) hh

theorem mulSite_80005860 (hP : ProdSpec) (hA : AddScaledSpec) {s u0 z : MachineState} {L : Nat}
    {f : FormRust} (hpre : FlushesArithPre s) (c : Inv s z) (hr : Reaches Image.code u0 z)
    (hpc : z.pc = 0x80005860) (h9 : z.getReg .x9 = s.getReg .x2 - 376)
    (h18 : z.getReg .x18 = 0xa00000b0) (bs : Held z (s.getReg .x2 - 400) f L (heapNext z))
    (hL : heapNext s ≤ L) (hLz : L ≤ heapNext z) :
    ∃ w, Reaches Image.code u0 w ∧ ((w.pc = 0x800058a8 ∧ Inv s w ∧ heapNext z ≤ heapNext w ∧
      w.getReg .x9 = z.getReg .x9 ∧ w.getReg .x18 = z.getReg .x18 ∧ w.getReg .x19 = z.getReg .x19 ∧
      Held w (s.getReg .x2 - 400) (f.add (prodRust 7 10 0)) L (heapNext w) ∧
      Keeps s z w (s.getReg .x2 - 400) 48 L) ∨ Dead Image.code w) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  obtain ⟨z₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80005860_spec hpc
    (by rv_eval [x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₁ := b80005860_keeps h₁
  have hm₁ := b80005860_mem_same h₁
  have c₁ := c.same hpre hm₁ fun r hr ↦ k₁ r (mem_of_mem hr _)
  have K₁ := sameKeeps hpre c hm₁
  have hn₁ : heapNext z₁ = heapNext z := by simp only [heapNext, hm₁]
  have h10₁ : z₁.getReg .x10 = s.getReg .x2 - 376 := by rw [b80005860_x10 h₁, h9]
  obtain ⟨z₂, hr₂, ⟨hpc₂, hp₂, hnew, hval⟩ | hd⟩ := hP.call (hr.trans hr₁) (b80005860_pc h₁)
    (colPre hpre c₁ h10₁ (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb]))
  swap
  · exact ⟨z₂, hr₂, Or.inr hd⟩
  rw [h10₁] at hnew hval
  obtain ⟨c₂, hn₂, b₂, K₂⟩ := afterNew hpre c₁ (M := heapNext z₁) (Or.inl (by addr_omega [hsb]))
    (Nat.le_refl _) (Or.inl (by addr_omega [hsb, hab])) (by simp only [colStack, powStack]; decide)
    hp₂ hnew
  rw [hval, b80005860_x11 h₁, b80005860_x12 h₁, b80005860_x13 h₁] at b₂
  have bs₂ := K₂.1 _ _ _ _ (K₁.1 _ _ _ _ bs (by omega) (Or.inl (by addr_omega [hsb]))
    (Or.inr (Or.inl rfl))) (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  obtain ⟨z₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80005884_spec
    (by rw [hpc₂, returnAddress_eq, b80005860_x1 h₁]; decide)
    (by rv_eval [c₂.x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₃ := b80005884_keeps h₃
  have hm₃ := b80005884_frame h₃ (by addr_omega [hsb, c₂.x2])
  rw [c₂.x2] at hm₃
  obtain ⟨c₃, hn₃⟩ := c₂.block hpre hm₃ (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ k₃ r (mem_of_mem hr _)
  have K₃ := blockKeeps hpre c₂ hm₃ (by addr_omega [hsb]) (by addr_omega [hsb])
  have bs₃ := moveHeld (e := s.getReg .x2 - 400) bs₂ hm₃.dframe c₂.heap hn₃.ge
    (fun x hx _ ↦ by addr_omega [hx, hsb, hab, c.heap.hi])
    (by
      have e1 := b80005884_m_x2_80 h₃
      have e2 := b80005860_x20 h₁
      rw [c₂.x2] at e1; rw [x2] at e2
      rv_eval [] at e1 e2 ⊢
      rw [e1, hp₂.reg .x20, e2, sum_kept hpre c₁ (by simp only [colStack, powStack]; decide)
        hnew.heap.hi hnew.frame (by addr_omega [hsb]), hm₁])
    (by
      have e1 := b80005884_m_x2_88 h₃
      have e2 := b80005860_x21 h₁
      rw [c₂.x2] at e1; rw [x2] at e2
      rv_eval [] at e1 e2 ⊢
      rw [e1, hp₂.reg .x21, e2, sum_kept hpre c₁ (by simp only [colStack, powStack]; decide)
        hnew.heap.hi hnew.frame (by addr_omega [hsb]), hm₁])
    (by
      have e1 := b80005884_m_x2_96 h₃
      have e2 := b80005860_x22 h₁
      rw [c₂.x2] at e1; rw [x2] at e2
      rv_eval [] at e1 e2 ⊢
      rw [e1, hp₂.reg .x22, e2, sum_kept hpre c₁ (by simp only [colStack, powStack]; decide)
        hnew.heap.hi hnew.frame (by addr_omega [hsb]), hm₁])
  have bo := heldMono (K₃.1 _ _ _ _ b₂ (Nat.le_refl _) (Or.inl (by addr_omega [hsb]))
    (by addr_omega [hsb])) (l' := heapNext z) (h' := heapNext z₃) (by omega) (by omega)
  obtain ⟨w, hr₄, ⟨hpc₄, hp₄, c₄, hn₄, b₄, K₄⟩ | hd⟩ := addCall hA hpre c₃ (hr₂.trans hr₃)
    (b80005884_pc h₃) (o := s.getReg .x2 - 400) (e := s.getReg .x2 - 376)
    (by rw [b80005884_x10 h₃, c₂.x2]; rv_eval [])
    (by rw [b80005884_x11 h₃, c₂.x2, vecPtr, hm₃ (s.getReg .x2 - 376 + 8) (by addr_omega [hsb])];
        rv_eval [])
    (by rw [b80005884_x12 h₃, c₂.x2, vecLen, hm₃ (s.getReg .x2 - 376 + 16) (by addr_omega [hsb])];
        rv_eval [])
    (by rw [b80005884_x13 h₃, hp₂.reg .x18, k₁ .x18 (by decide), h18]) (by addr_omega [hsb])
    (by addr_omega [hsb]) bs₃ bo hL (by omega) (by omega) (prodRust_terms _ _ _)
  swap
  · exact ⟨w, hr₄, Or.inr hd⟩
  have hhz := c.heap.hi
  refine ⟨w, hr₄, Or.inl ⟨by rw [hpc₄, returnAddress_eq, b80005884_x1 h₃]; decide, c₄, by omega,
    by rw [hp₄.reg .x9, k₃ .x9 (by decide), hp₂.reg .x9, k₁ .x9 (by decide)],
    by rw [hp₄.reg .x18, k₃ .x18 (by decide), hp₂.reg .x18, k₁ .x18 (by decide)],
    by rw [hp₄.reg .x19, k₃ .x19 (by decide), hp₂.reg .x19, k₁ .x19 (by decide)],
    b₄, fun e g l h b hh hs hap ↦ ?_, fun fl hi b hh ↦ ?_⟩⟩
  · have hs' : Loc s e ∨ (heapStart ≤ e.toNat ∧ e.toNat + 24 ≤ L) := hs
    have hap' : Apart e 24 (s.getReg .x2 - 400) 24 := by
      rcases hs' with h' | h' <;> addr_omega [hap, hsb, h', hhz, hLz]
    have hap'' : Apart e 24 (s.getReg .x2 - 376) 24 := by
      rcases hs' with h' | h' <;> addr_omega [hap, hsb, h', hhz, hLz]
    exact K₄.1 _ _ _ _ (K₃.1 _ _ _ _ (K₂.1 _ _ _ _ (K₁.1 _ _ _ _ b (by omega)
      (slot_mono hs (by omega)) (Or.inr (Or.inl rfl))) (by omega) (slot_mono hs (by omega)) hap'')
      (by omega) (slot_mono hs (by omega))
      (by rcases hs' with h' | h' <;> addr_omega [hap, hsb, h', hhz, hLz])) hh hs hap'
  · exact K₄.2 _ _ (K₃.2 _ _ (K₂.2 _ _ (K₁.2 _ _ b (by omega)) (by omega)) (by omega)) hh

theorem mulSite_800058fc (hP : ProdSpec) (hA : AddScaledSpec) {s u0 z : MachineState} {L : Nat}
    {f : FormRust} (hpre : FlushesArithPre s) (c : Inv s z) (hr : Reaches Image.code u0 z)
    (hpc : z.pc = 0x800058fc) (h9 : z.getReg .x9 = s.getReg .x2 - 376)
    (h18 : z.getReg .x18 = 0xa00000b0) (bs : Held z (s.getReg .x2 - 400) f L (heapNext z))
    (hL : heapNext s ≤ L) (hLz : L ≤ heapNext z) :
    ∃ w, Reaches Image.code u0 w ∧ ((w.pc = 0x80005944 ∧ Inv s w ∧ heapNext z ≤ heapNext w ∧
      w.getReg .x9 = z.getReg .x9 ∧ w.getReg .x18 = z.getReg .x18 ∧
      Held w (s.getReg .x2 - 400) (f.add (prodRust 6 9 0)) L (heapNext w) ∧
      Keeps s z w (s.getReg .x2 - 400) 48 L) ∨ Dead Image.code w) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  obtain ⟨z₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800058fc_spec hpc
    (by rv_eval [x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₁ := b800058fc_keeps h₁
  have hm₁ := b800058fc_mem_same h₁
  have c₁ := c.same hpre hm₁ fun r hr ↦ k₁ r (mem_of_mem hr _)
  have K₁ := sameKeeps hpre c hm₁
  have hn₁ : heapNext z₁ = heapNext z := by simp only [heapNext, hm₁]
  have h10₁ : z₁.getReg .x10 = s.getReg .x2 - 376 := by rw [b800058fc_x10 h₁, h9]
  obtain ⟨z₂, hr₂, ⟨hpc₂, hp₂, hnew, hval⟩ | hd⟩ := hP.call (hr.trans hr₁) (b800058fc_pc h₁)
    (colPre hpre c₁ h10₁ (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb]))
  swap
  · exact ⟨z₂, hr₂, Or.inr hd⟩
  rw [h10₁] at hnew hval
  obtain ⟨c₂, hn₂, b₂, K₂⟩ := afterNew hpre c₁ (M := heapNext z₁) (Or.inl (by addr_omega [hsb]))
    (Nat.le_refl _) (Or.inl (by addr_omega [hsb, hab])) (by simp only [colStack, powStack]; decide)
    hp₂ hnew
  rw [hval, b800058fc_x11 h₁, b800058fc_x12 h₁, b800058fc_x13 h₁] at b₂
  have bs₂ := K₂.1 _ _ _ _ (K₁.1 _ _ _ _ bs (by omega) (Or.inl (by addr_omega [hsb]))
    (Or.inr (Or.inl rfl))) (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  obtain ⟨z₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80005920_spec
    (by rw [hpc₂, returnAddress_eq, b800058fc_x1 h₁]; decide)
    (by rv_eval [c₂.x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₃ := b80005920_keeps h₃
  have hm₃ := b80005920_frame h₃ (by addr_omega [hsb, c₂.x2])
  rw [c₂.x2] at hm₃
  obtain ⟨c₃, hn₃⟩ := c₂.block hpre hm₃ (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ k₃ r (mem_of_mem hr _)
  have K₃ := blockKeeps hpre c₂ hm₃ (by addr_omega [hsb]) (by addr_omega [hsb])
  have bs₃ := moveHeld (e := s.getReg .x2 - 400) bs₂ hm₃.dframe c₂.heap hn₃.ge
    (fun x hx _ ↦ by addr_omega [hx, hsb, hab, c.heap.hi])
    (by
      have e1 := b80005920_m_x2_80 h₃
      have e2 := b800058fc_x19 h₁
      rw [c₂.x2] at e1; rw [x2] at e2
      rv_eval [] at e1 e2 ⊢
      rw [e1, hp₂.reg .x19, e2, sum_kept hpre c₁ (by simp only [colStack, powStack]; decide)
        hnew.heap.hi hnew.frame (by addr_omega [hsb]), hm₁])
    (by
      have e1 := b80005920_m_x2_88 h₃
      have e2 := b800058fc_x20 h₁
      rw [c₂.x2] at e1; rw [x2] at e2
      rv_eval [] at e1 e2 ⊢
      rw [e1, hp₂.reg .x20, e2, sum_kept hpre c₁ (by simp only [colStack, powStack]; decide)
        hnew.heap.hi hnew.frame (by addr_omega [hsb]), hm₁])
    (by
      have e1 := b80005920_m_x2_96 h₃
      have e2 := b800058fc_x21 h₁
      rw [c₂.x2] at e1; rw [x2] at e2
      rv_eval [] at e1 e2 ⊢
      rw [e1, hp₂.reg .x21, e2, sum_kept hpre c₁ (by simp only [colStack, powStack]; decide)
        hnew.heap.hi hnew.frame (by addr_omega [hsb]), hm₁])
  have bo := heldMono (K₃.1 _ _ _ _ b₂ (Nat.le_refl _) (Or.inl (by addr_omega [hsb]))
    (by addr_omega [hsb])) (l' := heapNext z) (h' := heapNext z₃) (by omega) (by omega)
  obtain ⟨w, hr₄, ⟨hpc₄, hp₄, c₄, hn₄, b₄, K₄⟩ | hd⟩ := addCall hA hpre c₃ (hr₂.trans hr₃)
    (b80005920_pc h₃) (o := s.getReg .x2 - 400) (e := s.getReg .x2 - 376)
    (by rw [b80005920_x10 h₃, c₂.x2]; rv_eval [])
    (by rw [b80005920_x11 h₃, c₂.x2, vecPtr, hm₃ (s.getReg .x2 - 376 + 8) (by addr_omega [hsb])];
        rv_eval [])
    (by rw [b80005920_x12 h₃, c₂.x2, vecLen, hm₃ (s.getReg .x2 - 376 + 16) (by addr_omega [hsb])];
        rv_eval [])
    (by rw [b80005920_x13 h₃, hp₂.reg .x18, k₁ .x18 (by decide), h18]) (by addr_omega [hsb])
    (by addr_omega [hsb]) bs₃ bo hL (by omega) (by omega) (prodRust_terms _ _ _)
  swap
  · exact ⟨w, hr₄, Or.inr hd⟩
  have hhz := c.heap.hi
  refine ⟨w, hr₄, Or.inl ⟨by rw [hpc₄, returnAddress_eq, b80005920_x1 h₃]; decide, c₄, by omega,
    by rw [hp₄.reg .x9, k₃ .x9 (by decide), hp₂.reg .x9, k₁ .x9 (by decide)],
    by rw [hp₄.reg .x18, k₃ .x18 (by decide), hp₂.reg .x18, k₁ .x18 (by decide)],
    b₄, fun e g l h b hh hs hap ↦ ?_, fun fl hi b hh ↦ ?_⟩⟩
  · have hs' : Loc s e ∨ (heapStart ≤ e.toNat ∧ e.toNat + 24 ≤ L) := hs
    have hap' : Apart e 24 (s.getReg .x2 - 400) 24 := by
      rcases hs' with h' | h' <;> addr_omega [hap, hsb, h', hhz, hLz]
    have hap'' : Apart e 24 (s.getReg .x2 - 376) 24 := by
      rcases hs' with h' | h' <;> addr_omega [hap, hsb, h', hhz, hLz]
    exact K₄.1 _ _ _ _ (K₃.1 _ _ _ _ (K₂.1 _ _ _ _ (K₁.1 _ _ _ _ b (by omega)
      (slot_mono hs (by omega)) (Or.inr (Or.inl rfl))) (by omega) (slot_mono hs (by omega)) hap'')
      (by omega) (slot_mono hs (by omega))
      (by rcases hs' with h' | h' <;> addr_omega [hap, hsb, h', hhz, hLz])) hh hs hap'
  · exact K₄.2 _ _ (K₃.2 _ _ (K₂.2 _ _ (K₁.2 _ _ b (by omega)) (by omega)) (by omega)) hh

theorem mulSite_80005944 (hP : ProdSpec) (hA : AddScaledSpec) {s u0 z : MachineState} {L : Nat}
    {f : FormRust} (hpre : FlushesArithPre s) (c : Inv s z) (hr : Reaches Image.code u0 z)
    (hpc : z.pc = 0x80005944) (h9 : z.getReg .x9 = s.getReg .x2 - 376)
    (h18 : z.getReg .x18 = 0xa00000b0) (bs : Held z (s.getReg .x2 - 400) f L (heapNext z))
    (hL : heapNext s ≤ L) (hLz : L ≤ heapNext z) :
    ∃ w, Reaches Image.code u0 w ∧ ((w.pc = 0x8000598c ∧ Inv s w ∧ heapNext z ≤ heapNext w ∧
      w.getReg .x9 = z.getReg .x9 ∧ w.getReg .x18 = z.getReg .x18 ∧
      Held w (s.getReg .x2 - 400) (f.add (prodRust 7 8 0)) L (heapNext w) ∧
      Keeps s z w (s.getReg .x2 - 400) 48 L) ∨ Dead Image.code w) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  obtain ⟨z₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80005944_spec hpc
    (by rv_eval [x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₁ := b80005944_keeps h₁
  have hm₁ := b80005944_mem_same h₁
  have c₁ := c.same hpre hm₁ fun r hr ↦ k₁ r (mem_of_mem hr _)
  have K₁ := sameKeeps hpre c hm₁
  have hn₁ : heapNext z₁ = heapNext z := by simp only [heapNext, hm₁]
  have h10₁ : z₁.getReg .x10 = s.getReg .x2 - 376 := by rw [b80005944_x10 h₁, h9]
  obtain ⟨z₂, hr₂, ⟨hpc₂, hp₂, hnew, hval⟩ | hd⟩ := hP.call (hr.trans hr₁) (b80005944_pc h₁)
    (colPre hpre c₁ h10₁ (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb]))
  swap
  · exact ⟨z₂, hr₂, Or.inr hd⟩
  rw [h10₁] at hnew hval
  obtain ⟨c₂, hn₂, b₂, K₂⟩ := afterNew hpre c₁ (M := heapNext z₁) (Or.inl (by addr_omega [hsb]))
    (Nat.le_refl _) (Or.inl (by addr_omega [hsb, hab])) (by simp only [colStack, powStack]; decide)
    hp₂ hnew
  rw [hval, b80005944_x11 h₁, b80005944_x12 h₁, b80005944_x13 h₁] at b₂
  have bs₂ := K₂.1 _ _ _ _ (K₁.1 _ _ _ _ bs (by omega) (Or.inl (by addr_omega [hsb]))
    (Or.inr (Or.inl rfl))) (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  obtain ⟨z₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80005968_spec
    (by rw [hpc₂, returnAddress_eq, b80005944_x1 h₁]; decide)
    (by rv_eval [c₂.x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₃ := b80005968_keeps h₃
  have hm₃ := b80005968_frame h₃ (by addr_omega [hsb, c₂.x2])
  rw [c₂.x2] at hm₃
  obtain ⟨c₃, hn₃⟩ := c₂.block hpre hm₃ (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ k₃ r (mem_of_mem hr _)
  have K₃ := blockKeeps hpre c₂ hm₃ (by addr_omega [hsb]) (by addr_omega [hsb])
  have bs₃ := moveHeld (e := s.getReg .x2 - 400) bs₂ hm₃.dframe c₂.heap hn₃.ge
    (fun x hx _ ↦ by addr_omega [hx, hsb, hab, c.heap.hi])
    (by
      have e1 := b80005968_m_x2_80 h₃
      have e2 := b80005944_x19 h₁
      rw [c₂.x2] at e1; rw [x2] at e2
      rv_eval [] at e1 e2 ⊢
      rw [e1, hp₂.reg .x19, e2, sum_kept hpre c₁ (by simp only [colStack, powStack]; decide)
        hnew.heap.hi hnew.frame (by addr_omega [hsb]), hm₁])
    (by
      have e1 := b80005968_m_x2_88 h₃
      have e2 := b80005944_x20 h₁
      rw [c₂.x2] at e1; rw [x2] at e2
      rv_eval [] at e1 e2 ⊢
      rw [e1, hp₂.reg .x20, e2, sum_kept hpre c₁ (by simp only [colStack, powStack]; decide)
        hnew.heap.hi hnew.frame (by addr_omega [hsb]), hm₁])
    (by
      have e1 := b80005968_m_x2_96 h₃
      have e2 := b80005944_x21 h₁
      rw [c₂.x2] at e1; rw [x2] at e2
      rv_eval [] at e1 e2 ⊢
      rw [e1, hp₂.reg .x21, e2, sum_kept hpre c₁ (by simp only [colStack, powStack]; decide)
        hnew.heap.hi hnew.frame (by addr_omega [hsb]), hm₁])
  have bo := heldMono (K₃.1 _ _ _ _ b₂ (Nat.le_refl _) (Or.inl (by addr_omega [hsb]))
    (by addr_omega [hsb])) (l' := heapNext z) (h' := heapNext z₃) (by omega) (by omega)
  obtain ⟨w, hr₄, ⟨hpc₄, hp₄, c₄, hn₄, b₄, K₄⟩ | hd⟩ := addCall hA hpre c₃ (hr₂.trans hr₃)
    (b80005968_pc h₃) (o := s.getReg .x2 - 400) (e := s.getReg .x2 - 376)
    (by rw [b80005968_x10 h₃, c₂.x2]; rv_eval [])
    (by rw [b80005968_x11 h₃, c₂.x2, vecPtr, hm₃ (s.getReg .x2 - 376 + 8) (by addr_omega [hsb])];
        rv_eval [])
    (by rw [b80005968_x12 h₃, c₂.x2, vecLen, hm₃ (s.getReg .x2 - 376 + 16) (by addr_omega [hsb])];
        rv_eval [])
    (by rw [b80005968_x13 h₃, hp₂.reg .x18, k₁ .x18 (by decide), h18]) (by addr_omega [hsb])
    (by addr_omega [hsb]) bs₃ bo hL (by omega) (by omega) (prodRust_terms _ _ _)
  swap
  · exact ⟨w, hr₄, Or.inr hd⟩
  have hhz := c.heap.hi
  refine ⟨w, hr₄, Or.inl ⟨by rw [hpc₄, returnAddress_eq, b80005968_x1 h₃]; decide, c₄, by omega,
    by rw [hp₄.reg .x9, k₃ .x9 (by decide), hp₂.reg .x9, k₁ .x9 (by decide)],
    by rw [hp₄.reg .x18, k₃ .x18 (by decide), hp₂.reg .x18, k₁ .x18 (by decide)],
    b₄, fun e g l h b hh hs hap ↦ ?_, fun fl hi b hh ↦ ?_⟩⟩
  · have hs' : Loc s e ∨ (heapStart ≤ e.toNat ∧ e.toNat + 24 ≤ L) := hs
    have hap' : Apart e 24 (s.getReg .x2 - 400) 24 := by
      rcases hs' with h' | h' <;> addr_omega [hap, hsb, h', hhz, hLz]
    have hap'' : Apart e 24 (s.getReg .x2 - 376) 24 := by
      rcases hs' with h' | h' <;> addr_omega [hap, hsb, h', hhz, hLz]
    exact K₄.1 _ _ _ _ (K₃.1 _ _ _ _ (K₂.1 _ _ _ _ (K₁.1 _ _ _ _ b (by omega)
      (slot_mono hs (by omega)) (Or.inr (Or.inl rfl))) (by omega) (slot_mono hs (by omega)) hap'')
      (by omega) (slot_mono hs (by omega))
      (by rcases hs' with h' | h' <;> addr_omega [hap, hsb, h', hhz, hLz])) hh hs hap'
  · exact K₄.2 _ _ (K₃.2 _ _ (K₂.2 _ _ (K₁.2 _ _ b (by omega)) (by omega)) (by omega)) hh

theorem mulSite_8000598c (hP : ProdSpec) (hA : AddScaledSpec) {s u0 z : MachineState} {L : Nat}
    {f : FormRust} (hpre : FlushesArithPre s) (c : Inv s z) (hr : Reaches Image.code u0 z)
    (hpc : z.pc = 0x8000598c) (h9 : z.getReg .x9 = s.getReg .x2 - 376)
    (h18 : z.getReg .x18 = 0xa00000b0) (bs : Held z (s.getReg .x2 - 400) f L (heapNext z))
    (hL : heapNext s ≤ L) (hLz : L ≤ heapNext z) :
    ∃ w, Reaches Image.code u0 w ∧ ((w.pc = 0x800059d4 ∧ Inv s w ∧ heapNext z ≤ heapNext w ∧
      w.getReg .x9 = z.getReg .x9 ∧ w.getReg .x18 = z.getReg .x18 ∧
      Held w (s.getReg .x2 - 400) (f.add (prodRust 7 10 0)) L (heapNext w) ∧
      Keeps s z w (s.getReg .x2 - 400) 48 L) ∨ Dead Image.code w) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  obtain ⟨z₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000598c_spec hpc
    (by rv_eval [x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₁ := b8000598c_keeps h₁
  have hm₁ := b8000598c_mem_same h₁
  have c₁ := c.same hpre hm₁ fun r hr ↦ k₁ r (mem_of_mem hr _)
  have K₁ := sameKeeps hpre c hm₁
  have hn₁ : heapNext z₁ = heapNext z := by simp only [heapNext, hm₁]
  have h10₁ : z₁.getReg .x10 = s.getReg .x2 - 376 := by rw [b8000598c_x10 h₁, h9]
  obtain ⟨z₂, hr₂, ⟨hpc₂, hp₂, hnew, hval⟩ | hd⟩ := hP.call (hr.trans hr₁) (b8000598c_pc h₁)
    (colPre hpre c₁ h10₁ (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb]))
  swap
  · exact ⟨z₂, hr₂, Or.inr hd⟩
  rw [h10₁] at hnew hval
  obtain ⟨c₂, hn₂, b₂, K₂⟩ := afterNew hpre c₁ (M := heapNext z₁) (Or.inl (by addr_omega [hsb]))
    (Nat.le_refl _) (Or.inl (by addr_omega [hsb, hab])) (by simp only [colStack, powStack]; decide)
    hp₂ hnew
  rw [hval, b8000598c_x11 h₁, b8000598c_x12 h₁, b8000598c_x13 h₁] at b₂
  have bs₂ := K₂.1 _ _ _ _ (K₁.1 _ _ _ _ bs (by omega) (Or.inl (by addr_omega [hsb]))
    (Or.inr (Or.inl rfl))) (by omega) (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb])
  obtain ⟨z₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800059b0_spec
    (by rw [hpc₂, returnAddress_eq, b8000598c_x1 h₁]; decide)
    (by rv_eval [c₂.x2]; and_intros <;> valid_access (stackValid hpre) [hsb])
  have k₃ := b800059b0_keeps h₃
  have hm₃ := b800059b0_frame h₃ (by addr_omega [hsb, c₂.x2])
  rw [c₂.x2] at hm₃
  obtain ⟨c₃, hn₃⟩ := c₂.block hpre hm₃ (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ k₃ r (mem_of_mem hr _)
  have K₃ := blockKeeps hpre c₂ hm₃ (by addr_omega [hsb]) (by addr_omega [hsb])
  have bs₃ := moveHeld (e := s.getReg .x2 - 400) bs₂ hm₃.dframe c₂.heap hn₃.ge
    (fun x hx _ ↦ by addr_omega [hx, hsb, hab, c.heap.hi])
    (by
      have e1 := b800059b0_m_x2_80 h₃
      have e2 := b8000598c_x19 h₁
      rw [c₂.x2] at e1; rw [x2] at e2
      rv_eval [] at e1 e2 ⊢
      rw [e1, hp₂.reg .x19, e2, sum_kept hpre c₁ (by simp only [colStack, powStack]; decide)
        hnew.heap.hi hnew.frame (by addr_omega [hsb]), hm₁])
    (by
      have e1 := b800059b0_m_x2_88 h₃
      have e2 := b8000598c_x20 h₁
      rw [c₂.x2] at e1; rw [x2] at e2
      rv_eval [] at e1 e2 ⊢
      rw [e1, hp₂.reg .x20, e2, sum_kept hpre c₁ (by simp only [colStack, powStack]; decide)
        hnew.heap.hi hnew.frame (by addr_omega [hsb]), hm₁])
    (by
      have e1 := b800059b0_m_x2_96 h₃
      have e2 := b8000598c_x21 h₁
      rw [c₂.x2] at e1; rw [x2] at e2
      rv_eval [] at e1 e2 ⊢
      rw [e1, hp₂.reg .x21, e2, sum_kept hpre c₁ (by simp only [colStack, powStack]; decide)
        hnew.heap.hi hnew.frame (by addr_omega [hsb]), hm₁])
  have bo := heldMono (K₃.1 _ _ _ _ b₂ (Nat.le_refl _) (Or.inl (by addr_omega [hsb]))
    (by addr_omega [hsb])) (l' := heapNext z) (h' := heapNext z₃) (by omega) (by omega)
  obtain ⟨w, hr₄, ⟨hpc₄, hp₄, c₄, hn₄, b₄, K₄⟩ | hd⟩ := addCall hA hpre c₃ (hr₂.trans hr₃)
    (b800059b0_pc h₃) (o := s.getReg .x2 - 400) (e := s.getReg .x2 - 376)
    (by rw [b800059b0_x10 h₃, c₂.x2]; rv_eval [])
    (by rw [b800059b0_x11 h₃, c₂.x2, vecPtr, hm₃ (s.getReg .x2 - 376 + 8) (by addr_omega [hsb])];
        rv_eval [])
    (by rw [b800059b0_x12 h₃, c₂.x2, vecLen, hm₃ (s.getReg .x2 - 376 + 16) (by addr_omega [hsb])];
        rv_eval [])
    (by rw [b800059b0_x13 h₃, hp₂.reg .x18, k₁ .x18 (by decide), h18]) (by addr_omega [hsb])
    (by addr_omega [hsb]) bs₃ bo hL (by omega) (by omega) (prodRust_terms _ _ _)
  swap
  · exact ⟨w, hr₄, Or.inr hd⟩
  have hhz := c.heap.hi
  refine ⟨w, hr₄, Or.inl ⟨by rw [hpc₄, returnAddress_eq, b800059b0_x1 h₃]; decide, c₄, by omega,
    by rw [hp₄.reg .x9, k₃ .x9 (by decide), hp₂.reg .x9, k₁ .x9 (by decide)],
    by rw [hp₄.reg .x18, k₃ .x18 (by decide), hp₂.reg .x18, k₁ .x18 (by decide)],
    b₄, fun e g l h b hh hs hap ↦ ?_, fun fl hi b hh ↦ ?_⟩⟩
  · have hs' : Loc s e ∨ (heapStart ≤ e.toNat ∧ e.toNat + 24 ≤ L) := hs
    have hap' : Apart e 24 (s.getReg .x2 - 400) 24 := by
      rcases hs' with h' | h' <;> addr_omega [hap, hsb, h', hhz, hLz]
    have hap'' : Apart e 24 (s.getReg .x2 - 376) 24 := by
      rcases hs' with h' | h' <;> addr_omega [hap, hsb, h', hhz, hLz]
    exact K₄.1 _ _ _ _ (K₃.1 _ _ _ _ (K₂.1 _ _ _ _ (K₁.1 _ _ _ _ b (by omega)
      (slot_mono hs (by omega)) (Or.inr (Or.inl rfl))) (by omega) (slot_mono hs (by omega)) hap'')
      (by omega) (slot_mono hs (by omega))
      (by rcases hs' with h' | h' <;> addr_omega [hap, hsb, h', hhz, hLz])) hh hs hap'
  · exact K₄.2 _ _ (K₃.2 _ _ (K₂.2 _ _ (K₁.2 _ _ b (by omega)) (by omega)) (by omega)) hh

end Rv64Verifier.Layout.Arith
