import Rv64Verifier.Proofs.Layout.LimbSum

/-!
# `flushes_keccak`'s `limb` closure: the sum's stages

`stageA` adds `col(a)` (`0x80004f34`, the sum empty) or skips it (`0x80005038`); `stageB` adds
`prod(flag, a)` (`0x80004f88`); `stageC` adds `prod(flag, b)` (`0x80004fdc`); `stageD` writes the sum
to `a0` (`0x80005028`) and returns.
-/

namespace Rv64Verifier.Layout.Limb
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F13 Rv64Verifier.Model.LayoutMirror

/-- The sum of `f` and an optional summand. -/
def addOpt (f : FormRust) : Option FormRust → FormRust
  | none => f
  | some g => f.add g

theorem sum_addOpt (l : List FormRust) (o : Option FormRust) :
    FormRust.sum (l ++ o.toList) = addOpt (FormRust.sum l) o := by
  cases o with
  | none => simp [addOpt]
  | some g => exact sum_snoc l g

/-- `col(a)`, or nothing. -/
theorem stageA (hA : AddScaledSpec) {s w : MachineState} (hpre : LimbPre s) (c : Inv s w)
    (hpc : w.pc = 0x80004f28) (hH : heapNext s ≤ heapNext w) {oc : Option FormRust}
    (sc : Slot s w (heapNext w) .x21 (s.getReg .x2 - 136) oc) :
    ∃ z, Reaches Image.code w z ∧ ((Mid s w z (addOpt {} oc) ∧
      z.pc = if w.getReg .x20 = 0xffffffffffffffff then 0x80004fd4 else 0x80004f88) ∨
      Dead Image.code z) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  obtain ⟨w₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80004f28_spec hpc trivial
  have k₁ := b80004f28_keeps h₁
  have c₁ := c.same hpre (b80004f28_mem_same h₁) fun r hr ↦ k₁ r (mem_of_mem hr _)
  have y18 : w₁.getReg .x18 = s.getReg .x2 - 80 := by rw [b80004f28_x18 h₁, x2]; addr_omega [hsb]
  have y19 := b80004f28_x19 h₁
  have hn₁ : heapNext w₁ = heapNext w := by simp only [heapNext, b80004f28_mem_same h₁]
  cases oc with
  | none =>
    have h21 : w.getReg .x21 = 0xffffffffffffffff := sc
    obtain ⟨w₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80005038_spec (b80004f28_pc_taken h₁ h21) trivial
    have k₂ := b80005038_keeps h₂
    have M : Mid s w w₂ (addOpt {} none) := {
      toInv := c₁.same hpre (b80005038_mem_same h₂) fun r hr ↦ k₂ r (mem_of_mem hr _)
      x18 := (k₂ .x18 (by decide)).trans y18
      x19 := (k₂ .x19 (by decide)).trans y19
      x9 := (k₂ .x9 (by decide)).trans (k₁ .x9 (by decide))
      x20 := (k₂ .x20 (by decide)).trans (k₁ .x20 (by decide))
      acc := Or.inr ⟨rfl, b80005038_x13 h₂, b80005038_x14 h₂, b80005038_x10 h₂⟩
      hz := by simp only [heapNext, b80005038_mem_same h₂, b80004f28_mem_same h₁]; exact le_refl _
      keep := fun e g l b he₁ he₂ ↦ (b.same c.heap (b80004f28_mem_same h₁) (by addr_omega [hsb, he₂])).same
        c₁.heap (b80005038_mem_same h₂) (by addr_omega [hsb, he₂]) }
    have x20₁ : w₁.getReg .x20 = w.getReg .x20 := k₁ .x20 (by decide)
    by_cases h20 : w.getReg .x20 = 0xffffffffffffffff
    · obtain ⟨w₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80005048_spec
        (b80005038_pc_not_taken h₂ (by rw [x20₁, y19, h20])) trivial
      have k₃ := b80005048_keeps h₃
      exact ⟨w₃, hr₁.trans (hr₂.trans hr₃), Or.inl ⟨M.same hpre (b80005048_mem_same h₃)
        fun r hr ↦ k₃ r (mem_of_mem hr _), by rw [b80005048_pc h₃]; simp only [h20, ↓reduceIte]⟩⟩
    · exact ⟨w₂, hr₁.trans hr₂, Or.inl ⟨M, by
        rw [b80005038_pc_taken h₂ (by rw [x20₁, y19]; exact h20)]; simp only [h20, ↓reduceIte]⟩⟩
  | some g =>
    obtain ⟨hg, bg, hne⟩ := sc
    -- the summand's buffer and length to `sp' + 128`
    obtain ⟨z₁, hr₂, h₂⟩ := Sym.BlockSpec.reaches copy0_spec (b80004f28_pc_not_taken h₁ hne) (by
      rv_eval [c₁.x2, y18]; and_intros <;> valid_access hpre.stack.valid [hsb])
    have k₂ := h₂.keeps (rs := [.x1, .x2, .x8, .x9, .x14, .x18, .x19, .x20, .x21, .x22, .x23, .x24,
      .x25, .x26, .x27]) rfl
    have hm₂ : MemFrame w₁ z₁ (s.getReg .x2 - 80) 16 := h₂.memFrame (by
      simp only [copy0E, List.mem_cons, List.not_mem_nil, or_false]
      rintro k (rfl | rfl) <;> rv_eval [y18] <;> addr_omega [hsb])
    have m₂0 := h₂.mem_eq 1 (by decide) (a := s.getReg .x2 - 80)
      (v := w₁.getMem (s.getReg .x2 - 128)) (by rv_eval [y18]) (by rv_eval [c₁.x2])
    have m₂8 := h₂.mem_eq 0 (by decide) (a := s.getReg .x2 - 72)
      (v := w₁.getMem (s.getReg .x2 - 120)) (by rv_eval [y18]) (by rv_eval [c₁.x2])
    have c₂ := c₁.block hpre hm₂ (by addr_omega [hsb]) (by addr_omega [hsb])
      fun r hr ↦ k₂ r (mem_of_mem hr _)
    have hn₂ : heapNext z₁ = heapNext w₁ := by
      simp only [heapNext]; rw [hm₂ _ (by addr_omega [hnx, hsb])]
    have bg₁ := (bg.same c.heap (b80004f28_mem_same h₁) (by addr_omega [hsb])).block hpre c₁ hm₂
      (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb])
    -- the empty sum at `sp' + 96`, and the call
    obtain ⟨u, hr₃, h₃⟩ := Sym.BlockSpec.reaches store0_spec (h₂.pc_eq rfl) (by
      rv_eval [c₂.x2]; and_intros <;> valid_access hpre.stack.valid [hsb])
    have k₃ := h₃.keeps (rs := [.x2, .x8, .x9, .x14, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25,
      .x26, .x27]) rfl
    have hm₃ : MemFrame z₁ u (s.getReg .x2 - 112) 32 := h₃.memFrame (by
      simp only [store0E, List.mem_cons, List.not_mem_nil, or_false]
      rintro k (rfl | rfl | rfl | rfl) <;> rv_eval [c₂.x2] <;> addr_omega [hsb])
    have c₃ := c₂.block hpre hm₃ (by addr_omega [hsb]) (by addr_omega [hsb])
      fun r hr ↦ k₃ r (mem_of_mem hr _)
    have hn₃ : heapNext u = heapNext z₁ := by
      simp only [heapNext]; rw [hm₃ _ (by addr_omega [hnx, hsb])]
    have bg₂ := bg₁.block hpre c₂ hm₃ (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb])
      (by addr_omega [hsb])
    have ba : Held u (s.getReg .x2 - 112) {} (heapNext w) (heapNext u) := held_empty
      (h₃.mem_eq 3 (by decide) (by rv_eval [c₂.x2]) (by rv_eval []))
      (by
        rw [show s.getReg .x2 - 112 + 8 = s.getReg .x2 - 104 by addr_omega [hsb]]
        exact h₃.mem_eq 2 (by decide) (by rv_eval [c₂.x2])
          (by rv_eval []; exact h₂.reg_eq .x13 rfl (by rv_eval [])))
      (by
        rw [show s.getReg .x2 - 112 + 16 = s.getReg .x2 - 96 by addr_omega [hsb]]
        exact h₃.mem_eq 1 (by decide) (by rv_eval [c₂.x2]) (by rv_eval []))
    have y11 : u.getReg .x11 = vecPtr u (s.getReg .x2 - 136) := by
      rw [h₃.reg_eq (v := z₁.getMem (z₁.getReg .x2 + 128)) .x11 rfl (by rv_eval []), c₂.x2,
        show s.getReg .x2 - 208 + 128 = s.getReg .x2 - 80 by addr_omega [hsb], m₂0, vecPtr,
        hm₃ _ (by addr_omega [hsb]), hm₂ _ (by addr_omega [hsb])]
      congr 1; addr_omega [hsb]
    have y12 : u.getReg .x12 = vecLen u (s.getReg .x2 - 136) := by
      rw [h₃.reg_eq (v := z₁.getMem (z₁.getReg .x2 + 136)) .x12 rfl (by rv_eval []), c₂.x2,
        show s.getReg .x2 - 208 + 136 = s.getReg .x2 - 72 by addr_omega [hsb], m₂8, vecLen,
        hm₃ _ (by addr_omega [hsb]), hm₂ _ (by addr_omega [hsb])]
      congr 1; addr_omega [hsb]
    have y10 : u.getReg .x10 = s.getReg .x2 - 112 := by
      rw [h₃.reg_eq (v := z₁.getReg .x2 + 96) .x10 rfl (by rv_eval []), c₂.x2]; addr_omega [hsb]
    have hHu : heapNext w ≤ heapNext u := by rw [hn₃, hn₂, hn₁]
    obtain ⟨v, hr₄, ⟨hpc₄, hp₄, c₄, hv₄, b₄, kp₄⟩ | hd⟩ := addCall hA hpre c₃ (hr₂.trans hr₃)
      (h₃.pc_eq rfl) y10 y11 y12 (h₃.reg_eq .x13 rfl (by rv_eval [])) ba bg₂ hH hHu hg
    swap
    · exact ⟨v, hr₁.trans hr₄, Or.inr hd⟩
    have hpv : v.pc = 0x80004f78 := by
      rw [hpc₄, returnAddress, h₃.reg_eq (v := 0x80004f78) .x1 rfl (by rv_eval [])]; rfl
    have hreg (r : Reg) (hr : r ∈ [Reg.x9, .x18, .x19, .x20, .x21, .x22]) :
        v.getReg r = w₁.getReg r := by
      rw [hp₄ r (mem_of_mem hr _), k₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _)]
    obtain ⟨z, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80004f78_spec hpv (by
      rv_eval [c₄.x2]; and_intros <;> valid_access hpre.stack.valid [hsb])
    have k₅ := b80004f78_keeps h₅
    have M : Mid s w z (addOpt {} (some g)) := Mid.reload hpre c₄
      ((hreg .x18 (by decide)).trans y18) ((hreg .x19 (by decide)).trans y19)
      ((hreg .x9 (by decide)).trans (k₁ .x9 (by decide)))
      ((hreg .x20 (by decide)).trans (k₁ .x20 (by decide))) b₄
      (fun e g' l b he₁ he₂ ↦ kp₄ e g' l (((b.same c.heap (b80004f28_mem_same h₁)
        (by addr_omega [hsb, he₂])).block hpre c₁ hm₂ (by addr_omega [hsb]) (by addr_omega [hsb])
        (by addr_omega [hsb, he₂]) (by addr_omega [hsb, he₂])).block hpre c₂ hm₃
        (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb, he₂])
        (by addr_omega [hsb, he₂])) he₁ (by omega) (by addr_omega [hsb, he₂]))
      (le_trans hHu hv₄) (b80004f78_mem_same h₅) (fun r hr ↦ k₅ r (mem_of_mem hr _))
      (b80004f78_x10 h₅) (b80004f78_x13 h₅) (b80004f78_x14 h₅)
    have x20 : v.getReg .x20 = w.getReg .x20 := (hreg .x20 (by decide)).trans (k₁ .x20 (by decide))
    have x19 : v.getReg .x19 = 0xffffffffffffffff := (hreg .x19 (by decide)).trans y19
    refine ⟨z, hr₁.trans (hr₄.trans hr₅), Or.inl ⟨M, ?_⟩⟩
    by_cases h20 : w.getReg .x20 = 0xffffffffffffffff
    · rw [b80004f78_pc_taken h₅ (by rw [x20, x19, h20])]; simp only [h20, ↓reduceIte]
    · rw [b80004f78_pc_not_taken h₅ (by rw [x20, x19]; exact h20)]; simp only [h20, ↓reduceIte]

/-- `prod(flag, a)`, or nothing. -/
theorem stageB (hA : AddScaledSpec) {s w z : MachineState} {f : FormRust} (hpre : LimbPre s)
    (hH : heapNext s ≤ heapNext w) (m : Mid s w z f)
    (hpc : z.pc = if w.getReg .x20 = 0xffffffffffffffff then 0x80004fd4 else 0x80004f88)
    {op : Option FormRust} (sp : Slot s w (heapNext w) .x20 (s.getReg .x2 - 160) op) :
    ∃ z', Reaches Image.code z z' ∧ ((Mid s w z' (addOpt f op) ∧ z'.pc = 0x80004fd4) ∨
      Dead Image.code z') := by
  obtain ⟨hsb, -⟩ := facts hpre
  cases op with
  | none =>
    have h20 : w.getReg .x20 = 0xffffffffffffffff := sp
    exact ⟨z, Reaches.refl _, Or.inl ⟨m, by rw [hpc]; simp only [h20, ↓reduceIte]⟩⟩
  | some g =>
    obtain ⟨hg, bg, hne⟩ := sp
    have hpc' : z.pc = 0x80004f88 := by rw [hpc]; simp only [hne, ↓reduceIte]
    have bg' : Held z (s.getReg .x2 - 208 + (56 - 8)) g (heapNext s) (heapNext w) := by
      rw [show s.getReg .x2 - 208 + (56 - 8) = s.getReg .x2 - 160 by addr_omega [hsb]]
      exact m.keep _ _ _ bg (by addr_omega [hsb]) (by addr_omega [hsb])
    obtain ⟨v, hr, ⟨hpcv, cv, hzv, hreg, bv, kv⟩ | hd⟩ := site hA hpre m.toInv hH m.hz copy1_spec
      store1_spec hpc' m.x18 (Or.inr rfl) m.acc hg bg'
    swap
    · exact ⟨v, hr, Or.inr hd⟩
    obtain ⟨z', hr', h'⟩ := Sym.BlockSpec.reaches b80004fc8_spec (by rw [hpcv]; rfl) (by
      rv_eval [cv.x2]; and_intros <;> valid_access hpre.stack.valid [hsb])
    have k' := b80004fc8_keeps h'
    exact ⟨z', hr.trans hr', Or.inl ⟨Mid.reload hpre cv ((hreg .x18 (by decide)).trans m.x18)
      ((hreg .x19 (by decide)).trans m.x19) ((hreg .x9 (by decide)).trans m.x9)
      ((hreg .x20 (by decide)).trans m.x20) bv
      (fun e g' l b he₁ he₂ ↦ kv e g' l (m.keep e g' l b he₁ he₂) he₁ he₂) (m.hz.trans hzv)
      (b80004fc8_mem_same h') (fun r hr ↦ k' r (mem_of_mem hr _)) (b80004fc8_x10 h')
      (b80004fc8_x13 h') (b80004fc8_x14 h'), b80004fc8_pc h'⟩⟩

/-- `prod(flag, b)`, or nothing. -/
theorem stageC (hA : AddScaledSpec) {s w z : MachineState} {f : FormRust} (hpre : LimbPre s)
    (hH : heapNext s ≤ heapNext w) (m : Mid s w z f) (hpc : z.pc = 0x80004fd4)
    {ob : Option FormRust} (sb : Slot s w (heapNext w) .x9 (s.getReg .x2 - 184) ob) :
    ∃ z', Reaches Image.code z z' ∧ ((Mid s w z' (addOpt f ob) ∧ z'.pc = 0x80005028) ∨
      Dead Image.code z') := by
  obtain ⟨hsb, -⟩ := facts hpre
  obtain ⟨z₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80004fd4_spec hpc trivial
  have k₁ := b80004fd4_keeps h₁
  have m₁ := m.same hpre (b80004fd4_mem_same h₁) fun r hr ↦ k₁ r (mem_of_mem hr _)
  have x9 : z.getReg .x9 = w.getReg .x9 := m.x9
  cases ob with
  | none =>
    have h9 : w.getReg .x9 = 0xffffffffffffffff := sb
    exact ⟨z₁, hr₁, Or.inl ⟨m₁, b80004fd4_pc_taken h₁ (by rw [x9, h9])⟩⟩
  | some g =>
    obtain ⟨hg, bg, hne⟩ := sb
    have bg' : Held z₁ (s.getReg .x2 - 208 + (32 - 8)) g (heapNext s) (heapNext w) := by
      rw [show s.getReg .x2 - 208 + (32 - 8) = s.getReg .x2 - 184 by addr_omega [hsb]]
      exact m₁.keep _ _ _ bg (by addr_omega [hsb]) (by addr_omega [hsb])
    obtain ⟨v, hr, ⟨hpcv, cv, hzv, hreg, bv, kv⟩ | hd⟩ := site hA hpre m₁.toInv hH m₁.hz copy2_spec
      store2_spec (b80004fd4_pc_not_taken h₁ (by rw [x9]; exact hne)) m₁.x18 (Or.inl rfl) m₁.acc
      hg bg'
    swap
    · exact ⟨v, hr₁.trans hr, Or.inr hd⟩
    obtain ⟨z', hr', h'⟩ := Sym.BlockSpec.reaches b8000501c_spec (by rw [hpcv]; rfl) (by
      rv_eval [cv.x2]; and_intros <;> valid_access hpre.stack.valid [hsb])
    have k' := b8000501c_keeps h'
    exact ⟨z', hr₁.trans (hr.trans hr'), Or.inl ⟨Mid.reload hpre cv ((hreg .x18 (by decide)).trans m₁.x18)
      ((hreg .x19 (by decide)).trans m₁.x19) ((hreg .x9 (by decide)).trans m₁.x9)
      ((hreg .x20 (by decide)).trans m₁.x20) bv
      (fun e g' l b he₁ he₂ ↦ kv e g' l (m₁.keep e g' l b he₁ he₂) he₁ he₂) (m₁.hz.trans hzv)
      (b8000501c_mem_same h') (fun r hr ↦ k' r (mem_of_mem hr _)) (b8000501c_x10 h')
      (b8000501c_x13 h') (b8000501c_x14 h'), b8000501c_pc h'⟩⟩

/-- The sum to `a0`, and the return. -/
theorem stageD {s w z : MachineState} {f : FormRust} (hpre : LimbPre s)
    (hH : heapNext s ≤ heapNext w) (m : Mid s w z f) (hpc : z.pc = 0x80005028) :
    ∃ t, Reaches Image.code z t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      NewForm s t (s.getReg .x10) limbStack ∧ formOf t (s.getReg .x10) = f := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hob := ValidMemRange.bounds hpre.out (by decide)
  have hof := hpre.outFree
  have x8 : z.getReg .x8 = s.getReg .x10 := m.x8
  obtain ⟨y, hr, h⟩ := Sym.BlockSpec.reaches b80005028_spec hpc (by
    rv_eval [x8]; and_intros <;> valid_access hpre.out [hob])
  have k := b80005028_keeps h
  have hm := b80005028_frame h (by rw [x8]; addr_omega [hob])
  rw [x8] at hm
  have hn : heapNext y = heapNext z := by
    simp only [heapNext]; rw [hm _ (by addr_omega [hof])]
  have m0 := b80005028_m_x8_0 h
  have m8 := b80005028_m_x8_8 h
  have m16 := b80005028_m_x8_16 h
  rw [x8] at m0 m8 m16
  have hzh := m.hz
  have hb : Held y (s.getReg .x10) f (heapNext s) (heapNext y) := by
    rcases m.acc with ⟨b, a13, a14, a10⟩ | ⟨rfl, a13, a14, a10⟩
    · have hhz := m.heap.hi
      have hk := formOf_move hm.dframe b.ok (m0.trans a13)
        (by rw [m8, a14]; congr 1; addr_omega [hsb])
        (by rw [m16, a10]; congr 1; addr_omega [hsb])
        (fun x hx hw ↦ by
          have := b.buf x hx
          simp only [Outside, heapEnd] at hof hhz
          addr_omega [hw, this, hof, hhz, hH]) m.heap hn.ge
      refine ⟨hk.2.1, hk.1.trans b.val, fun x hx ↦ ?_⟩
      rw [hk.2.2] at hx
      have := b.buf x hx
      omega
    · exact held_empty (m0.trans a13) (m8.trans a14) (m16.trans a10)
  obtain ⟨t, ht, rest⟩ := finish hpre m.toInv hm.dframe (fun a ha ↦ Or.inl ha)
    ⟨hn ▸ m.heap.lo, hn ▸ m.heap.hi⟩ hn.ge (fun r hr ↦ k r (mem_of_mem hr _)) (b80005028_pc h) hb
  exact ⟨t, hr.trans ht, rest⟩

end Rv64Verifier.Layout.Limb
