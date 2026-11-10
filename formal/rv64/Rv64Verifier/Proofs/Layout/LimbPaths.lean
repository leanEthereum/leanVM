import Rv64Verifier.Proofs.Layout.LimbStages

/-!
# `flushes_keccak`'s `limb` closure: the forms built

`none`: `a`, `b` both `None`, `constant(ZERO)` (`0x8000504c`, `0x80005068`). `equal`: `a == b`,
`col(a, 0)` into `a0` after the eager `constant(ZERO)` (`0x80004e88`, `0x80004ea4`). `summands`:
`col(a)` at `sp' + 72` and `prod(flag, a)` at `sp' + 48` when `a` is `Some` (`0x80004ecc`,
`0x80004ee0`), `prod(flag, b)` at `sp' + 24` when `b` is `Some` (`0x80004f04`), then the sum.
-/

namespace Rv64Verifier.Layout.Limb
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F13 Rv64Verifier.Model.LayoutMirror

/-- The final post, from a state `z` of the run. -/
def Done (s z : MachineState) (f : FormRust) : Prop :=
  ∃ t, Reaches Image.code z t ∧ ((t.pc = returnAddress s ∧ Preserves s t ∧
    NewForm s t (s.getReg .x10) limbStack ∧ formOf t (s.getReg .x10) = f) ∨ Dead Image.code t)

theorem Done.back {s z z' : MachineState} {f : FormRust} (h : Reaches Image.code z z')
    (d : Done s z' f) : Done s z f :=
  let ⟨t, ht, r⟩ := d; ⟨t, h.trans ht, r⟩

/-- A call that builds a new form in the locals (`col` or `prod`), the form `F` of its arguments. -/
theorem newAt {E : Word} {F : MachineState → FormRust}
    (hS : FunSpec Image.code E ColPre fun s t ↦
      NewForm s t (s.getReg .x10) colStack ∧ formOf t (s.getReg .x10) = F s)
    {s u0 u : MachineState} (hpre : LimbPre s) (c : Inv s u) (hr : Reaches Image.code u0 u)
    (hpc : u.pc = E) {o : Word} (h10 : u.getReg .x10 = o)
    (ho₁ : (s.getReg .x2).toNat - 208 ≤ o.toNat) (ho₂ : o.toNat + 24 ≤ (s.getReg .x2).toNat - 112)
    (h8 : o.toNat % 8 = 0) :
    ∃ v, Reaches Image.code u0 v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧ Inv s v ∧
      heapNext u ≤ heapNext v ∧ Held v o (F u) (heapNext u) (heapNext v) ∧
      ∀ e f l h, Held u e f l h → h ≤ heapNext u →
        (s.getReg .x2).toNat - 208 ≤ e.toNat → e.toNat + 24 ≤ (s.getReg .x2).toNat - 64 →
        Apart e 24 o 24 → Held v e f l h) ∨ Dead Image.code v) := by
  obtain ⟨v, hrv, ⟨hpcv, hpres, hnew, hval⟩ | hd⟩ :=
    hS.call hr hpc (colPre hpre c h10 ho₁ (by omega) h8)
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  rw [h10] at hnew hval
  obtain ⟨cv, bv, kv⟩ := afterNew hpre c ho₁ (by omega)
    (by simp only [colStack, powStack, Contracts.mulStack]; decide) hpres hnew
  exact ⟨v, hrv, Or.inl ⟨hpcv, hpres, cv, hnew.mono, ⟨bv.ok, bv.val.trans hval, bv.buf⟩, kv⟩⟩

theorem terms_ne (m : Monomial) (c : E) : (FormRust.term m c).terms ≠ [] := by
  simp [FormRust.term]

/-- `prod(flag, b, 0)` at `sp' + 24` from `0x80004f04`, then `0x80004f28`. -/
theorem prodB (hP : ProdSpec) {s u : MachineState} (hpre : LimbPre s) (c : Inv s u)
    (hpc : u.pc = 0x80004f04) :
    ∃ w, Reaches Image.code u w ∧ ((w.pc = 0x80004f28 ∧ Inv s w ∧ heapNext u ≤ heapNext w ∧
      (∀ r ∈ [Reg.x18, .x19, .x20, .x21, .x22], w.getReg r = u.getReg r) ∧
      w.getReg .x9 ≠ 0xffffffffffffffff ∧
      Held w (s.getReg .x2 - 184) (prodRust (u.getReg .x19).toNat (u.getReg .x18).toNat 0)
        (heapNext u) (heapNext w) ∧
      ∀ e f l h, Held u e f l h → h ≤ heapNext u →
        (s.getReg .x2).toNat - 208 ≤ e.toNat → e.toNat + 24 ≤ (s.getReg .x2).toNat - 64 →
        Apart e 24 (s.getReg .x2 - 184) 24 → Held w e f l h) ∨ Dead Image.code w) := by
  obtain ⟨hsb, -⟩ := facts hpre
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80004f04_spec hpc trivial
  have k₁ := b80004f04_keeps h₁
  have c₁ := c.same hpre (b80004f04_mem_same h₁) fun r hr ↦ k₁ r (mem_of_mem hr _)
  obtain ⟨v, hrv, ⟨hpcv, hpres, cv, hmv, bv, kv⟩ | hd⟩ := newAt (F := fun s ↦
      prodRust (s.getReg .x11).toNat (s.getReg .x12).toNat (s.getReg .x13).toNat)
    (o := s.getReg .x2 - 184) hP hpre c₁ hr₁
    (b80004f04_pc h₁) (by rw [b80004f04_x10 h₁, c.x2]; addr_omega [hsb]) (by addr_omega [hsb])
    (by addr_omega [hsb]) (by addr_omega [hsb])
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  obtain ⟨w, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80004f1c_spec
    (by rw [hpcv, returnAddress_eq, b80004f04_x1 h₁]; decide) (by
      rv_eval [cv.x2]; valid_access hpre.stack.valid [hsb])
  have k₂ := b80004f1c_keeps h₂
  have hm₂ := b80004f1c_mem_same h₂
  have hn : heapNext w = heapNext v := by simp only [heapNext, hm₂]
  have hn₁ : heapNext u₁ = heapNext u := by simp only [heapNext, b80004f04_mem_same h₁]
  refine ⟨w, hrv.trans hr₂, Or.inl ⟨b80004f1c_pc h₂,
    cv.same hpre hm₂ fun r hr ↦ k₂ r (mem_of_mem hr _), by rw [hn, ← hn₁]; exact hmv,
    fun r hr ↦ by rw [k₂ r (mem_of_mem hr _), hpres r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)],
    ?_, ?_, fun e f l h b hh he₁ he₂ hap ↦ ?_⟩⟩
  · rw [b80004f1c_x9 h₂, cv.x2, show s.getReg .x2 - 208 + 24 = s.getReg .x2 - 184 by addr_omega [hsb]]
    exact cap_ne cv.heap bv.ok
  · have := bv.same cv.heap hm₂ (by addr_omega [hsb])
    rw [hn, hn₁, b80004f04_x11 h₁, b80004f04_x12 h₁, b80004f04_x13 h₁] at *
    simpa using this
  · have := kv e f l h (b.same c.heap (b80004f04_mem_same h₁) (by addr_omega [hsb, he₂]))
      (by rw [hn₁]; exact hh) he₁ he₂ hap
    exact this.same cv.heap hm₂ (by addr_omega [hsb, he₂])

/-- From `0x80004f28`, the summands in their slots: the sum, returned. -/
theorem fromF28 (hA : AddScaledSpec) {s w : MachineState} (hpre : LimbPre s) (c : Inv s w)
    (hpc : w.pc = 0x80004f28) {oc op ob : Option FormRust}
    (sc : Slot s w (heapNext w) .x21 (s.getReg .x2 - 136) oc)
    (sp : Slot s w (heapNext w) .x20 (s.getReg .x2 - 160) op)
    (sb : Slot s w (heapNext w) .x9 (s.getReg .x2 - 184) ob) :
    Done s w (addOpt (addOpt (addOpt {} oc) op) ob) := by
  have hH := c.mono
  obtain ⟨z₁, hr₁, ⟨m₁, hp₁⟩ | hd⟩ := stageA hA hpre c hpc hH sc
  · obtain ⟨z₂, hr₂, ⟨m₂, hp₂⟩ | hd⟩ := stageB hA hpre hH m₁ hp₁ sp
    · obtain ⟨z₃, hr₃, ⟨m₃, hp₃⟩ | hd⟩ := stageC hA hpre hH m₂ hp₂ sb
      · obtain ⟨t, ht, rest⟩ := stageD hpre hH m₃ hp₃
        exact ⟨t, hr₁.trans (hr₂.trans (hr₃.trans ht)), Or.inl rest⟩
      · exact ⟨z₃, hr₁.trans (hr₂.trans hr₃), Or.inr hd⟩
    · exact ⟨z₂, hr₁.trans hr₂, Or.inr hd⟩
  · exact ⟨z₁, hr₁, Or.inr hd⟩

/-- `a` is `None`, `b` is `Some`: `prod(flag, b)` alone (`0x80004ec0`). -/
theorem onlyB (hP : ProdSpec) (hA : AddScaledSpec) {s z : MachineState} (hpre : LimbPre s)
    (c : Inv s z) (hpc : z.pc = 0x80004ec0) :
    Done s z (addOpt (addOpt (addOpt {} none) none)
      (some (prodRust (z.getReg .x19).toNat (z.getReg .x18).toNat 0))) := by
  obtain ⟨hsb, -⟩ := facts hpre
  obtain ⟨u, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80004ec0_spec hpc trivial
  have k₁ := b80004ec0_keeps h₁
  have c₁ := c.same hpre (b80004ec0_mem_same h₁) fun r hr ↦ k₁ r (mem_of_mem hr _)
  obtain ⟨w, hr₂, ⟨hpw, cw, -, hreg, h9, bw, -⟩ | hd⟩ := prodB hP hpre c₁ (b80004ec0_pc h₁)
  swap
  · exact ⟨w, hr₁.trans hr₂, Or.inr hd⟩
  have hu := c₁.mono
  refine Done.back (hr₁.trans hr₂) ?_
  rw [k₁ .x19 (by decide), k₁ .x18 (by decide)] at bw
  exact fromF28 hA hpre cw hpw (by
      show w.getReg .x21 = _; rw [hreg .x21 (by decide), b80004ec0_x21 h₁])
    (by show w.getReg .x20 = _; rw [hreg .x20 (by decide), b80004ec0_x20 h₁])
    ⟨terms_ne _ _, bw.weaken hu (le_refl _), h9⟩

/-- `a` is `Some`, and `b` is `None` or another lane: `col(a)`, `prod(flag, a)`, then
`prod(flag, b)` if `b` is `Some` (from `0x80004ecc`). -/
theorem withA (hC : ColSpec) (hP : ProdSpec) (hA : AddScaledSpec) {s z : MachineState}
    (hpre : LimbPre s) (c : Inv s z) (hpc : z.pc = 0x80004ecc) :
    Done s z (addOpt (addOpt (addOpt {} (some (colRust (z.getReg .x9).toNat 0)))
      (some (prodRust (z.getReg .x19).toNat (z.getReg .x9).toNat 0)))
      (if z.getReg .x22 = 0 then none
        else some (prodRust (z.getReg .x19).toNat (z.getReg .x18).toNat 0))) := by
  obtain ⟨hsb, -⟩ := facts hpre
  have x2 := c.x2
  -- `col(a, 0)` at `sp' + 72`
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80004ecc_spec hpc trivial
  have k₁ := b80004ecc_keeps h₁
  have c₁ := c.same hpre (b80004ecc_mem_same h₁) fun r hr ↦ k₁ r (mem_of_mem hr _)
  obtain ⟨v₁, hr₂, ⟨hpc₂, hp₂, c₂, hm₂, b₂, kp₂⟩ | hd⟩ := newAt (F := fun s ↦
      colRust (s.getReg .x11).toNat (s.getReg .x12).toNat) (o := s.getReg .x2 - 136) hC hpre c₁ hr₁
    (b80004ecc_pc h₁) (by rw [b80004ecc_x10 h₁, x2]; addr_omega [hsb]) (by addr_omega [hsb])
    (by addr_omega [hsb]) (by addr_omega [hsb])
  swap
  · exact ⟨v₁, hr₂, Or.inr hd⟩
  have hreg₂ (r : Reg) (hr : r ∈ [Reg.x9, .x18, .x19, .x20, .x22]) : v₁.getReg r = z.getReg r := by
    rw [hp₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  -- `prod(flag, a, 0)` at `sp' + 48`
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80004ee0_spec
    (by rw [hpc₂, returnAddress_eq, b80004ecc_x1 h₁]; decide) (by
      rv_eval [c₂.x2]; valid_access hpre.stack.valid [hsb])
  have k₃ := b80004ee0_keeps h₃
  have c₃ := c₂.same hpre (b80004ee0_mem_same h₃) fun r hr ↦ k₃ r (mem_of_mem hr _)
  have y21 : u₃.getReg .x21 ≠ 0xffffffffffffffff := by
    rw [b80004ee0_x21 h₃, c₂.x2, show s.getReg .x2 - 208 + 72 = s.getReg .x2 - 136 by
      addr_omega [hsb]]
    exact cap_ne c₂.heap b₂.ok
  obtain ⟨v₃, hr₄, ⟨hpc₄, hp₄, c₄, hm₄, b₄, kp₄⟩ | hd⟩ := newAt (F := fun s ↦
      prodRust (s.getReg .x11).toNat (s.getReg .x12).toNat (s.getReg .x13).toNat)
    (o := s.getReg .x2 - 160) hP hpre c₃ hr₃
    (b80004ee0_pc h₃) (by rw [b80004ee0_x10 h₃, c₂.x2]; addr_omega [hsb]) (by addr_omega [hsb])
    (by addr_omega [hsb]) (by addr_omega [hsb])
  swap
  · exact ⟨v₃, hr₂.trans hr₄, Or.inr hd⟩
  have hn₃ : heapNext u₃ = heapNext v₁ := by simp only [heapNext, b80004ee0_mem_same h₃]
  have hn₁ : heapNext u₁ = heapNext z := by simp only [heapNext, b80004ecc_mem_same h₁]
  have bc₄ := kp₄ _ _ _ _ (b₂.same c₂.heap (b80004ee0_mem_same h₃) (by addr_omega [hsb]))
    (by rw [hn₃]) (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb])
  have hreg₄ (r : Reg) (hr : r ∈ [Reg.x9, .x18, .x19, .x22]) : v₃.getReg r = z.getReg r := by
    rw [hp₄ r (mem_of_mem hr _), k₃ r (mem_of_mem hr _), hreg₂ r (mem_of_mem hr _)]
  have y21₄ : v₃.getReg .x21 ≠ 0xffffffffffffffff := by rw [hp₄ .x21 (by decide)]; exact y21
  -- the values
  have vcol : colRust (u₁.getReg .x11).toNat (u₁.getReg .x12).toNat = colRust (z.getReg .x9).toNat 0 := by
    rw [b80004ecc_x11 h₁, b80004ecc_x12 h₁]; rfl
  have vprod : prodRust (u₃.getReg .x11).toNat (u₃.getReg .x12).toNat (u₃.getReg .x13).toNat =
      prodRust (z.getReg .x19).toNat (z.getReg .x9).toNat 0 := by
    rw [b80004ee0_x11 h₃, b80004ee0_x12 h₃, b80004ee0_x13 h₃, hreg₂ .x19 (by decide),
      hreg₂ .x9 (by decide)]; rfl
  rw [vcol] at bc₄
  rw [vprod] at b₄
  have hz := c.mono
  have h12 : heapNext z ≤ heapNext v₁ := by rw [← hn₁]; exact hm₂
  -- `0x80004efc`: `s4`, and `b`
  obtain ⟨u₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80004efc_spec
    (by rw [hpc₄, returnAddress_eq, b80004ee0_x1 h₃]; decide) (by
      rv_eval [c₄.x2]; valid_access hpre.stack.valid [hsb])
  have k₅ := b80004efc_keeps h₅
  have c₅ := c₄.same hpre (b80004efc_mem_same h₅) fun r hr ↦ k₅ r (mem_of_mem hr _)
  have hn₅ : heapNext u₅ = heapNext v₃ := by simp only [heapNext, b80004efc_mem_same h₅]
  have y20 : u₅.getReg .x20 ≠ 0xffffffffffffffff := by
    rw [b80004efc_x20 h₅, c₄.x2, show s.getReg .x2 - 208 + 48 = s.getReg .x2 - 160 by
      addr_omega [hsb]]
    exact cap_ne c₄.heap b₄.ok
  have bc₅ := bc₄.same c₄.heap (b80004efc_mem_same h₅) (by addr_omega [hsb])
  have bp₅ := b₄.same c₄.heap (b80004efc_mem_same h₅) (by addr_omega [hsb])
  refine Done.back (hr₂.trans (hr₄.trans hr₅)) ?_
  by_cases hb : z.getReg .x22 = 0
  · obtain ⟨w, hr₆, h₆⟩ := Sym.BlockSpec.reaches b80004f24_spec
      (b80004efc_pc_taken h₅ (by rw [hreg₄ .x22 (by decide), hb])) trivial
    have k₆ := b80004f24_keeps h₆
    have hm₆ := b80004f24_mem_same h₆
    have hn₆ : heapNext w = heapNext u₅ := by simp only [heapNext, hm₆]
    refine Done.back hr₆ ?_
    simp only [hb, ↓reduceIte]
    exact fromF28 hA hpre (c₅.same hpre hm₆ fun r hr ↦ k₆ r (mem_of_mem hr _)) (b80004f24_pc h₆)
      ⟨terms_ne _ _, (bc₅.same c₅.heap hm₆ (by addr_omega [hsb])).weaken (by rw [hn₁]; exact hz)
        (by rw [hn₆, hn₅]; exact le_trans (by rw [hn₃]) hm₄), by
          rw [k₆ .x21 (by decide), k₅ .x21 (by decide)]; exact y21₄⟩
      ⟨terms_ne _ _, (bp₅.same c₅.heap hm₆ (by addr_omega [hsb])).weaken (by rw [hn₃]; omega)
        (by rw [hn₆, hn₅]), by rw [k₆ .x20 (by decide)]; exact y20⟩
      (b80004f24_x9 h₆)
  · obtain ⟨w, hr₆, ⟨hpw, cw, hmw, hreg, h9, bw, kw⟩ | hd⟩ := prodB hP hpre c₅
      (b80004efc_pc_not_taken h₅ (by rw [hreg₄ .x22 (by decide)]; exact hb))
    swap
    · exact ⟨w, hr₆, Or.inr hd⟩
    refine Done.back hr₆ ?_
    simp only [hb, ↓reduceIte]
    rw [k₅ .x19 (by decide), k₅ .x18 (by decide), hreg₄ .x19 (by decide),
      hreg₄ .x18 (by decide)] at bw
    exact fromF28 hA hpre cw hpw
      ⟨terms_ne _ _, (kw _ _ _ _ bc₅ (by rw [hn₅]; exact le_trans (by rw [hn₃]) hm₄)
        (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb])).weaken (by rw [hn₁]; exact hz)
        (by omega), by
          rw [hreg .x21 (by decide), k₅ .x21 (by decide)]; exact y21₄⟩
      ⟨terms_ne _ _, (kw _ _ _ _ bp₅ (by rw [hn₅]) (by addr_omega [hsb]) (by addr_omega [hsb])
        (by addr_omega [hsb])).weaken (by rw [hn₃]; omega) (by rw [← hn₅]; exact hmw), by
          rw [hreg .x20 (by decide)]; exact y20⟩
      ⟨terms_ne _ _, bw.weaken (by have := c₄.mono; omega) (le_refl _), h9⟩

end Rv64Verifier.Layout.Limb
