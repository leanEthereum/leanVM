import Rv64Verifier.Proofs.Layout.LimbPaths

/-!
# `flushes_keccak`'s `limb` closure meets its contract

`bothNone` and `equal` end in a single form; `onlyB` and `withA` (`LimbPaths.lean`) in the sum.
-/

namespace Rv64Verifier.Layout.Limb
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F13 Rv64Verifier.Model.LayoutMirror

/-- `a`, `b` both `None`: `constant(ZERO)` at `sp'` (`0x8000504c`), moved to `a0`. -/
theorem bothNone (hT : TermSpec) {s z : MachineState} (hpre : LimbPre s) (c : Inv s z)
    (hpc : z.pc = 0x8000504c) : Done s z (constantRust 0) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hob := ValidMemRange.bounds hpre.out (by decide)
  have hof := hpre.outFree
  obtain ⟨u, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000504c_spec hpc (by
    rv_eval [c.x2]; valid_access hpre.stack.valid [hsb])
  have k₁ := b8000504c_keeps h₁
  have hm₁ := b8000504c_frame h₁ (by rw [c.x2]; addr_omega [hsb])
  rw [c.x2, show s.getReg .x2 - 208 + 96 = s.getReg .x2 - 112 by addr_omega [hsb]] at hm₁
  have c₁ := c.block hpre hm₁ (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ k₁ r (mem_of_mem hr _)
  obtain ⟨v, hr₂, ⟨hpc₂, -, cv, bv⟩ | hd⟩ := termCall hT hpre c₁ hr₁ (b8000504c_pc h₁)
    (by rw [b8000504c_x10 h₁, c.x2]) (by rw [b8000504c_x11 h₁, c.x2]; addr_omega [hsb])
    (b8000504c_x12 h₁) (by
      have := b8000504c_m_x2_96 h₁
      rw [c.x2, show s.getReg .x2 - 208 + 96 = s.getReg .x2 - 112 by addr_omega [hsb]] at this
      exact this)
  swap
  · exact ⟨v, hr₂, Or.inr hd⟩
  have x8 : v.getReg .x8 = s.getReg .x10 := cv.x8
  obtain ⟨y, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80005068_spec
    (by rw [hpc₂, returnAddress_eq, b8000504c_x1 h₁]; decide) (by
      rv_eval [x8, cv.x2]; and_intros
      · valid_access hpre.out [hob]
      · valid_access hpre.out [hob]
      · valid_access hpre.out [hob]
      · valid_access hpre.stack.valid [hsb]
      · valid_access hpre.stack.valid [hsb]
      · valid_access hpre.stack.valid [hsb])
  have k₃ := b80005068_keeps h₃
  have hm := b80005068_frame h₃ (by rw [x8]; addr_omega [hob])
  rw [x8] at hm
  have hn : heapNext y = heapNext v := by
    simp only [heapNext]; rw [hm _ (by addr_omega [hof])]
  have m0 := b80005068_m_x8_0 h₃
  have m8 := b80005068_m_x8_8 h₃
  have m16 := b80005068_m_x8_16 h₃
  rw [x8, cv.x2] at m0 m8 m16
  have hu := c₁.mono
  have hhv := cv.heap.hi
  have hk := formOf_move hm.dframe bv.ok m0 m8 m16 (fun x hx hw ↦ by
      have := bv.buf x hx
      simp only [Outside, heapEnd] at hof hhv
      addr_omega [hw, this, hof, hhv, hu]) cv.heap hn.ge
  have hb : Held y (s.getReg .x10) (constantRust 0) (heapNext s) (heapNext y) := by
    refine ⟨hk.2.1, hk.1.trans bv.val, fun x hx ↦ ?_⟩
    rw [hk.2.2] at hx
    have := bv.buf x hx
    omega
  obtain ⟨t, ht, rest⟩ := finish hpre cv hm.dframe (fun a ha ↦ Or.inl ha)
    ⟨hn ▸ cv.heap.lo, hn ▸ cv.heap.hi⟩ hn.ge (fun r hr ↦ k₃ r (mem_of_mem hr _)) (b80005068_pc h₃) hb
  exact ⟨t, hr₂.trans (hr₃.trans ht), Or.inl rest⟩

/-- `a == b`, both `Some`: the eager `constant(ZERO)` (`0x80004e88`), then `col(a, 0)` into `a0`. -/
theorem equal (hT : TermSpec) (hC : ColSpec) {s z : MachineState} (hpre : LimbPre s) (c : Inv s z)
    (hpc : z.pc = 0x80004e88) : Done s z (colRust (z.getReg .x9).toNat 0) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hob := ValidMemRange.bounds hpre.out (by decide)
  have hof := hpre.outFree
  have hos := hpre.outStack
  simp only [limbStack, colStack, powStack, Contracts.mulStack, Nat.reduceAdd] at hos
  obtain ⟨u, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80004e88_spec hpc (by
    rv_eval [c.x2]; valid_access hpre.stack.valid [hsb])
  have k₁ := b80004e88_keeps h₁
  have hm₁ := b80004e88_frame h₁ (by rw [c.x2]; addr_omega [hsb])
  rw [c.x2, show s.getReg .x2 - 208 + 96 = s.getReg .x2 - 112 by addr_omega [hsb]] at hm₁
  have c₁ := c.block hpre hm₁ (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ k₁ r (mem_of_mem hr _)
  obtain ⟨v, hr₂, ⟨hpc₂, hpv, cv, -⟩ | hd⟩ := termCall hT hpre c₁ hr₁ (b80004e88_pc h₁)
    (by rw [b80004e88_x10 h₁, c.x2]) (by rw [b80004e88_x11 h₁, c.x2]; addr_omega [hsb])
    (b80004e88_x12 h₁) (by
      have := b80004e88_m_x2_96 h₁
      rw [c.x2, show s.getReg .x2 - 208 + 96 = s.getReg .x2 - 112 by addr_omega [hsb]] at this
      exact this)
  swap
  · exact ⟨v, hr₂, Or.inr hd⟩
  -- `col(a, 0)` into `a0`
  obtain ⟨w, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80004ea4_spec
    (by rw [hpc₂, returnAddress_eq, b80004e88_x1 h₁]; decide) trivial
  have k₃ := b80004ea4_keeps h₃
  have cw := cv.same hpre (b80004ea4_mem_same h₃) fun r hr ↦ k₃ r (mem_of_mem hr _)
  have x10 : w.getReg .x10 = s.getReg .x10 := by rw [b80004ea4_x10 h₃, cv.x8]
  have hcw := cw.mono
  have hcol : ColPre w := {
    heap := cw.heap
    stack := hpre.stack.inner (k := 208) cw.x2 (by decide) (by decide) (by decide) (by decide)
      (by decide)
    out := by rw [x10]; exact hpre.out
    outFree := by
      rw [x10]
      refine ⟨?_, hof.2⟩
      rcases hof.1 with h | h
      · exact Or.inl (by omega)
      · exact Or.inr h
    outStack := by rw [x10]; simp only [stackLo, cw.x2, colStack, powStack, Contracts.mulStack]
                   addr_omega [hos, hsb]
    rodata := cw.rodata }
  obtain ⟨x, hr₄, ⟨hpc₄, hpres, hnew, hval⟩ | hd⟩ := hC.call hr₃ (b80004ea4_pc h₃) hcol
  swap
  · exact ⟨x, hr₂.trans hr₄, Or.inr hd⟩
  rw [x10] at hnew hval
  obtain ⟨y, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80004eb8_spec
    (by rw [hpc₄, returnAddress_eq, b80004ea4_x1 h₃]; decide) trivial
  have k₅ := b80004eb8_keeps h₅
  have hm₅ := b80004eb8_mem_same h₅
  have hn : heapNext y = heapNext x := by simp only [heapNext, hm₅]
  have hfx := hnew.frame
  have hsl : stackLo w colStack = s.getReg .x2 - 1408 := by
    simp only [stackLo, cw.x2, colStack, powStack, Contracts.mulStack]; addr_omega [hsb]
  rw [hsl] at hfx
  have hhx := hnew.heap.hi
  obtain ⟨t, ht, rest⟩ := finish hpre cw (hfx.union (DFrame.of_same hm₅ fun _ ↦ False))
    (fun a ha ↦ by
      rcases ha with (h | h | h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (by simp only [colStack, powStack, Contracts.mulStack] at h
                                 addr_omega [h, hsb]))
      · exact Or.inr (Or.inr (Or.inl h))
      · simp only [Fresh] at h ⊢; exact Or.inr (Or.inr (Or.inr ⟨h.1, by omega⟩))
      · exact h.elim)
    ⟨hn ▸ hnew.heap.lo, hn ▸ hnew.heap.hi⟩ (by rw [hn]; exact hnew.mono)
    (fun r hr ↦ by rw [k₅ r (mem_of_mem hr _), hpres r (mem_of_mem hr _)]) (b80004eb8_pc h₅)
    ⟨(formOf_frame (DFrame.of_same hm₅ fun _ ↦ False) hnew.ok (fun _ _ h ↦ h) (fun _ _ h ↦ h)
      (by addr_omega [hob]) hnew.heap hn.ge).2,
     (formOf_frame (DFrame.of_same hm₅ fun _ ↦ False) hnew.ok (fun _ _ h ↦ h) (fun _ _ h ↦ h)
      (by addr_omega [hob]) hnew.heap hn.ge).1.trans hval, fun a ha ↦ by
        have hb := hnew.fresh
        simp only [formBuf, vecPtr, vecCap, hm₅] at ha
        simp only [NewBuf, Within, vecPtr, vecCap] at hb ha
        rw [hn]; omega⟩
  refine ⟨t, hr₂.trans (hr₄.trans (hr₅.trans ht)), Or.inl ⟨rest.1, rest.2.1, rest.2.2.1, ?_⟩⟩
  rw [rest.2.2.2, b80004ea4_x11 h₃, b80004ea4_x12 h₃, hpv .x9 (by decide), k₁ .x9 (by decide)]
  rfl

theorem sum3 (a b c : Option FormRust) :
    FormRust.sum ([a, b, c].filterMap id) = addOpt (addOpt (addOpt {} a) b) c := by
  cases a <;> cases b <;> cases c <;> rfl

theorem layoutLimb_eq (s : MachineState) :
    layoutLimbRust (laneOf (limbLanes s) (s.getReg .x12) (s.getReg .x13))
      (laneOf (limbLanes s) (s.getReg .x14) (s.getReg .x15)) (s.getMem (limbFlagPtr s)).toNat
      (missingOf s) =
    if aOf s = bOf s then ((aOf s).map (colRust · 0)).getD (constantRust 0)
    else addOpt (addOpt (addOpt {} ((aOf s).map (colRust · 0)))
      ((aOf s).map (prodRust (s.getMem (limbFlagPtr s)).toNat · 0)))
      ((bOf s).map (prodRust (s.getMem (limbFlagPtr s)).toNat · 0)) := by
  rw [← sum3]; rfl

/-- **`flushes_keccak`'s `limb` closure meets its contract**, given `term`'s, `col`'s, `prod`'s and
`add_scaled`'s. -/
theorem limb_spec (hT : TermSpec) (hC : ColSpec) (hP : ProdSpec) (hA : AddScaledSpec) :
    LimbSpec := by
  intro s hpc hpre
  obtain ⟨u₀, hr₀, c₀, S₀, h16, hr, hpc₀⟩ := entry hpre hpc
  obtain ⟨u₁, hr₁, c₁, S₁, hpc₁, x11, x10, x12, x9, x18⟩ := lanes hpre c₀ S₀ h16 hr hpc₀
  obtain ⟨u, hr₂, R⟩ := ready hpre c₁ S₁ hpc₁ x11 x10 x12 x9 x18
  suffices h : Done s u (layoutLimbRust (laneOf (limbLanes s) (s.getReg .x12) (s.getReg .x13))
      (laneOf (limbLanes s) (s.getReg .x14) (s.getReg .x15)) (s.getMem (limbFlagPtr s)).toNat
      (missingOf s)) by
    obtain ⟨t, ht, rest⟩ := h
    exact ⟨t, hr₀.trans (hr₁.trans (hr₂.trans ht)), rest⟩
  rw [layoutLimb_eq]
  have ha := R.a
  have hb := R.b
  rw [← R.flag]
  by_cases h10 : u.getReg .x10 = 0
  · -- `a` is `None`
    simp only [optOf, h10, ↓reduceIte] at ha
    rw [← ha]
    obtain ⟨u₂, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80004ebc_spec
      (by rw [R.pc]; simp only [h10, ↓reduceIte]; rfl) trivial
    have k₃ := b80004ebc_keeps h₃
    have c₃ := R.toInv.same hpre (b80004ebc_mem_same h₃) fun r hr ↦ k₃ r (mem_of_mem hr _)
    refine Done.back hr₃ ?_
    by_cases h22 : u.getReg .x22 = 0
    · simp only [optOf, h22, ↓reduceIte] at hb
      rw [← hb]
      split
      · exact bothNone hT hpre c₃ (b80004ebc_pc_taken h₃ h22)
      · rename_i hne; exact absurd rfl hne
    · simp only [optOf, h22, ↓reduceIte] at hb
      rw [← hb]
      split
      · rename_i heq; exact absurd heq (by simp)
      · have := onlyB hP hA hpre c₃ (b80004ebc_pc_not_taken h₃ h22)
        rw [k₃ .x19 (by decide), k₃ .x18 (by decide)] at this
        exact this
  · -- `a` is `Some`
    simp only [optOf, h10, ↓reduceIte] at ha
    rw [← ha]
    obtain ⟨u₂, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80004e80_spec
      (by rw [R.pc]; simp only [h10, ↓reduceIte]; rfl) trivial
    have k₃ := b80004e80_keeps h₃
    have c₃ := R.toInv.same hpre (b80004e80_mem_same h₃) fun r hr ↦ k₃ r (mem_of_mem hr _)
    refine Done.back hr₃ ?_
    by_cases h22 : u.getReg .x22 = 0
    · simp only [optOf, h22, ↓reduceIte] at hb
      rw [← hb]
      split
      · rename_i heq; exact absurd heq (by simp)
      · have := withA hC hP hA hpre c₃ (b80004e80_pc_taken h₃ h22)
        rw [k₃ .x19 (by decide), k₃ .x9 (by decide), k₃ .x22 (by decide), h22] at this
        exact this
    · simp only [optOf, h22, ↓reduceIte] at hb
      rw [← hb]
      obtain ⟨u₃, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80004e84_spec
        (b80004e80_pc_not_taken h₃ h22) trivial
      have k₄ := b80004e84_keeps h₄
      have c₄ := c₃.same hpre (b80004e84_mem_same h₄) fun r hr ↦ k₄ r (mem_of_mem hr _)
      refine Done.back hr₄ ?_
      by_cases h9 : u.getReg .x9 = u.getReg .x18
      · split
        · have := equal hT hC hpre c₄ (b80004e84_pc_not_taken h₄
            (by rw [k₃ .x9 (by decide), k₃ .x18 (by decide)]; exact h9))
          rw [k₄ .x9 (by decide), k₃ .x9 (by decide)] at this
          exact this
        · rename_i hne; exact absurd (by rw [h9]) hne
      · split
        · rename_i heq
          exact absurd (BitVec.eq_of_toNat_eq (Option.some.inj heq)) h9
        · have := withA hC hP hA hpre c₄ (b80004e84_pc_taken h₄
            (by rw [k₃ .x9 (by decide), k₃ .x18 (by decide)]; exact h9))
          rw [k₄ .x19 (by decide), k₃ .x19 (by decide), k₄ .x9 (by decide), k₃ .x9 (by decide),
            k₄ .x22 (by decide), k₃ .x22 (by decide), k₄ .x18 (by decide), k₃ .x18 (by decide)] at this
          simp only [h22, ↓reduceIte] at this
          exact this

end Rv64Verifier.Layout.Limb
