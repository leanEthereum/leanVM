import Rv64Verifier.Proofs.Layout.LimbCalls

/-!
# `flushes_keccak`'s `limb` closure: the reads

`0x80004de4` saves the registers; `0x80004e14`/`0x80004e34` and `0x80004e3c`/`0x80004e2c` read
`lane(e)` into `a0`/`s1` and `lane(o)` into `a2`/`s2`; `0x80004e50` to `0x80004e74` take `missing`
for a lane that is `None` and read `flag` into `s3`. `Ready` is the state at the branch on `a`.
-/

namespace Rv64Verifier.Layout.Limb
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F13 Rv64Verifier.Model.LayoutMirror

/-- `missing`. -/
abbrev missingOf (s : MachineState) : Option ℕ :=
  optOf (s.getMem (limbMissing s)) (s.getMem (limbMissing s + 8))

/-- `a`, `b`. -/
abbrev aOf (s : MachineState) : Option ℕ :=
  (laneOf (limbLanes s) (s.getReg .x12) (s.getReg .x13)).or (missingOf s)
abbrev bOf (s : MachineState) : Option ℕ :=
  (laneOf (limbLanes s) (s.getReg .x14) (s.getReg .x15)).or (missingOf s)

/-- At the branch on `a`: `a` in `a0`/`s1`, `b` in `s6`/`s2`, `flag` in `s3`. -/
structure Ready (s u : MachineState) : Prop extends Inv s u where
  a : optOf (u.getReg .x10) (u.getReg .x9) = aOf s
  b : optOf (u.getReg .x22) (u.getReg .x18) = bOf s
  flag : u.getReg .x19 = s.getMem (limbFlagPtr s)
  pc : u.pc = if u.getReg .x10 = 0 then 0x80004ebc else 0x80004e80

/-- After the prologue, memory is the entry's but the saved registers. -/
def Same (s u : MachineState) : Prop := ∀ a, ¬ Within a (s.getReg .x2 - 64) 64 → u.getMem a = s.getMem a

theorem Same.read {s u : MachineState} (hpre : LimbPre s) (h : Same s u) {a : Word}
    (ha : Apart a 8 (stackLo s limbStack) limbStack) (hw : a.toNat + 8 ≤ 2 ^ 64) :
    u.getMem a = s.getMem a := by
  obtain ⟨hsb, -⟩ := facts hpre
  simp only [limbStack, colStack, powStack, Contracts.mulStack, Nat.reduceAdd] at ha
  exact h a (by addr_omega [ha, hsb, hw])

/-- The prologue. -/
theorem entry {s : MachineState} (hpre : LimbPre s) (hpc : s.pc = 0x80004de4) :
    ∃ u, Reaches Image.code s u ∧ Inv s u ∧ Same s u ∧ u.getReg .x16 = 1 ∧
      (∀ r ∈ [Reg.x11, .x12, .x13, .x14, .x15], u.getReg r = s.getReg r) ∧
      u.pc = if s.getReg .x12 ≠ 1 then 0x80004e34 else 0x80004e14 := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  obtain ⟨u, hr, h⟩ := Sym.BlockSpec.reaches b80004de4_spec hpc (by
    rv_eval []; and_intros <;> valid_access hpre.stack.valid [hsb])
  have k := b80004de4_keeps h
  have hm := b80004de4_frame h (by addr_omega [hsb])
  have hn : heapNext u = heapNext s := by
    simp only [heapNext]; rw [hm _ (by addr_omega [hnx, hsb])]
  refine ⟨u, hr, {
    x2 := b80004de4_x2 h
    x8 := b80004de4_x8 h
    regs := fun r hr ↦ k r (mem_of_mem hr _)
    ra := b80004de4_m_x2_n8 h
    s0 := b80004de4_m_x2_n16 h
    s1 := b80004de4_m_x2_n24 h
    s2 := b80004de4_m_x2_n32 h
    s3 := b80004de4_m_x2_n40 h
    s4 := b80004de4_m_x2_n48 h
    s5 := b80004de4_m_x2_n56 h
    s6 := b80004de4_m_x2_n64 h
    heap := ⟨hn ▸ hpre.heap.lo, hn ▸ hpre.heap.hi⟩
    mono := hn.ge
    rodata := RodataOk.dframe hpre.rodata hm.dframe fun x hx hw ↦ by addr_omega [hx, hw, hsb, hro]
    frame := hm.dframe.mono fun x hx ↦ Or.inl (by addr_omega [hx, hsb]) }, hm,
    b80004de4_x16 h, fun r hr ↦ k r (mem_of_mem hr _), ?_⟩
  by_cases h1 : s.getReg .x12 = 1
  · rw [b80004de4_pc_not_taken h h1]; simp [h1]
  · rw [b80004de4_pc_taken h h1]; simp only [ne_eq, h1, not_false_eq_true, ↓reduceIte]

/-- The two lanes: `a0` = `e`'s tag and `s1` its lane, `a2` = `o`'s tag and `s2` its lane. -/
theorem lanes {s u : MachineState} (hpre : LimbPre s) (c : Inv s u) (hS : Same s u)
    (h16 : u.getReg .x16 = 1) (hr : ∀ r ∈ [Reg.x11, .x12, .x13, .x14, .x15], u.getReg r = s.getReg r)
    (hpc : u.pc = if s.getReg .x12 ≠ 1 then 0x80004e34 else 0x80004e14) :
    ∃ v, Reaches Image.code u v ∧ Inv s v ∧ Same s v ∧ v.pc = 0x80004e50 ∧
      v.getReg .x11 = s.getReg .x11 ∧ v.getReg .x10 = s.getReg .x12 ∧
      v.getReg .x12 = s.getReg .x14 ∧
      (s.getReg .x12 = 1 → v.getReg .x9 = limbLanes s + s.getReg .x13) ∧
      (s.getReg .x14 = 1 → v.getReg .x18 = limbLanes s + s.getReg .x15) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x11 := hr .x11 (by decide)
  have x12 := hr .x12 (by decide)
  have x13 := hr .x13 (by decide)
  have x14 := hr .x14 (by decide)
  have x15 := hr .x15 (by decide)
  have hE := ValidMemRange.bounds hpre.env (by decide)
  have hL1 := ValidMemRange.bounds hpre.lanes1 (by decide)
  have r0 : u.getMem (u.getReg .x11) = s.getMem (s.getReg .x11) := by
    rw [x11]; exact hS.read hpre (by have := hpre.envStack; addr_omega [this]) (by addr_omega [hE])
  have r1 : u.getMem (u.getMem (u.getReg .x11)) = s.getMem (s.getMem (s.getReg .x11)) := by
    rw [r0]; exact hS.read hpre (by have := hpre.lanes1Stack; addr_omega [this])
      (by addr_omega [hL1])
  have hL2 := ValidMemRange.bounds hpre.lanes2 (by decide)
  have r2 : u.getMem (u.getMem (u.getMem (u.getReg .x11))) = limbLanes s := by
    rw [r1]; exact hS.read hpre (by have := hpre.lanes2Stack; addr_omega [this])
      (by addr_omega [hL2])
  have vobl (w : MachineState) (hw : ∀ a, w.getMem a = u.getMem a) (h11 : w.getReg .x11 = u.getReg .x11) :
      Sym.validAccess 8 (w.getMem (w.getMem (w.getReg .x11))) = true ∧
      Sym.validAccess 8 (w.getMem (w.getReg .x11)) = true ∧ Sym.validAccess 8 (w.getReg .x11) = true := by
    rw [hw, hw, h11, r1, r0, x11]
    exact ⟨by valid_access hpre.lanes2 [hL2], by valid_access hpre.lanes1 [hL1],
      by valid_access hpre.env [hE]⟩
  have keepInv (w : MachineState) (hw : ∀ a, w.getMem a = u.getMem a)
      (hk : ∀ r ∈ [Reg.x2, .x8, .x23, .x24, .x25, .x26, .x27], w.getReg r = u.getReg r) :
      Inv s w ∧ Same s w :=
    ⟨c.same hpre hw hk, fun a ha ↦ (hw a).trans (hS a ha)⟩
  rcases hpre.evenTag with he | he <;> rcases hpre.oddTag with ho | ho
  · -- `e`, `o` both `None`
    obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80004e34_spec (by rw [hpc, he]; rfl) trivial
    have k₁ := b80004e34_keeps h₁
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80004e2c_spec
      (b80004e34_pc_taken h₁ (by rw [x14, h16, ho]; decide))
      trivial
    have k₂ := b80004e2c_keeps h₂
    have hm (a : Word) : u₂.getMem a = u.getMem a := (b80004e2c_mem_same h₂ a).trans (b80004e34_mem_same h₁ a)
    obtain ⟨c₂, S₂⟩ := keepInv u₂ hm fun r hr ↦ (k₂ r (mem_of_mem hr _)).trans (k₁ r (mem_of_mem hr _))
    exact ⟨u₂, hr₁.trans hr₂, c₂, S₂, b80004e2c_pc h₂, by rw [k₂ .x11 (by decide), k₁ .x11 (by decide), x11],
      by rw [k₂ .x10 (by decide), b80004e34_x10 h₁, he], by rw [b80004e2c_x12 h₂, ho],
      fun h ↦ absurd (he.symm.trans h) (by decide), fun h ↦ absurd (ho.symm.trans h) (by decide)⟩
  · -- `o` only
    obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80004e34_spec (by rw [hpc, he]; rfl) trivial
    have k₁ := b80004e34_keeps h₁
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80004e3c_spec
      (b80004e34_pc_not_taken h₁ (by rw [x14, h16, ho]))
      (by rv_eval []; exact vobl u₁ (b80004e34_mem_same h₁) (k₁ .x11 (by decide)))
    have k₂ := b80004e3c_keeps h₂
    have hm (a : Word) : u₂.getMem a = u.getMem a := (b80004e3c_mem_same h₂ a).trans (b80004e34_mem_same h₁ a)
    obtain ⟨c₂, S₂⟩ := keepInv u₂ hm fun r hr ↦ (k₂ r (mem_of_mem hr _)).trans (k₁ r (mem_of_mem hr _))
    refine ⟨u₂, hr₁.trans hr₂, c₂, S₂, b80004e3c_pc h₂, by rw [k₂ .x11 (by decide), k₁ .x11 (by decide), x11],
      by rw [k₂ .x10 (by decide), b80004e34_x10 h₁, he], by rw [b80004e3c_x12 h₂, ho],
      fun h ↦ absurd (he.symm.trans h) (by decide), fun _ ↦ ?_⟩
    rw [b80004e3c_x18 h₂, b80004e34_mem_same h₁, b80004e34_mem_same h₁, b80004e34_mem_same h₁,
      k₁ .x11 (by decide), k₁ .x15 (by decide), r2, x15]
  · -- `e` only
    obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80004e14_spec (by rw [hpc, he]; rfl)
      (by rv_eval []; exact vobl u (fun _ ↦ rfl) rfl)
    have k₁ := b80004e14_keeps h₁
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80004e2c_spec
      (b80004e14_pc_not_taken h₁ (by rw [x14, h16, ho]; decide))
      trivial
    have k₂ := b80004e2c_keeps h₂
    have hm (a : Word) : u₂.getMem a = u.getMem a := (b80004e2c_mem_same h₂ a).trans (b80004e14_mem_same h₁ a)
    obtain ⟨c₂, S₂⟩ := keepInv u₂ hm fun r hr ↦ (k₂ r (mem_of_mem hr _)).trans (k₁ r (mem_of_mem hr _))
    refine ⟨u₂, hr₁.trans hr₂, c₂, S₂, b80004e2c_pc h₂, by rw [k₂ .x11 (by decide), k₁ .x11 (by decide), x11],
      by rw [k₂ .x10 (by decide), b80004e14_x10 h₁, he], by rw [b80004e2c_x12 h₂, ho],
      fun _ ↦ ?_, fun h ↦ absurd (ho.symm.trans h) (by decide)⟩
    rw [k₂ .x9 (by decide), b80004e14_x9 h₁, r2, x13]
  · -- both
    obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80004e14_spec (by rw [hpc, he]; rfl)
      (by rv_eval []; exact vobl u (fun _ ↦ rfl) rfl)
    have k₁ := b80004e14_keeps h₁
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80004e3c_spec
      (b80004e14_pc_taken h₁ (by rw [x14, h16, ho]))
      (by rv_eval []; exact vobl u₁ (b80004e14_mem_same h₁) (k₁ .x11 (by decide)))
    have k₂ := b80004e3c_keeps h₂
    have hm (a : Word) : u₂.getMem a = u.getMem a := (b80004e3c_mem_same h₂ a).trans (b80004e14_mem_same h₁ a)
    obtain ⟨c₂, S₂⟩ := keepInv u₂ hm fun r hr ↦ (k₂ r (mem_of_mem hr _)).trans (k₁ r (mem_of_mem hr _))
    refine ⟨u₂, hr₁.trans hr₂, c₂, S₂, b80004e3c_pc h₂, by rw [k₂ .x11 (by decide), k₁ .x11 (by decide), x11],
      by rw [k₂ .x10 (by decide), b80004e14_x10 h₁, he], by rw [b80004e3c_x12 h₂, ho],
      fun _ ↦ ?_, fun _ ↦ ?_⟩
    · rw [k₂ .x9 (by decide), b80004e14_x9 h₁, r2, x13]
    · rw [b80004e3c_x18 h₂, b80004e14_mem_same h₁, b80004e14_mem_same h₁, b80004e14_mem_same h₁,
        k₁ .x11 (by decide), k₁ .x15 (by decide), r2, x15]

theorem opt_or {t m v mv L ev : Word} (ht : t = 0 ∨ t = 1) (hv : t = 1 → v = L + ev)
    (hm : t = 0 → v = mv) : optOf (m ||| t) v = (laneOf L t ev).or (optOf m mv) := by
  rcases ht with rfl | rfl
  · have h0 : m ||| (0 : Word) = m := by ext i; simp
    simp only [h0, laneOf, ↓reduceIte, Option.none_or, hm rfl]
  · have h1 : m ||| 1 ≠ 0 := by
      intro h
      have := congrArg (BitVec.getLsbD · 0) h
      simp at this
    simp only [optOf, h1, ↓reduceIte, laneOf, hv rfl]
    rfl

/-- `missing` and `flag`, into `Ready`. -/
theorem ready {s u : MachineState} (hpre : LimbPre s) (c : Inv s u) (hS : Same s u)
    (hpc : u.pc = 0x80004e50) (x11 : u.getReg .x11 = s.getReg .x11)
    (x10 : u.getReg .x10 = s.getReg .x12) (x12 : u.getReg .x12 = s.getReg .x14)
    (x9 : s.getReg .x12 = 1 → u.getReg .x9 = limbLanes s + s.getReg .x13)
    (x18 : s.getReg .x14 = 1 → u.getReg .x18 = limbLanes s + s.getReg .x15) :
    ∃ v, Reaches Image.code u v ∧ Ready s v := by
  have hE := ValidMemRange.bounds hpre.env (by decide)
  have es := hpre.envStack
  have hM := ValidMemRange.bounds hpre.missing (by decide)
  have ms := hpre.missingStack
  have hF := ValidMemRange.bounds hpre.flag (by decide)
  have fs := hpre.flagStack
  simp only [limbMissing, limbFlagPtr] at hM ms hF fs
  have rM : u.getMem (s.getReg .x11 + 16) = limbMissing s :=
    hS.read hpre (by addr_omega [es, hE]) (by addr_omega [hE])
  have rM0 : u.getMem (limbMissing s) = s.getMem (limbMissing s) :=
    hS.read hpre (by simp only [limbMissing]; addr_omega [ms, hM]) (by simp only [limbMissing]; addr_omega [hM])
  have rM8 : u.getMem (limbMissing s + 8) = s.getMem (limbMissing s + 8) :=
    hS.read hpre (by simp only [limbMissing]; addr_omega [ms, hM]) (by simp only [limbMissing]; addr_omega [hM])
  have rF : u.getMem (s.getReg .x11 + 8) = limbFlagPtr s :=
    hS.read hpre (by addr_omega [es, hE]) (by addr_omega [hE])
  have rF0 : u.getMem (limbFlagPtr s) = s.getMem (limbFlagPtr s) :=
    hS.read hpre (by simp only [limbFlagPtr]; addr_omega [fs, hF]) (by simp only [limbFlagPtr]; addr_omega [hF])
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80004e50_spec hpc (by
    rv_eval [x11, rM]
    simp only [limbMissing] at hM ⊢
    and_intros
    · valid_access hpre.missing [hM]
    · valid_access hpre.missing [hM]
    · valid_access hpre.env [hE])
  have k₁ := b80004e50_keeps h₁
  have m₁ := b80004e50_mem_same h₁
  have y13 : u₁.getReg .x13 = s.getMem (limbMissing s) := by rw [b80004e50_x13 h₁, x11, rM, rM0]
  have y14 : u₁.getReg .x14 = s.getMem (limbMissing s + 8) := by rw [b80004e50_x14 h₁, x11, rM, rM8]
  -- `a`: `missing` for `None`
  obtain ⟨u₂, hr₂, hm₂, hk₂, hpc₂, hv1, hv0⟩ : ∃ u₂, Reaches Image.code u₁ u₂ ∧
      (∀ a, u₂.getMem a = u₁.getMem a) ∧
      (∀ r ∈ [Reg.x2, .x8, .x10, .x11, .x12, .x13, .x14, .x18, .x23, .x24, .x25, .x26, .x27],
        u₂.getReg r = u₁.getReg r) ∧ u₂.pc = 0x80004e64 ∧
      (s.getReg .x12 = 1 → u₂.getReg .x9 = limbLanes s + s.getReg .x13) ∧
      (s.getReg .x12 = 0 → u₂.getReg .x9 = s.getMem (limbMissing s + 8)) := by
    by_cases h0 : s.getReg .x12 = 0
    · obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80004e60_spec
        (b80004e50_pc_not_taken h₁ (by rw [x10, h0])) trivial
      have k₂ := b80004e60_keeps h₂
      exact ⟨u₂, hr₂, b80004e60_mem_same h₂, fun r hr ↦ k₂ r (mem_of_mem hr _), b80004e60_pc h₂,
        fun h ↦ absurd (h0.symm.trans h) (by decide), fun _ ↦ by rw [b80004e60_x9 h₂, y14]⟩
    · refine ⟨u₁, Reaches.refl _, fun _ ↦ rfl, fun _ _ ↦ rfl,
        b80004e50_pc_taken h₁ (by rw [x10]; exact h0), fun h ↦ ?_, fun h ↦ absurd h h0⟩
      rw [k₁ .x9 (by decide)]; exact x9 h
  have z11 : u₂.getReg .x11 = s.getReg .x11 := by rw [hk₂ .x11 (by decide), k₁ .x11 (by decide), x11]
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80004e64_spec hpc₂ (by
    rv_eval [z11]; valid_access hpre.env [hE])
  have k₃ := b80004e64_keeps h₃
  have z10 : u₃.getReg .x10 = s.getMem (limbMissing s) ||| s.getReg .x12 := by
    rw [b80004e64_x10 h₃, hk₂ .x13 (by decide), hk₂ .x10 (by decide), y13, k₁ .x10 (by decide), x10]
  have z11' : u₃.getReg .x11 = limbFlagPtr s := by
    rw [b80004e64_x11 h₃, z11, hm₂, m₁, rF]
  -- `b`: `missing` for `None`
  obtain ⟨u₄, hr₄, hm₄, hk₄, hpc₄, hw1, hw0⟩ : ∃ u₄, Reaches Image.code u₃ u₄ ∧
      (∀ a, u₄.getMem a = u₃.getMem a) ∧
      (∀ r ∈ [Reg.x2, .x8, .x9, .x10, .x11, .x12, .x13, .x23, .x24, .x25, .x26, .x27],
        u₄.getReg r = u₃.getReg r) ∧ u₄.pc = 0x80004e74 ∧
      (s.getReg .x14 = 1 → u₄.getReg .x18 = limbLanes s + s.getReg .x15) ∧
      (s.getReg .x14 = 0 → u₄.getReg .x18 = s.getMem (limbMissing s + 8)) := by
    have x12₂ : u₂.getReg .x12 = s.getReg .x14 := by rw [hk₂ .x12 (by decide), k₁ .x12 (by decide), x12]
    by_cases h0 : s.getReg .x14 = 0
    · obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80004e70_spec
        (b80004e64_pc_not_taken h₃ (by rw [x12₂, h0])) trivial
      have k₄ := b80004e70_keeps h₄
      exact ⟨u₄, hr₄, b80004e70_mem_same h₄, fun r hr ↦ k₄ r (mem_of_mem hr _), b80004e70_pc h₄,
        fun h ↦ absurd (h0.symm.trans h) (by decide), fun _ ↦ by
          rw [b80004e70_x18 h₄, k₃ .x14 (by decide), hk₂ .x14 (by decide), y14]⟩
    · refine ⟨u₃, Reaches.refl _, fun _ ↦ rfl, fun _ _ ↦ rfl,
        b80004e64_pc_taken h₃ (by rw [x12₂]; exact h0), fun h ↦ ?_, fun h ↦ absurd h h0⟩
      rw [k₃ .x18 (by decide), hk₂ .x18 (by decide), k₁ .x18 (by decide)]; exact x18 h
  have z11'' : u₄.getReg .x11 = limbFlagPtr s := by rw [hk₄ .x11 (by decide), z11']
  obtain ⟨v, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80004e74_spec hpc₄ (by
    rv_eval [z11'']; simp only [limbFlagPtr] at hF ⊢; valid_access hpre.flag [hF])
  have k₅ := b80004e74_keeps h₅
  have hmv (a : Word) : v.getMem a = u.getMem a := by
    rw [b80004e74_mem_same h₅, hm₄, b80004e64_mem_same h₃, hm₂, m₁]
  have z10' : v.getReg .x10 = s.getMem (limbMissing s) ||| s.getReg .x12 := by
    rw [k₅ .x10 (by decide), hk₄ .x10 (by decide), z10]
  refine ⟨v, hr₁.trans (hr₂.trans (hr₃.trans (hr₄.trans hr₅))), {
    toInv := c.same hpre hmv fun r hr ↦ by
      rw [k₅ r (mem_of_mem hr _), hk₄ r (mem_of_mem hr _), k₃ r (mem_of_mem hr _),
        hk₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
    a := ?_
    b := ?_
    flag := by rw [b80004e74_x19 h₅, z11'', hm₄, b80004e64_mem_same h₃, hm₂, m₁, rF0]
    pc := ?_ }⟩
  · rw [z10', k₅ .x9 (by decide), hk₄ .x9 (by decide), k₃ .x9 (by decide)]
    exact opt_or hpre.evenTag hv1 hv0
  · rw [b80004e74_x22 h₅, hk₄ .x13 (by decide), k₃ .x13 (by decide), hk₂ .x13 (by decide), y13,
      hk₄ .x12 (by decide), k₃ .x12 (by decide), hk₂ .x12 (by decide), k₁ .x12 (by decide), x12,
      k₅ .x18 (by decide)]
    exact opt_or hpre.oddTag hw1 hw0
  · by_cases h0 : v.getReg .x10 = 0
    · rw [b80004e74_pc_taken h₅ (by rw [← k₅ .x10 (by decide)]; exact h0)]; simp only [h0, ↓reduceIte]
    · rw [b80004e74_pc_not_taken h₅ (by rw [← k₅ .x10 (by decide)]; exact h0)]
      simp only [h0, ↓reduceIte]

end Rv64Verifier.Layout.Limb
