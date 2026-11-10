import Rv64Verifier.Proofs.Layout.ArithOps

/-!
# `flushes_arith`: the two operands read

`0x800055e4` calls `prod(sp' + 80, fp, o_a, 0)` and `0x800055fc` `memory_cols(sp' + 8, sp' + 80,
cnt_a, va)`; `0x8000561c` and `0x80005634` do the same for `o_b` and `vb`; `0x80005654` branches on
`multiply`.
-/

namespace Rv64Verifier.Layout.Arith
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F19 Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Layout.Limb (Held)

theorem cols_va {u : MachineState} (h : RodataOk u) : colsAt u 0xa0000f00 3 = [5, 6, 7] := by
  have h0 : u.getMem 0xa0000f00 = 5 := h.word
  have h1 : u.getMem 0xa0000f08 = 6 := h.word
  have h2 : u.getMem 0xa0000f10 = 7 := h.word
  show [(u.getMem (0xa0000f00 + BitVec.ofNat 64 (8 * 0))).toNat,
    (u.getMem (0xa0000f00 + BitVec.ofNat 64 (8 * 1))).toNat,
    (u.getMem (0xa0000f00 + BitVec.ofNat 64 (8 * 2))).toNat] = _
  rw [show (0xa0000f00 : Word) + BitVec.ofNat 64 (8 * 0) = 0xa0000f00 by decide,
    show (0xa0000f00 : Word) + BitVec.ofNat 64 (8 * 1) = 0xa0000f08 by decide,
    show (0xa0000f00 : Word) + BitVec.ofNat 64 (8 * 2) = 0xa0000f10 by decide, h0, h1, h2]
  rfl

theorem cols_vb {u : MachineState} (h : RodataOk u) : colsAt u 0xa0000f18 3 = [8, 9, 10] := by
  have h0 : u.getMem 0xa0000f18 = 8 := h.word
  have h1 : u.getMem 0xa0000f20 = 9 := h.word
  have h2 : u.getMem 0xa0000f28 = 10 := h.word
  show [(u.getMem (0xa0000f18 + BitVec.ofNat 64 (8 * 0))).toNat,
    (u.getMem (0xa0000f18 + BitVec.ofNat 64 (8 * 1))).toNat,
    (u.getMem (0xa0000f18 + BitVec.ofNat 64 (8 * 2))).toNat] = _
  rw [show (0xa0000f18 : Word) + BitVec.ofNat 64 (8 * 0) = 0xa0000f18 by decide,
    show (0xa0000f18 : Word) + BitVec.ofNat 64 (8 * 1) = 0xa0000f20 by decide,
    show (0xa0000f18 : Word) + BitVec.ofNat 64 (8 * 2) = 0xa0000f28 by decide, h0, h1, h2]
  rfl

/-- `memory_cols(sp' + 8, sp' + 80, count, columns, 3)`, the columns in `.rodata`. -/
theorem memColsCall (hK : MemoryColsSpec) {s u0 u : MachineState} (hpre : FlushesArithPre s)
    (c : Inv s u) (hr : Reaches Image.code u0 u) (hpc : u.pc = 0x80005c64) {fl : FlushesRust}
    {hi : Nat} (fb : FHeld s u fl hi) (hhi : hi ≤ heapNext u) {a : FormRust} {l h : Nat}
    (b : Held u (s.getReg .x2 - 400) a l h) (h10 : u.getReg .x10 = s.getReg .x2 - 472)
    (h11 : u.getReg .x11 = s.getReg .x2 - 400) (h14 : u.getReg .x14 = 3)
    (h13 : u.getReg .x13 = 0xa0000f00 ∨ u.getReg .x13 = 0xa0000f18) :
    ∃ v, Reaches Image.code u0 v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧ Inv s v ∧
      FHeld s v (fl.memoryCols a (u.getReg .x12).toNat (colsAt u (u.getReg .x13) 3))
        (heapNext v)) ∨ Dead Image.code v) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  have hsl : stackLo u memoryColsStack = s.getReg .x2 - 2224 := by
    simp only [stackLo, x2, memoryColsStack, memoryStack, countedStack, colStack, powStack,
      Contracts.mulStack]; addr_omega [hsb]
  have hc : ∃ p : Word, u.getReg .x13 = p ∧ 0xa0000f00 ≤ p.toNat ∧ p.toNat + 24 ≤ 0xa0000f30 ∧
      p.toNat % 8 = 0 := by
    rcases h13 with h | h <;> exact ⟨_, h, by decide, by decide, by decide⟩
  obtain ⟨p, hp, hp₁, hp₂, hp₃⟩ := hc
  have e3 : (3 : Word).toNat = 3 := rfl
  have hmp : MemoryColsPre u := {
    toFlushesPre := flushesPre hpre c fb h10 (by decide) (by decide) (by decide)
    address := by rw [h11]; valid_sub (stackValid hpre) [hsb]
    addressOk := by rw [h11]; exact b.ok
    addressFree := by rw [h11]; addr_omega [hsb, hab, hnx]
    addressStack := by rw [h11, hsl]; addr_omega [hsb]
    len := by rw [h14]; decide
    columns := by
      rw [hp, h14]
      have e3 : (3 : Word).toNat = 3 := rfl
      exact validMemRange_of hp₃ (Or.inr ⟨by omega, by omega⟩)
    columnsFree := by rw [hp, h14]; addr_omega [hp₁, hp₂]
    columnsStack := by rw [hp, h14, hsl]; addr_omega [hp₁, hp₂, hsb, hro] }
  obtain ⟨v, hrv, ⟨hpcv, hpres, hg, hval⟩ | hd⟩ := hK.call hr hpc hmp
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  rw [h10] at hg hval
  obtain ⟨cv, fv⟩ := afterGrow hpre c fb hhi (by decide) hpres hg
  rw [hval, fb.val, h11, b.val, h14] at fv
  exact ⟨v, hrv, Or.inl ⟨hpcv, hpres, cv, fv⟩⟩

/-- The `Flushes` after the two `memory_cols`. -/
def flCols (opcode : ℕ) : FlushesRust :=
  ((flBc opcode).memoryCols (prodRust 1 2 0) 11 [5, 6, 7]).memoryCols (prodRust 1 3 0) 12 [8, 9, 10]

/-- At the branch on `multiply`. -/
structure AtBranch (s u : MachineState) : Prop extends Inv s u where
  pc : u.pc = if s.getReg .x12 = 0 then 0x800059f4 else 0x80005658
  fl : FHeld s u (flCols (s.getReg .x11).toNat) (heapNext u)

/-- The two operands read, and the branch. -/
theorem cols (hP : ProdSpec) (hK : MemoryColsSpec) {s u0 u : MachineState}
    (hpre : FlushesArithPre s) (hr : Reaches Image.code u0 u) (A : AtCols s u) :
    ∃ v, Reaches Image.code u0 v ∧ (AtBranch s v ∨ Dead Image.code v) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have c := A.toInv
  -- `prod(sp' + 80, fp, o_a, 0)`, `memory_cols(sp' + 8, sp' + 80, cnt_a, va)`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800055e4_spec A.pc trivial
  have k₁ := b800055e4_keeps h₁
  have hm₁ := b800055e4_mem_same h₁
  have c₁ := c.same hpre hm₁ fun r hr ↦ k₁ r (mem_of_mem hr _)
  have K₁ := sameKeeps hpre c hm₁
  have hn₁ : heapNext t₁ = heapNext u := by simp only [heapNext, hm₁]
  obtain ⟨t₂, hr₂, ⟨hpc₂, hp₂, c₂, hn₂, b₂, K₂⟩ | hd⟩ := prodCall hP hpre c₁ (hr.trans hr₁)
    (b800055e4_pc h₁) (o := s.getReg .x2 - 400) (by rw [b800055e4_x10 h₁, c.x2]; rv_eval [])
    (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb]) (Nat.le_refl _)
    (Or.inl (by addr_omega [hsb, hab]))
  swap
  · exact ⟨t₂, hr₂, Or.inr hd⟩
  rw [b800055e4_x11 h₁, b800055e4_x12 h₁, b800055e4_x13 h₁] at b₂
  have f₂ := K₂.2 _ _ (K₁.2 _ _ A.fl (Nat.le_refl _)) (by omega)
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800055fc_spec
    (by rw [hpc₂, returnAddress_eq, b800055e4_x1 h₁]; decide) trivial
  have k₃ := b800055fc_keeps h₃
  have hm₃ := b800055fc_mem_same h₃
  have c₃ := c₂.same hpre hm₃ fun r hr ↦ k₃ r (mem_of_mem hr _)
  have K₃ := sameKeeps hpre c₂ hm₃
  have hn₃ : heapNext t₃ = heapNext t₂ := by simp only [heapNext, hm₃]
  have b₃ := K₃.1 _ _ _ _ b₂ (by omega) (Or.inl (by addr_omega [hsb])) (Or.inr (Or.inl rfl))
  have f₃ := K₃.2 _ _ f₂ (by omega)
  obtain ⟨t₄, hr₄, ⟨hpc₄, hp₄, c₄, f₄⟩ | hd⟩ := memColsCall hK hpre c₃ (hr₂.trans hr₃)
    (b800055fc_pc h₃) f₃ (by omega) b₃ (by rw [b800055fc_x10 h₃, c₂.x2]; rv_eval [])
    (by rw [b800055fc_x11 h₃, c₂.x2]; rv_eval []) (b800055fc_x14 h₃) (Or.inl (b800055fc_x13 h₃))
  swap
  · exact ⟨t₄, hr₄, Or.inr hd⟩
  rw [b800055fc_x12 h₃, b800055fc_x13 h₃, cols_va c₃.rodata] at f₄
  -- `prod(sp' + 80, fp, o_b, 0)`, `memory_cols(sp' + 8, sp' + 80, cnt_b, vb)`
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b8000561c_spec
    (by rw [hpc₄, returnAddress_eq, b800055fc_x1 h₃]; decide) trivial
  have k₅ := b8000561c_keeps h₅
  have hm₅ := b8000561c_mem_same h₅
  have c₅ := c₄.same hpre hm₅ fun r hr ↦ k₅ r (mem_of_mem hr _)
  have K₅ := sameKeeps hpre c₄ hm₅
  have hn₅ : heapNext t₅ = heapNext t₄ := by simp only [heapNext, hm₅]
  obtain ⟨t₆, hr₆, ⟨hpc₆, hp₆, c₆, hn₆, b₆, K₆⟩ | hd⟩ := prodCall hP hpre c₅ (hr₄.trans hr₅)
    (b8000561c_pc h₅) (o := s.getReg .x2 - 400) (by rw [b8000561c_x10 h₅, c₄.x2]; rv_eval [])
    (Or.inl (by addr_omega [hsb])) (by addr_omega [hsb]) (Nat.le_refl _)
    (Or.inl (by addr_omega [hsb, hab]))
  swap
  · exact ⟨t₆, hr₆, Or.inr hd⟩
  rw [b8000561c_x11 h₅, b8000561c_x12 h₅, b8000561c_x13 h₅] at b₆
  have f₆ := K₆.2 _ _ (K₅.2 _ _ f₄ (Nat.le_refl _)) (by omega)
  obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80005634_spec
    (by rw [hpc₆, returnAddress_eq, b8000561c_x1 h₅]; decide) trivial
  have k₇ := b80005634_keeps h₇
  have hm₇ := b80005634_mem_same h₇
  have c₇ := c₆.same hpre hm₇ fun r hr ↦ k₇ r (mem_of_mem hr _)
  have K₇ := sameKeeps hpre c₆ hm₇
  have hn₇ : heapNext t₇ = heapNext t₆ := by simp only [heapNext, hm₇]
  have b₇ := K₇.1 _ _ _ _ b₆ (by omega) (Or.inl (by addr_omega [hsb])) (Or.inr (Or.inl rfl))
  have f₇ := K₇.2 _ _ f₆ (by omega)
  obtain ⟨t₈, hr₈, ⟨hpc₈, hp₈, c₈, f₈⟩ | hd⟩ := memColsCall hK hpre c₇ (hr₆.trans hr₇)
    (b80005634_pc h₇) f₇ (by omega) b₇ (by rw [b80005634_x10 h₇, c₆.x2]; rv_eval [])
    (by rw [b80005634_x11 h₇, c₆.x2]; rv_eval []) (b80005634_x14 h₇) (Or.inr (b80005634_x13 h₇))
  swap
  · exact ⟨t₈, hr₈, Or.inr hd⟩
  rw [b80005634_x12 h₇, b80005634_x13 h₇, cols_vb c₇.rodata] at f₈
  -- the branch
  obtain ⟨t₉, hr₉, h₉⟩ := Sym.BlockSpec.reaches b80005654_spec
    (by rw [hpc₈, returnAddress_eq, b80005634_x1 h₇]; decide) trivial
  have k₉ := b80005654_keeps h₉
  have hm₉ := b80005654_mem_same h₉
  have c₉ := c₈.same hpre hm₉ fun r hr ↦ k₉ r (mem_of_mem hr _)
  have K₉ := sameKeeps hpre c₈ hm₉
  have x9 : t₈.getReg .x9 = s.getReg .x12 := by
    rw [hp₈.reg .x9, k₇ .x9 (by decide), hp₆.reg .x9, k₅ .x9 (by decide), hp₄.reg .x9,
      k₃ .x9 (by decide), hp₂.reg .x9, k₁ .x9 (by decide), A.x9]
  have hn₉ : heapNext t₉ = heapNext t₈ := by simp only [heapNext, hm₉]
  refine ⟨t₉, hr₈.trans hr₉, Or.inl {
    toInv := c₉
    pc := ?_
    fl := hn₉ ▸ K₉.2 _ _ f₈ (Nat.le_refl _) }⟩
  by_cases hz : s.getReg .x12 = 0
  · rw [b80005654_pc_taken h₉ (by rw [x9, hz])]; simp only [hz, ↓reduceIte]
  · rw [b80005654_pc_not_taken h₉ (by rw [x9]; exact hz)]; simp only [hz, ↓reduceIte]

end Rv64Verifier.Layout.Arith
