import Rv64Verifier.Proofs.Layout.MemoryColsTail

/-!
# `Flushes::memory_cols` meets its contract

The limbs, by the number of columns (`MemoryColsBase.lean`): `head` builds limb 0 from `columns[0]`;
with one column, `pathA` and `fromDa0` build two zeros; with two, `pathB` builds limb 1 from
`columns[1]` and `fromDa0` a zero; with three, `pathB` and `pathC` the last two from the columns.
`MemoryColsTail.lean` ends each.
-/

namespace Rv64Verifier.Layout.MemoryCols
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F20 Rv64Verifier.Model.LayoutMirror

/-- Column `i` as the entry holds it. -/
def cAt (s : MachineState) (i : Nat) : Nat :=
  (s.getMem (s.getReg .x13 + BitVec.ofNat 64 (8 * i))).toNat

/-- The prologue, `term`, `col(sp' + 144, columns[0], 0)` and its move to `sp' + 72`. -/
theorem head (hT : TermSpec) (hC : ColSpec) {s : MachineState} (hpc : s.pc = 0x80005c64)
    (hpre : MemoryColsPre s) :
    ∃ t, Reaches Image.code s t ∧ ((Inv s t ∧
      Built s t (s.getReg .x2 - 168) (colRust (cAt s 0) 0) ∧
      ((s.getReg .x14).toNat ≤ 1 → t.pc = 0x80005d68) ∧
      (1 < (s.getReg .x14).toNat → t.pc = 0x80005ce4)) ∨ Dead Image.code t) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hlen := hpre.len
  have hcb := ValidMemRange.bounds hpre.columns (by omega)
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80005c64_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hpre.stack.valid [hsb])
  have k₁ := b80005c64_keeps h₁
  have hm₁ := b80005c64_frame h₁ (by addr_omega [hsb])
  have hn₁ : heapNext t₁ = heapNext s := by
    simp only [heapNext]; rw [hm₁ _ (by addr_omega [hnx, hsb])]
  have c₁ : Inv s t₁ := {
    x2 := b80005c64_x2 h₁
    x8 := b80005c64_x8 h₁
    x9 := b80005c64_x9 h₁
    x18 := b80005c64_x18 h₁
    x19 := b80005c64_x19 h₁
    x20 := b80005c64_x20 h₁
    regs := fun r hr ↦ k₁ r (mem_of_mem hr _)
    ra := b80005c64_m_x2_n8 h₁
    s0 := b80005c64_m_x2_n16 h₁
    s1 := b80005c64_m_x2_n24 h₁
    s2 := b80005c64_m_x2_n32 h₁
    s3 := b80005c64_m_x2_n40 h₁
    s4 := b80005c64_m_x2_n48 h₁
    heap := ⟨hn₁ ▸ hpre.heap.lo, hn₁ ▸ hpre.heap.hi⟩
    mono := hn₁.ge
    rodata := hpre.rodata.frame hm₁ (by addr_omega [hsb, hro])
    frame := hm₁.dframe.mono fun x hx ↦ Or.inl (by addr_omega [hx, hsb]) }
  obtain ⟨v₁, hrv₁, ⟨hpcv₁, cv₁, -, -⟩ | hd⟩ := termCall hT hpre c₁ hr₁ (b80005c64_pc h₁)
    (b80005c64_x10 h₁) (b80005c64_x11 h₁) (b80005c64_x12 h₁) (b80005c64_m_x2_n240 h₁)
  swap
  · exact ⟨v₁, hrv₁, Or.inr hd⟩
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80005cb0_spec
    (by rw [hpcv₁, returnAddress_eq, b80005c64_x1 h₁]; decide) (by
      rv_eval [cv₁.x19]
      valid_access hpre.columns [hcb, hlen])
  have x11₂ : t₂.getReg .x11 = s.getMem (s.getReg .x13 + BitVec.ofNat 64 (8 * 0)) := by
    rw [b80005cb0_x11 h₂, cv₁.x19, ← cv₁.column hpre (i := 0) (by omega)]
    simp
  obtain ⟨v₂, hrv₂, ⟨hpcv₂, cv₂, bv₂, -⟩ | hd⟩ := colBlock hC hpre cv₁ (hrv₁.trans hr₂)
    (b80005cb0_mem_same h₂) (fun r hr ↦ b80005cb0_keeps h₂ r (mem_of_mem hr _))
    (b80005cb0_pc h₂) (b80005cb0_x10 h₂) (b80005cb0_x12 h₂)
  swap
  · exact ⟨v₂, hrv₂, Or.inr hd⟩
  rw [x11₂] at bv₂
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80005cc4_spec
    (by rw [hpcv₂, returnAddress_eq, b80005cb0_x1 h₂]; decide) (by
      rv_eval [cv₂.x2]
      and_intros <;> valid_access hpre.stack.valid [hsb])
  have hm₃ := b80005cc4_frame h₃ (by addr_omega [hsb, cv₂.x2])
  rw [cv₂.x2] at hm₃
  have k₃ := b80005cc4_keeps h₃
  refine ⟨t₃, hrv₂.trans hr₃, Or.inl ⟨cv₂.block hpre hm₃ (by addr_omega [hsb])
    (by addr_omega [hsb]) fun r hr ↦ k₃ r (mem_of_mem hr _), bv₂.blockMove hpre cv₂ hm₃
    (by addr_omega [hsb]) (by addr_omega [hsb])
    (by have := b80005cc4_m_x2_72 h₃; rw [cv₂.x2] at this; rv_eval [] at this ⊢; exact this)
    (by have := b80005cc4_m_x2_80 h₃; rw [cv₂.x2] at this; rv_eval [] at this ⊢; exact this)
    (by have := b80005cc4_m_x2_88 h₃; rw [cv₂.x2] at this; rv_eval [] at this ⊢; exact this),
    fun h ↦ ?_, fun h ↦ ?_⟩⟩
  · apply b80005cc4_pc_taken h₃; rw [cv₂.x20]; exact h
  · apply b80005cc4_pc_not_taken h₃; rw [cv₂.x20]; exact h

/-- One column: limb 1 is a zero, built and moved to `sp' + 96`. -/
theorem pathA (hT : TermSpec) {s t : MachineState} (hpre : MemoryColsPre s) (c : Inv s t)
    (hr : Reaches Image.code s t) (hpc : t.pc = 0x80005d68) {f0 : FormRust}
    (b0 : Built s t (s.getReg .x2 - 168) f0) :
    ∃ u, Reaches Image.code s u ∧ ((Inv s u ∧ u.pc = 0x80005da0 ∧
      Built s u (s.getReg .x2 - 168) f0 ∧ Built s u (s.getReg .x2 - 144) (constantRust 0)) ∨
      Dead Image.code u) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80005d68_spec hpc (by
    rv_eval [c.x2]
    valid_access hpre.stack.valid [hsb])
  obtain ⟨v, hrv, ⟨hpcv, cv, bz, kv⟩ | hd⟩ := zeroTerm hT hpre c (hr.trans hr₁)
    (b80005d68_frame h₁ (by addr_omega [hsb, c.x2]))
    (fun r hr ↦ b80005d68_keeps h₁ r (mem_of_mem hr _)) (b80005d68_pc h₁) (b80005d68_x10 h₁)
    (b80005d68_x11 h₁) (b80005d68_x12 h₁) (b80005d68_m_x2_0 h₁)
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have b0v := kv _ _ b0 (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb])
  obtain ⟨u, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80005d84_spec
    (by rw [hpcv, returnAddress_eq, b80005d68_x1 h₁]; decide) (by
      rv_eval [cv.x2]
      and_intros <;> valid_access hpre.stack.valid [hsb])
  have hm₂ := b80005d84_frame h₂ (by addr_omega [hsb, cv.x2])
  rw [cv.x2] at hm₂
  have k₂ := b80005d84_keeps h₂
  refine ⟨u, hrv.trans hr₂, Or.inl ⟨cv.block hpre hm₂ (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ k₂ r (mem_of_mem hr _), b80005d84_pc h₂,
    b0v.block hpre cv hm₂ (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb])
      (by addr_omega [hsb]),
    bz.blockMove hpre cv hm₂ (by addr_omega [hsb]) (by addr_omega [hsb])
      (by have := b80005d84_m_x2_96 h₂; rw [cv.x2] at this; rv_eval [] at this ⊢; exact this)
      (by have := b80005d84_m_x2_104 h₂; rw [cv.x2] at this; rv_eval [] at this ⊢; exact this)
      (by have := b80005d84_m_x2_112 h₂; rw [cv.x2] at this; rv_eval [] at this ⊢; exact this)⟩⟩

/-- Limb 2 is a zero, built and moved to `sp' + 144`. -/
theorem fromDa0 (hT : TermSpec) {s t : MachineState} (hpre : MemoryColsPre s) (c : Inv s t)
    (hr : Reaches Image.code s t) (hpc : t.pc = 0x80005da0) {f0 f1 : FormRust}
    (b0 : Built s t (s.getReg .x2 - 168) f0) (b1 : Built s t (s.getReg .x2 - 144) f1) :
    ∃ u, Reaches Image.code s u ∧ ((Inv s u ∧ u.pc = 0x80005dd4 ∧
      Built s u (s.getReg .x2 - 168) f0 ∧ Built s u (s.getReg .x2 - 144) f1 ∧
      Built s u (s.getReg .x2 - 96) (constantRust 0)) ∨ Dead Image.code u) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80005da0_spec hpc (by
    rv_eval [c.x2]
    valid_access hpre.stack.valid [hsb])
  obtain ⟨v, hrv, ⟨hpcv, cv, bz, kv⟩ | hd⟩ := zeroTerm hT hpre c (hr.trans hr₁)
    (b80005da0_frame h₁ (by addr_omega [hsb, c.x2]))
    (fun r hr ↦ b80005da0_keeps h₁ r (mem_of_mem hr _)) (b80005da0_pc h₁) (b80005da0_x10 h₁)
    (b80005da0_x11 h₁) (b80005da0_x12 h₁) (b80005da0_m_x2_0 h₁)
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have b0v := kv _ _ b0 (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb])
  have b1v := kv _ _ b1 (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb])
  obtain ⟨u, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80005dbc_spec
    (by rw [hpcv, returnAddress_eq, b80005da0_x1 h₁]; decide) (by
      rv_eval [cv.x2]
      and_intros <;> valid_access hpre.stack.valid [hsb])
  have hm₂ := b80005dbc_frame h₂ (by addr_omega [hsb, cv.x2])
  rw [cv.x2] at hm₂
  have k₂ := b80005dbc_keeps h₂
  refine ⟨u, hrv.trans hr₂, Or.inl ⟨cv.block hpre hm₂ (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ k₂ r (mem_of_mem hr _), b80005dbc_pc h₂,
    b0v.block hpre cv hm₂ (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb])
      (by addr_omega [hsb]),
    b1v.block hpre cv hm₂ (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb])
      (by addr_omega [hsb]),
    bz.blockMove hpre cv hm₂ (by addr_omega [hsb]) (by addr_omega [hsb])
      (by have := b80005dbc_m_x2_144 h₂; rw [cv.x2] at this; rv_eval [] at this ⊢; exact this)
      (by have := b80005dbc_m_x2_152 h₂; rw [cv.x2] at this; rv_eval [] at this ⊢; exact this)
      (by have := b80005dbc_m_x2_160 h₂; rw [cv.x2] at this; rv_eval [] at this ⊢; exact this)⟩⟩

/-- Two columns or more: limb 1 from `columns[1]`, moved to `sp' + 96`. -/
theorem pathB (hT : TermSpec) (hC : ColSpec) {s t : MachineState} (hpre : MemoryColsPre s)
    (c : Inv s t) (hr : Reaches Image.code s t) (hpc : t.pc = 0x80005ce4)
    (hlen : 1 < (s.getReg .x14).toNat) {f0 : FormRust}
    (b0 : Built s t (s.getReg .x2 - 168) f0) :
    ∃ u, Reaches Image.code s u ∧ ((Inv s u ∧ Built s u (s.getReg .x2 - 168) f0 ∧
      Built s u (s.getReg .x2 - 144) (colRust (cAt s 1) 0) ∧
      (s.getReg .x14 ≠ 3 → u.pc = 0x80005da0) ∧ (s.getReg .x14 = 3 → u.pc = 0x80005d34)) ∨
      Dead Image.code u) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hcb := ValidMemRange.bounds hpre.columns (by omega)
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80005ce4_spec hpc (by
    rv_eval [c.x2]
    valid_access hpre.stack.valid [hsb])
  obtain ⟨v, hrv, ⟨hpcv, cv, -, kv⟩ | hd⟩ := zeroTerm hT hpre c (hr.trans hr₁)
    (b80005ce4_frame h₁ (by addr_omega [hsb, c.x2]))
    (fun r hr ↦ b80005ce4_keeps h₁ r (mem_of_mem hr _)) (b80005ce4_pc h₁) (b80005ce4_x10 h₁)
    (b80005ce4_x11 h₁) (b80005ce4_x12 h₁) (b80005ce4_m_x2_0 h₁)
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have b0v := kv _ _ b0 (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb])
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80005d00_spec
    (by rw [hpcv, returnAddress_eq, b80005ce4_x1 h₁]; decide) (by
      rv_eval [cv.x19]
      valid_access hpre.columns [hcb, hlen])
  have x11₂ : t₂.getReg .x11 = s.getMem (s.getReg .x13 + BitVec.ofNat 64 (8 * 1)) := by
    rw [b80005d00_x11 h₂, cv.x19, ← cv.column hpre (i := 1) hlen]
    rfl
  obtain ⟨v₂, hrv₂, ⟨hpcv₂, cv₂, bv₂, kv₂⟩ | hd⟩ := colBlock hC hpre cv (hrv.trans hr₂)
    (b80005d00_mem_same h₂) (fun r hr ↦ b80005d00_keeps h₂ r (mem_of_mem hr _))
    (b80005d00_pc h₂) (b80005d00_x10 h₂) (b80005d00_x12 h₂)
  swap
  · exact ⟨v₂, hrv₂, Or.inr hd⟩
  rw [x11₂] at bv₂
  have b0₂ := kv₂ _ _ b0v (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb])
  obtain ⟨u, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80005d14_spec
    (by rw [hpcv₂, returnAddress_eq, b80005d00_x1 h₂]; decide) (by
      rv_eval [cv₂.x2]
      and_intros <;> valid_access hpre.stack.valid [hsb])
  have hm₃ := b80005d14_frame h₃ (by addr_omega [hsb, cv₂.x2])
  rw [cv₂.x2] at hm₃
  have k₃ := b80005d14_keeps h₃
  refine ⟨u, hrv₂.trans hr₃, Or.inl ⟨cv₂.block hpre hm₃ (by addr_omega [hsb])
    (by addr_omega [hsb]) fun r hr ↦ k₃ r (mem_of_mem hr _),
    b0₂.block hpre cv₂ hm₃ (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb])
      (by addr_omega [hsb]),
    bv₂.blockMove hpre cv₂ hm₃ (by addr_omega [hsb]) (by addr_omega [hsb])
      (by have := b80005d14_m_x2_96 h₃; rw [cv₂.x2] at this; rv_eval [] at this ⊢; exact this)
      (by have := b80005d14_m_x2_104 h₃; rw [cv₂.x2] at this; rv_eval [] at this ⊢; exact this)
      (by have := b80005d14_m_x2_112 h₃; rw [cv₂.x2] at this; rv_eval [] at this ⊢; exact this),
    fun h ↦ ?_, fun h ↦ ?_⟩⟩
  · apply b80005d14_pc_taken h₃; rw [cv₂.x20]; exact h
  · apply b80005d14_pc_not_taken h₃; rw [cv₂.x20]; exact h

/-- Three columns: limb 2 from `columns[2]`, left at `sp' + 144`. -/
theorem pathC (hT : TermSpec) (hC : ColSpec) {s t : MachineState} (hpre : MemoryColsPre s)
    (c : Inv s t) (hr : Reaches Image.code s t) (hpc : t.pc = 0x80005d34)
    (hlen : (s.getReg .x14).toNat = 3) {f0 f1 : FormRust}
    (b0 : Built s t (s.getReg .x2 - 168) f0) (b1 : Built s t (s.getReg .x2 - 144) f1) :
    ∃ u, Reaches Image.code s u ∧ ((Inv s u ∧ u.pc = 0x80005dd4 ∧
      Built s u (s.getReg .x2 - 168) f0 ∧ Built s u (s.getReg .x2 - 144) f1 ∧
      Built s u (s.getReg .x2 - 96) (colRust (cAt s 2) 0)) ∨ Dead Image.code u) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hcb := ValidMemRange.bounds hpre.columns (by omega)
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80005d34_spec hpc (by
    rv_eval [c.x2]
    valid_access hpre.stack.valid [hsb])
  obtain ⟨v, hrv, ⟨hpcv, cv, -, kv⟩ | hd⟩ := zeroTerm hT hpre c (hr.trans hr₁)
    (b80005d34_frame h₁ (by addr_omega [hsb, c.x2]))
    (fun r hr ↦ b80005d34_keeps h₁ r (mem_of_mem hr _)) (b80005d34_pc h₁) (b80005d34_x10 h₁)
    (b80005d34_x11 h₁) (b80005d34_x12 h₁) (b80005d34_m_x2_0 h₁)
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have b0v := kv _ _ b0 (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb])
  have b1v := kv _ _ b1 (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb])
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80005d50_spec
    (by rw [hpcv, returnAddress_eq, b80005d34_x1 h₁]; decide) (by
      rv_eval [cv.x19]
      valid_access hpre.columns [hcb, hlen])
  have x11₂ : t₂.getReg .x11 = s.getMem (s.getReg .x13 + BitVec.ofNat 64 (8 * 2)) := by
    rw [b80005d50_x11 h₂, cv.x19, ← cv.column hpre (i := 2) (by omega)]
    rfl
  obtain ⟨v₂, hrv₂, ⟨hpcv₂, cv₂, bv₂, kv₂⟩ | hd⟩ := colBlock hC hpre cv (hrv.trans hr₂)
    (b80005d50_mem_same h₂) (fun r hr ↦ b80005d50_keeps h₂ r (mem_of_mem hr _))
    (b80005d50_pc h₂) (b80005d50_x10 h₂) (b80005d50_x12 h₂)
  swap
  · exact ⟨v₂, hrv₂, Or.inr hd⟩
  rw [x11₂] at bv₂
  have b0₂ := kv₂ _ _ b0v (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb])
  have b1₂ := kv₂ _ _ b1v (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb])
  obtain ⟨u, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80005d64_spec
    (by rw [hpcv₂, returnAddress_eq, b80005d50_x1 h₂]; decide) trivial
  have hm₃ := b80005d64_mem_same h₃
  have k₃ := b80005d64_keeps h₃
  have hheap := cv₂.heap
  refine ⟨u, hrv₂.trans hr₃, Or.inl ⟨cv₂.same hpre hm₃ fun r hr ↦ k₃ r (mem_of_mem hr _),
    b80005d64_pc h₃, b0₂.same hheap hm₃ (by addr_omega [hsb]),
    b1₂.same hheap hm₃ (by addr_omega [hsb]), bv₂.same hheap hm₃ (by addr_omega [hsb])⟩⟩

/-- The three limbs at `0x80005dd4`, the rest of the code. -/
theorem close (hM : MemcpySpec 0x800126e4) (hK : MemorySpec) {s u : MachineState}
    (hpre : MemoryColsPre s) (c : Inv s u) (hr : Reaches Image.code s u) (hpc : u.pc = 0x80005dd4)
    {f0 f1 f2 : FormRust} (b0 : Built s u (s.getReg .x2 - 168) f0)
    (b1 : Built s u (s.getReg .x2 - 144) f1) (b2 : Built s u (s.getReg .x2 - 96) f2)
    (hv : ∀ (F : FlushesRust) (A : FormRust) (n : Nat), F.memoryCols A n (colsAt s (s.getReg .x13) (s.getReg .x14).toNat) =
      F.memory A n [f0, f1, f2]) :
    ∃ t, Reaches Image.code s t ∧ ((t.pc = returnAddress s ∧ Preserves s t ∧
      (GrowFlushes s t (s.getReg .x10) memoryColsStack (fun _ ↦ False) ∧
        flushesOf t (s.getReg .x10) = (flushesOf s (s.getReg .x10)).memoryCols
          (formOf s (s.getReg .x11)) (s.getReg .x12).toNat
          (colsAt s (s.getReg .x13) (s.getReg .x14).toNat))) ∨ Dead Image.code t) := by
  obtain ⟨w, hrw, A | hd⟩ := toMemory hM hpre c hr hpc b0 b1 b2
  swap
  · exact ⟨w, hrw, Or.inr hd⟩
  obtain ⟨t, hrt, ⟨h1, h2, h3, h4⟩ | hd⟩ := finish hK hpre A
  · exact ⟨t, hrw.trans hrt, Or.inl ⟨h1, h2, h3, h4.trans (hv _ _ _).symm⟩⟩
  · exact ⟨t, hrw.trans hrt, Or.inr hd⟩

/-- **`Flushes::memory_cols` meets its contract**, given `Form::term`'s, `col`'s, `memcpy`'s and
`Flushes::memory`'s. -/
theorem memory_cols_spec (hT : TermSpec) (hC : ColSpec) (hM : MemcpySpec 0x800126e4)
    (hK : MemorySpec) : MemoryColsSpec := by
  intro s hpc hpre
  have hlen := hpre.len
  obtain ⟨t, hr, ⟨c, b0, hpa, hpb⟩ | hd⟩ := head hT hC hpc hpre
  swap
  · exact ⟨t, hr, Or.inr hd⟩
  by_cases h1 : (s.getReg .x14).toNat ≤ 1
  · have e : (s.getReg .x14).toNat = 1 := by omega
    obtain ⟨u, hru, ⟨cu, hpcu, b0u, b1u⟩ | hd⟩ := pathA hT hpre c hr (hpa h1) b0
    swap
    · exact ⟨u, hru, Or.inr hd⟩
    obtain ⟨w, hrw, ⟨cw, hpcw, b0w, b1w, b2w⟩ | hd⟩ := fromDa0 hT hpre cu hru hpcu b0u b1u
    swap
    · exact ⟨w, hrw, Or.inr hd⟩
    exact close hM hK hpre cw hrw hpcw b0w b1w b2w fun F A n ↦ by rw [e]; rfl
  · obtain ⟨u, hru, ⟨cu, b0u, b1u, hp2, hp3⟩ | hd⟩ := pathB hT hC hpre c hr (hpb (by omega)) (by omega) b0
    swap
    · exact ⟨u, hru, Or.inr hd⟩
    by_cases h3 : s.getReg .x14 = 3
    · have e : (s.getReg .x14).toNat = 3 := by rw [h3]; rfl
      obtain ⟨w, hrw, ⟨cw, hpcw, b0w, b1w, b2w⟩ | hd⟩ := pathC hT hC hpre cu hru (hp3 h3) e b0u b1u
      swap
      · exact ⟨w, hrw, Or.inr hd⟩
      exact close hM hK hpre cw hrw hpcw b0w b1w b2w fun F A n ↦ by rw [e]; rfl
    · have e : (s.getReg .x14).toNat = 2 := by
        have : (s.getReg .x14).toNat ≠ 3 := fun h ↦ h3 (BitVec.eq_of_toNat_eq h)
        omega
      obtain ⟨w, hrw, ⟨cw, hpcw, b0w, b1w, b2w⟩ | hd⟩ := fromDa0 hT hpre cu hru (hp2 h3) b0u b1u
      swap
      · exact ⟨w, hrw, Or.inr hd⟩
      exact close hM hK hpre cw hrw hpcw b0w b1w b2w fun F A n ↦ by rw [e]; rfl

end Rv64Verifier.Layout.MemoryCols
