import Rv64Verifier.Proofs.Layout.BytecodeBase
import Rv64Verifier.Proofs.Layout.Col

/-!
# `Flushes::bytecode`: the opcode's form and the suffix's `Vec`

`head`: `alloc(8, 24)`, `pow` and `term(B, One, GEN^opcode)`; `start`: `try_allocate_in` and the
first `spec_extend`, from `B`.
-/

namespace Rv64Verifier.Layout.Bytecode
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F11 Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Layout.MemoryCols (Built)

/-- At `try_allocate_in`: the opcode's form at `B`. -/
structure AtTry (s t : MachineState) (B : Word) : Prop extends Inv s t where
  pc : t.pc = 0x80004c14
  x18 : t.getReg .x18 = B
  x19 : t.getReg .x19 = s.getReg .x13
  x20 : t.getReg .x20 = s.getReg .x12
  al : B.toNat % 8 = 0
  lo : heapNext s ≤ B.toNat
  hi : B.toNat + 24 ≤ heapNext t
  b : Built s t B (constantRust (gpowRust (s.getReg .x12).toNat))

theorem head (hA : AllocSpec) (hP : PowSpec) (hT : TermSpec) {s : MachineState}
    (hpc : s.pc = 0x80004b94) (hpre : BytecodePre s) :
    ∃ t B, Reaches Image.code s t ∧ (AtTry s t B ∨ Dead Image.code t) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hheap := hpre.heap
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80004b94_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hpre.stack.valid [hsb])
  have k₁ := b80004b94_keeps h₁
  have hm₁ := b80004b94_frame h₁ (by addr_omega [hsb])
  have hn₁ : heapNext t₁ = heapNext s := by
    simp only [heapNext]; rw [hm₁ _ (by addr_omega [hnx, hsb])]
  have c₁ : Inv s t₁ := {
    x2 := b80004b94_x2 h₁
    x8 := b80004b94_x8 h₁
    x9 := b80004b94_x9 h₁
    regs := fun r hr ↦ k₁ r (mem_of_mem hr _)
    ra := b80004b94_m_x2_n8 h₁
    s0 := b80004b94_m_x2_n16 h₁
    s1 := b80004b94_m_x2_n24 h₁
    s2 := b80004b94_m_x2_n32 h₁
    s3 := b80004b94_m_x2_n40 h₁
    s4 := b80004b94_m_x2_n48 h₁
    heap := ⟨hn₁ ▸ hheap.lo, hn₁ ▸ hheap.hi⟩
    mono := hn₁.ge
    rodata := hpre.rodata.frame hm₁ (by addr_omega [hsb, hro])
    frame := hm₁.dframe.mono fun x hx ↦ Or.inl (by addr_omega [hx, hsb]) }
  -- `alloc(8, 24)`
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hdead⟩ := hA.call hr₁ (b80004b94_pc h₁)
    ⟨c₁.heap, by rw [b80004b94_x10 h₁]; decide⟩
  swap
  · exact ⟨t₂, 0, hr₂, Or.inr hdead⟩
  obtain ⟨B, hB⟩ : ∃ B, t₂.getReg .x10 = B := ⟨_, rfl⟩
  have hBal : B.toNat % 8 = 0 := by rw [← hB]; simpa [b80004b94_x10 h₁] using hpost₂.aligned
  have hBlo : heapNext s ≤ B.toNat := by rw [← hB, ← hn₁]; exact hpost₂.above
  have hBn : heapNext t₂ = B.toNat + 24 := by rw [hpost₂.next, hB, b80004b94_x11 h₁]; rfl
  have hh₂ := hpost₂.heap.hi
  have hlo₀ := hheap.lo
  have c₂ : Inv s t₂ := c₁.step hpre (W := fun x ↦ Within x nextAddr 8)
    (fun a ha _ ↦ hpost₂.mem a fun h ↦ ha a (by rw [h]; addr_omega []) (by rw [h]; addr_omega []))
    (fun x h ↦ Or.inr (Or.inl h)) hpost₂.heap (by omega) (keepRegs_of hpres₂)
  -- the null check
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80004bd0_spec
    (by rw [hpc₂, returnAddress_eq, b80004b94_x1 h₁]; decide) trivial
  have hB0 : t₂.getReg .x10 ≠ 0 := by
    rw [hB]; intro h; rw [h] at hBlo; simp only [heapStart] at hlo₀; simp at hBlo; omega
  have c₃ := (c₂.same hpre (b80004bd0_mem_same h₃) fun r hr ↦ b80004bd0_keeps h₃ r (mem_of_mem hr _)).1
  have x10₃ : t₃.getReg .x10 = B := (b80004bd0_keeps h₃ .x10 (by decide)).trans hB
  -- `GEN` at `sp'`, and `pow(sp' + 72, sp', opcode)`
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80004bd4_spec (b80004bd0_pc_not_taken h₃ hB0) (by
    rv_eval [c₃.x2]
    and_intros <;> valid_access hpre.stack.valid [hsb])
  have hm₄ := b80004bd4_frame h₄ (by addr_omega [hsb, c₃.x2])
  rw [c₃.x2] at hm₄
  have k₄ := b80004bd4_keeps h₄
  obtain ⟨c₄, -, -, hn₄⟩ := c₃.block hpre hm₄ (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ k₄ r (mem_of_mem hr _)
  have x2₄ := c₄.x2
  have hgen : eAt t₄ (s.getReg .x2 - 144) = genRust := by
    have g0 := b80004bd4_m_x2_0 h₄
    have g8 := b80004bd4_m_x2_8 h₄
    have g16 := b80004bd4_m_x2_16 h₄
    rw [c₃.x2] at g0 g8 g16
    exact Col.eAt_gen g0 g8 g16
  have hpow : PowPre t₄ := {
    out := by rw [b80004bd4_x10 h₄, c₃.x2]; valid_sub hpre.stack.valid [hsb]
    base := by rw [b80004bd4_x11 h₄, c₃.x2]; valid_sub hpre.stack.valid [hsb]
    stack := (hpre.stack.inner (k := 144) x2₄ (by decide) (by decide) (by decide) (by decide)
      (by decide)).toStackOk
    pool := poolOk_of_rodata c₄.rodata (by addr_omega [hsb, hro, x2₄])
    outBase := by rw [b80004bd4_x10 h₄, b80004bd4_x11 h₄, c₃.x2]; addr_omega [hsb]
    outStack := by rw [b80004bd4_x10 h₄, c₃.x2]; addr_omega [hsb, x2₄]
    baseStack := by rw [b80004bd4_x11 h₄, c₃.x2]; addr_omega [hsb, x2₄]
    basePool := by rw [b80004bd4_x11 h₄, c₃.x2]; addr_omega [hsb, hro] }
  obtain ⟨t₅, hr₅, ⟨hpc₅, hpres₅, hpost₅⟩ | hdead⟩ := hP.call hr₄ (b80004bd4_pc h₄) hpow
  swap
  · exact ⟨t₅, 0, hr₂.trans (hr₃.trans hr₅), Or.inr hdead⟩
  have hf₅ := dframe_of_three hpost₅.frame
  rw [b80004bd4_x10 h₄, b80004bd4_x11 h₄, c₃.x2, show stackLo t₄ powStack = s.getReg .x2 - 1248 by
    simp only [stackLo, x2₄, powStack, Contracts.mulStack]; rv_eval [Nat.reduceAdd]] at hf₅
  have hn₅ : heapNext t₅ = heapNext t₄ := by
    simp only [heapNext]
    rw [hf₅.getMem_of (fun x hx h ↦ by rcases h with h | h | h <;> addr_omega [hx, h, hnx, hsb])
      (by decide)]
  have c₅ := c₄.step hpre hf₅ (fun x h ↦ Or.inl (by rcases h with h | h | h <;> addr_omega [h, hsb]))
    ⟨hn₅ ▸ c₄.heap.lo, hn₅ ▸ c₄.heap.hi⟩ hn₅.ge (keepRegs_of hpres₅)
  have hv₅ : eAt t₅ (s.getReg .x2 - 72) = genRust ^ (s.getReg .x12).toNat := by
    have hv := hpost₅.value
    rw [b80004bd4_x10 h₄, b80004bd4_x11 h₄, b80004bd4_x12 h₄, c₃.x2, hgen,
      show s.getReg .x2 - 144 + 72 = s.getReg .x2 - 72 by rv_eval []] at hv
    rw [hv, b80004bd0_keeps h₃ .x20 (by decide), hpres₂.reg .x20, b80004b94_x20 h₁]
  -- the tag at `sp'`, and `term(B, One, sp' + 72)`
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b80004bfc_spec
    (by rw [hpc₅, returnAddress_eq, b80004bd4_x1 h₄]; decide) (by
      rv_eval [c₅.x2]
      valid_access hpre.stack.valid [hsb])
  have hm₆ := b80004bfc_frame h₆ (by addr_omega [hsb, c₅.x2])
  rw [c₅.x2] at hm₆
  have k₆ := b80004bfc_keeps h₆
  obtain ⟨c₆, -, -, hn₆⟩ := c₅.block hpre hm₆ (by addr_omega [hsb]) (by addr_omega [hsb])
    fun r hr ↦ k₆ r (mem_of_mem hr _)
  have hv₆ : eAt t₆ (s.getReg .x2 - 72) = genRust ^ (s.getReg .x12).toNat := by
    rw [hm₆.eAt (by addr_omega [hsb]) (by addr_omega [hsb]), hv₅]
  have tag₆ : t₆.getMem (s.getReg .x2 - 144) = 0 := by
    have := b80004bfc_m_x2_0 h₆; rw [c₅.x2] at this; exact this
  have x10₆ : t₆.getReg .x10 = B := by
    rw [b80004bfc_x10 h₆, hpres₅.reg .x18, b80004bd4_x18 h₄, x10₃]
  have x11₆ : t₆.getReg .x11 = s.getReg .x2 - 144 := by rw [b80004bfc_x11 h₆, c₅.x2]
  have x12₆ : t₆.getReg .x12 = s.getReg .x2 - 72 := by rw [b80004bfc_x12 h₆, c₅.x2]; rv_eval []
  have hh₆ : B.toNat + 24 ≤ heapNext t₆ := by
    rw [hn₆, hn₅, hn₄, show heapNext t₃ = heapNext t₂ by simp only [heapNext, b80004bd0_mem_same h₃]]
    omega
  have hhi₆ := c₆.heap.hi
  have x2₆ := c₆.x2
  have hterm : TermPre t₆ := {
    heap := c₆.heap
    stack := hpre.stack.inner (k := 144) x2₆ (by decide) (by decide) (by decide) (by decide)
      (by decide)
    out := by
      rw [x10₆]; exact validMemRange_of hBal (Or.inl ⟨by simp only [heapStart] at hlo₀; omega,
        by simp only [heapEnd] at hhi₆; omega⟩)
    mono := by rw [x11₆]; valid_sub hpre.stack.valid [hsb]
    coeff := by rw [x12₆]; valid_sub hpre.stack.valid [hsb]
    monoOk := by rw [x11₆]; simp only [MonoOk, tag₆]; decide
    outFree := by rw [x10₆]; addr_omega [hh₆, hhi₆]
    monoNext := by rw [x11₆]; addr_omega [hsb, hnx]
    coeffNext := by rw [x12₆]; addr_omega [hsb, hnx]
    outStack := by rw [x10₆]; addr_omega [hsb, hab, x2₆, hh₆, hhi₆]
    monoStack := by rw [x11₆]; addr_omega [hsb, x2₆]
    coeffStack := by rw [x12₆]; addr_omega [hsb, x2₆] }
  obtain ⟨t₇, hr₇, ⟨hpc₇, hpres₇, hnew₇, hval₇⟩ | hdead⟩ := hT.call hr₆ (b80004bfc_pc h₆) hterm
  swap
  · exact ⟨t₇, 0, hr₂.trans (hr₃.trans (hr₅.trans hr₇)), Or.inr hdead⟩
  rw [x10₆] at hnew₇ hval₇
  rw [x11₆, x12₆] at hval₇
  have hm₆' := c₆.mono
  have hm₇ := hnew₇.mono
  have c₇ := c₆.step hpre hnew₇.frame (fun x h ↦ by
      rcases h with h | h | h | h
      · exact Or.inr (Or.inr ⟨by addr_omega [h, hBlo], by addr_omega [h, hh₆, hm₇]⟩)
      · exact Or.inl (by addr_omega [h, hsb, x2₆])
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨by simp only [Fresh] at h; omega, h.2⟩))
    hnew₇.heap hm₇ (keepRegs_of hpres₇)
  refine ⟨t₇, B, hr₂.trans (hr₃.trans (hr₅.trans hr₇)), Or.inl {
    toInv := c₇
    pc := by rw [hpc₇, returnAddress_eq, b80004bfc_x1 h₆]; decide
    x18 := by rw [hpres₇.reg .x18, k₆ .x18 (by decide), hpres₅.reg .x18, b80004bd4_x18 h₄, x10₃]
    x19 := by
      rw [hpres₇.reg .x19, k₆ .x19 (by decide), hpres₅.reg .x19, k₄ .x19 (by decide),
        b80004bd0_keeps h₃ .x19 (by decide), hpres₂.reg .x19, b80004b94_x19 h₁]
    x20 := by
      rw [hpres₇.reg .x20, k₆ .x20 (by decide), hpres₅.reg .x20, k₄ .x20 (by decide),
        b80004bd0_keeps h₃ .x20 (by decide), hpres₂.reg .x20, b80004b94_x20 h₁]
    al := hBal
    lo := hBlo
    hi := by omega
    b := ⟨hnew₇.ok, by rw [hval₇, monoOf, tag₆, hv₆]; rfl, fun x hx ↦ by
      have hb := hnew₇.fresh
      simp only [NewBuf, formBuf, Within] at hb hx
      omega⟩ }⟩

end Rv64Verifier.Layout.Bytecode
