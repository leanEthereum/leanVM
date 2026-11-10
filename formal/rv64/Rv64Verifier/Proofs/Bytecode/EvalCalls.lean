import Rv64Verifier.Proofs.Bytecode.EvalCalled

/-!
# `Bytecode::evaluate`: the three calls

`eq_kernel` on the point's low part (`0x80010e8c`), on its high part (`0x80010eb4`), then
`vec![ZERO; 2048]` (`0x80010ec8`), each from its contract; `called_of` collects what holds after.
-/

namespace Rv64Verifier.Proofs.Bytecode.Eval
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Contracts
  Rv64Verifier.Blocks.F84
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

set_option maxHeartbeats 4000000 in
/-- The three calls. -/
theorem calls (hEK : EqKernelSpec) (hFE : FromElemSpec) {s t : MachineState}
    (hpre : EvaluatePre s) (hpc : t.pc = 0x8000cb38) (hc : PreCall s t) :
    ∃ u, Reaches Image.code t u ∧ (Dead Image.code u ∨
      (u.pc = 0x80010efc ∧ ∃ low high bk, Called s u low high bk)) := by
  have hsp := sp_bounds hpre.stack
  have hst := hpre.stack.valid
  have hstn := hpre.stack.next
  have hstr := hpre.stack.rodata
  have hpc' := hpre.pointClear
  have hn := hc.short
  have e2 : t.getReg .x2 = s.getReg .x2 - 1968 := hc.saved.sp
  have hnext : t.getMem nextAddr = s.getMem nextAddr := hc.mem _ (by addr_omega [hsp, hstn])
  have hmin : min (s.getReg .x13).toNat 14 ≤ (s.getReg .x13).toNat := Nat.min_le_left _ _
  have hsm := hpre.stack.mapped (by decide) (by decide)
  have hpr := hpre.pointRegion
  -- `eq_kernel` on the low part
  have pre₁ : EqKernelPre t := {
    heap := HeapOk.of_next hpre.heap hnext
    out := by rw [hc.x10]; addr_omega [hsp, hsm]
    point := by rw [hc.x11, hc.x12]; addr_omega [hpr, hmin]
    short := by rw [hc.x12]; omega
    stack := rtStack_inner hpre.stack e2 (by decide) (by decide) (by decide)
    outFree := by
      simp only [Outside, heapNext, hnext]; rw [hc.x10]; addr_omega [hsp, hstn]
    outStack := by simp only [stackLo, e2, hc.x10]; addr_omega [hsp]
    pointFree := by
      simp only [Outside, heapNext, hnext]; rw [hc.x11, hc.x12]; addr_omega [hpc', hmin]
    pointStack := by simp only [stackLo, e2]; rw [hc.x11, hc.x12]; addr_omega [hpc', hmin, hsp]
    pointOut := by rw [hc.x11, hc.x12, hc.x10]; addr_omega [hpc', hmin, hsp]
    rodata := RodataOk.of_dwords hpre.rodata fun a ha ↦ hc.mem a (by addr_omega [ha, hsp, hstr])
    outRodata := by rw [hc.x10]; addr_omega [hsp, hstr] }
  obtain ⟨t₁, hr₁, ⟨pc₁, pres₁, post₁⟩ | hd⟩ := hEK.call (Reaches.refl t) hpc pre₁
  swap
  · exact ⟨t₁, hr₁, Or.inl hd⟩
  have hx1 : returnAddress t = 0x80010eb4 := by rw [returnAddress_eq, hc.x1]; rfl
  rw [hx1] at pc₁
  have e2₁ : t₁.getReg .x2 = s.getReg .x2 - 1968 := (pres₁.reg .x2).trans e2
  have heap₁ := post₁.heap
  have mono₁ : heapNext s ≤ heapNext t₁ := by
    have := post₁.mono; simp only [heapNext, hnext] at this ⊢; exact this
  have hnn : (t.getReg .x12).toNat = min (s.getReg .x13).toNat 14 := hc.x12
  -- `eq_kernel` on the high part
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80010eb4_spec pc₁ trivial
  have k₂ := b80010eb4_keeps h₂
  have hm₂ := b80010eb4_mem_same h₂
  have e2₂ : t₂.getReg .x2 = s.getReg .x2 - 1968 := (k₂ .x2 (by decide)).trans e2₁
  have x10₂ : t₂.getReg .x10 = s.getReg .x2 - 1736 := by
    rw [b80010eb4_x10 h₂, e2₁]; rv_eval []
  have x11₂ : t₂.getReg .x11 = s.getReg .x12 + BitVec.ofNat 64 (24 * min (s.getReg .x13).toNat 14) :=
    by rw [b80010eb4_x11 h₂, pres₁.reg .x9, hc.x9]
  have x12₂ : (t₂.getReg .x12).toNat = (s.getReg .x13).toNat - min (s.getReg .x13).toNat 14 := by
    rw [b80010eb4_x12 h₂, pres₁.reg .x18, hc.x18]
  have hnext₂ : t₂.getMem nextAddr = t₁.getMem nextAddr := hm₂ _
  have hpb : (s.getReg .x13).toNat = 0 ∨
      (s.getReg .x12).toNat + 24 * (s.getReg .x13).toNat ≤ 0xc0000008 := by
    by_cases h : (s.getReg .x13).toNat = 0
    · exact Or.inl h
    · have := ValidMemRange.bounds hpre.point (by omega); right; omega
  have pre₂ : EqKernelPre t₂ := {
    heap := HeapOk.of_next heap₁ hnext₂
    out := by rw [x10₂]; addr_omega [hsp, hsm]
    point := by rw [x11₂, x12₂]; addr_omega [hpr, hmin]
    short := by rw [x12₂]; omega
    stack := rtStack_inner hpre.stack e2₂ (by decide) (by decide) (by decide)
    outFree := by
      simp only [Outside, heapNext, hnext₂]; rw [x10₂]; addr_omega [hsp, hstn, heap₁.hi]
    outStack := by simp only [stackLo, e2₂, x10₂]; addr_omega [hsp]
    pointFree := by
      simp only [Outside, heapNext, hnext₂]; rw [x11₂, x12₂]
      simp only [heapNext] at mono₁
      addr_omega [hpc', hmin, mono₁, hpb]
    pointStack := by
      simp only [stackLo, e2₂]; rw [x11₂, x12₂]; addr_omega [hpc', hmin, hsp, hpb]
    pointOut := by rw [x11₂, x12₂, x10₂]; addr_omega [hpc', hmin, hsp, hpb]
    rodata := by
      refine RodataOk.of_dwords (RodataOk.dframe pre₁.rodata post₁.frame fun a ha hw ↦ ?_)
        fun a _ ↦ hm₂ a
      simp only [stackLo, e2, hc.x10] at hw
      have := heap₁.hi
      simp only [Fresh, heapNext, heapEnd] at hw this
      addr_omega [ha, hw, hsp, hstr, this]
    outRodata := by rw [x10₂]; addr_omega [hsp, hstr] }
  obtain ⟨t₃, hr₃, ⟨pc₃, pres₃, post₃⟩ | hd⟩ := hEK.call hr₂ (b80010eb4_pc h₂) pre₂
  swap
  · exact ⟨t₃, hr₁.trans hr₃, Or.inl hd⟩
  have hx1₂ : returnAddress t₂ = 0x80010ec8 := by rw [returnAddress_eq, b80010eb4_x1 h₂]; rfl
  rw [hx1₂] at pc₃
  have e2₃ : t₃.getReg .x2 = s.getReg .x2 - 1968 := (pres₃.reg .x2).trans e2₂
  have heap₃ := post₃.heap
  have mono₃ : heapNext t₁ ≤ heapNext t₃ := by
    have := post₃.mono; simp only [heapNext, hnext₂] at this ⊢; exact this
  -- `vec![ZERO; 2048]`
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80010ec8_spec pc₃ (by
    rv_eval [e2₃]
    and_intros <;> valid_access hst [hsp])
  have k₄ := b80010ec8_keeps h₄
  have hf₄ := b80010ec8_frame h₄ (by rw [e2₃]; addr_omega [hsp])
  rw [e2₃] at hf₄
  have e2₄ : t₄.getReg .x2 = s.getReg .x2 - 1968 := (k₄ .x2 (by decide)).trans e2₃
  have hnext₄ : t₄.getMem nextAddr = t₃.getMem nextAddr := hf₄ _ (by addr_omega [hsp, hstn])
  have u₄ := h₄.unaligned (by rv_eval [e2₃]; and_intros <;> addr_omega [hsp])
  have pre₃ : FromElemPre t₄ := {
    heap := HeapOk.of_next heap₃ hnext₄
    out := by rw [b80010ec8_x10 h₄, e2₃]; rv_eval []; valid_sub hst [hsp]
    elem := by
      rw [b80010ec8_x11 h₄]
      intro i hi
      have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases this with rfl | rfl | rfl <;> decide
    stack := rtStack_inner hpre.stack e2₄ (by decide) (by decide) (by decide)
    outFree := by
      simp only [Outside, heapNext, hnext₄]; rw [b80010ec8_x10 h₄, e2₃]
      addr_omega [hsp, hstn, heap₃.hi]
    outStack := by simp only [stackLo, e2₄]; rw [b80010ec8_x10 h₄, e2₃]; addr_omega [hsp]
    elemFree := by
      simp only [Outside, heapNext, hnext₄]; rw [b80010ec8_x11 h₄]; addr_omega []
    elemStack := by
      simp only [stackLo, e2₄]; rw [b80010ec8_x11 h₄]; addr_omega [hsp, hstr]
    elemOut := by rw [b80010ec8_x11 h₄, b80010ec8_x10 h₄, e2₃]; addr_omega [hsp, hstr] }
  obtain ⟨t₅, hr₅, ⟨pc₅, pres₅, post₅⟩ | hd⟩ := hFE.call hr₄ (b80010ec8_pc h₄) pre₃
  swap
  · exact ⟨t₅, hr₁.trans (hr₃.trans hr₅), Or.inl hd⟩
  have hx1₄ : returnAddress t₄ = 0x80010efc := by rw [returnAddress_eq, b80010ec8_x1 h₄]; rfl
  rw [hx1₄] at pc₅
  refine ⟨t₅, hr₁.trans (hr₃.trans hr₅), Or.inr ⟨pc₅, t₁.getMem (s.getReg .x2 - 1752),
    t₃.getMem (s.getReg .x2 - 1728), t₅.getMem (s.getReg .x2 - 1704), ?_⟩⟩
  exact called_of hpre hc pres₁ post₁ hm₂ (k₂ .x8 (by decide)) e2₂ x10₂ x11₂ x12₂ pres₃ post₃ h₄
    pres₅ post₅

end Rv64Verifier.Proofs.Bytecode.Eval
