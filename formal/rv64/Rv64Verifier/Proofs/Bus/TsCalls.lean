import Rv64Verifier.Proofs.Bus.TsStart

/-!
# `table_sumcheck`: the epilogue and `vec![None; n_rounds]`

`0x8000893c` restores the saved registers and returns. `0x800080b8` calls
`<Option<E> as SpecFromElem>::from_elem` into `S - 248` (`sp + 248`), the element a `None` at
`sp + 296`; it returns to `0x800080cc`.
-/

namespace Rv64Verifier.Proofs.Bus.TableSumcheck
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Model
  Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F30
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem slot {s u : MachineState} (hpre : TableSumcheckPre s) (h : Inv s u) (k i : Nat)
    (hi : i < 13) (hk : k = 488 - 8 * i) :
    u.getMem (u.getReg .x2 + BitVec.ofNat 64 k) = s.getReg (savedRegs.getD i .x0) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  rw [← h.saved i hi, h.sp]
  congr 1
  addr_omega [hb1, hk, hi]

/-- The epilogue returns to the caller with its saved registers. -/
theorem epilogue {s u : MachineState} (hpre : TableSumcheckPre s) (h : Inv s u)
    (hpc : u.pc = 0x8000893c) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      ∀ a, t.getMem a = u.getMem a := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hpre.stack.valid
  obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b8000893c_spec hpc (by
    rv_eval [h.sp]
    and_intros <;> valid_access hval [hb1])
  have x2 := b8000893c_x2 ht
  rw [h.sp] at x2
  rv_eval [] at x2
  refine ⟨t, hr, ?_, preserves_of x2 ?_ ?_ ?_ ?_ fun r hr' ↦ ?_, b8000893c_mem_same ht⟩
  · rw [b8000893c_pc ht, returnAddress_eq]
    exact congrArg (· &&& _) (slot hpre h 488 0 (by decide) rfl)
  · rw [b8000893c_x8 ht]; exact slot hpre h 480 1 (by decide) rfl
  · rw [b8000893c_x9 ht]; exact slot hpre h 472 2 (by decide) rfl
  · rw [b8000893c_x18 ht]; exact slot hpre h 464 3 (by decide) rfl
  · rw [b8000893c_x19 ht]; exact slot hpre h 456 4 (by decide) rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [b8000893c_x20 ht]; exact slot hpre h 448 5 (by decide) rfl
    · rw [b8000893c_x21 ht]; exact slot hpre h 440 6 (by decide) rfl
    · rw [b8000893c_x22 ht]; exact slot hpre h 432 7 (by decide) rfl
    · rw [b8000893c_x23 ht]; exact slot hpre h 424 8 (by decide) rfl
    · rw [b8000893c_x24 ht]; exact slot hpre h 416 9 (by decide) rfl
    · rw [b8000893c_x25 ht]; exact slot hpre h 408 10 (by decide) rfl
    · rw [b8000893c_x26 ht]; exact slot hpre h 400 11 (by decide) rfl
    · rw [b8000893c_x27 ht]; exact slot hpre h 392 12 (by decide) rfl

/-- `from_elem`'s arguments at `0x800080b8`'s end. -/
theorem optPre {s u : MachineState} (hpre : TableSumcheckPre s) (h : Inv s u)
    (h10 : u.getReg .x10 = s.getReg .x2 - 248) (h11 : u.getReg .x11 = s.getReg .x2 - 200) :
    OptFromElemPre u := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hx := hpre.stack.next
  rw [stackLo_eq, stack_eq] at hx
  have hst : RtStack u optFromElemStack :=
    hpre.stack.sub 496 h.sp (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsl : stackLo u optFromElemStack = s.getReg .x2 - 736 := by
    show u.getReg .x2 - BitVec.ofNat 64 240 = _
    rw [h.sp]; addr_omega [hb1]
  refine ⟨h.heap, ?_, ?_, hst, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [h10, h11, hsl, Outside, heapEnd] <;> addr_omega [hb1, hb2, hb3, hx]

/-- `vec![None; n_rounds]`, from `0x800080b8` to `0x800080cc`: a new `Vec` at `S - 248` of
`n_rounds` `None`s. -/
theorem stageA (hOF : OptFromElemSpec) {s u : MachineState} (hpre : TableSumcheckPre s)
    (h : Inv s u) (hpc : u.pc = 0x800080b8) (h12 : (u.getReg .x12).toNat = nRounds s) :
    ∃ v, Reaches Image.code u v ∧ ((Inv s v ∧ v.pc = 0x800080cc ∧ (∀ r ∈ calleeSaved,
      v.getReg r = u.getReg r) ∧ DFrame u v (Loc s u v) ∧
      VecOk v (s.getReg .x2 - 248) 32 8 ∧ (vecLen v (s.getReg .x2 - 248)).toNat = nRounds s ∧
      optEListAt v (vecPtr v (s.getReg .x2 - 248)) (nRounds s) = List.replicate (nRounds s) none ∧
      NewBuf u v (vecPtr v (s.getReg .x2 - 248)) (32 * nRounds s) 8) ∨ Dead Image.code v) := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 2128) 266 := hpre.stack.valid
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800080b8_spec hpc (by
    rv_eval [h.sp]; valid_access hval [hb1])
  have hf₁ := DFrame.of_memFrame (b800080b8_frame h₁ (by rw [h.sp]; addr_omega [hb1]))
  rw [h.sp] at hf₁
  have hk₁ := b800080b8_keeps h₁
  have hn₁ : heapNext u₁ = heapNext u := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (hf₁ nextAddr fun i hi hw ↦ by addr_omega [hw, hi, hb1])
  have hL₁ : DFrame u u₁ (Loc s u u₁) :=
    hf₁.mono fun a ha ↦ Or.inl (by addr_omega [ha, hb1])
  have I₁ : Inv s u₁ := h.loc hpre hL₁ ⟨hn₁ ▸ h.heap.lo, hn₁ ▸ h.heap.hi⟩ hn₁.ge
    (hk₁ .x2 (by decide))
  have h10 : u₁.getReg .x10 = s.getReg .x2 - 248 := by rw [b800080b8_x10 h₁, h.sp]; rv_eval []
  have h11 : u₁.getReg .x11 = s.getReg .x2 - 200 := by rw [b800080b8_x11 h₁, h.sp]; rv_eval []
  have hnone : u₁.getMem (s.getReg .x2 - 200) = 0 := by
    have := b800080b8_m_x2_296 h₁
    rw [h.sp] at this
    rv_eval [] at this
    exact this
  obtain ⟨u₂, hr₂, ⟨hpc₂, hp₂, post⟩ | hd⟩ :=
    hOF.call hr₁ (b800080b8_pc h₁) (optPre hpre I₁ h10 h11)
  swap
  · exact ⟨u₂, hr₂, Or.inr hd⟩
  have hsl : stackLo u₁ optFromElemStack = s.getReg .x2 - 736 := by
    show u₁.getReg .x2 - BitVec.ofNat 64 240 = _
    rw [I₁.sp]; addr_omega [hb1]
  have hfr := post.frame
  rw [h10, hsl] at hfr
  have hm₂ := post.mono
  have hL₂ : DFrame u u₂ (Loc s u u₂) := (hL₁.mono fun a ha ↦ by
      rcases ha with ha | ha | ⟨h1, h2⟩
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ⟨h1, by omega⟩)).trans (DFrame.of_byteFrame hfr) fun a ha ↦ by
    rcases ha with ha | ha | ha | ⟨h1, h2⟩
    · exact Or.inl (by addr_omega [ha, hb1])
    · exact Or.inl (by addr_omega [ha, hb1])
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr ⟨by omega, h2⟩)
  have hn₂ : heapNext u ≤ heapNext u₂ := hn₁.symm.le.trans hm₂
  have hx12 : u₁.getReg .x12 = u.getReg .x12 := hk₁ .x12 (by decide)
  have hel := post.elems
  have hfresh := post.fresh
  have hlen := post.len
  simp only [h10, h11, hx12] at hel hfresh hlen
  rw [h12] at hel hfresh
  refine ⟨u₂, hr₂, Or.inl ⟨h.loc hpre hL₂ post.heap hn₂ (by rw [hp₂.reg .x2, hk₁ .x2 (by decide)]),
    by rw [hpc₂, returnAddress_eq, b800080b8_x1 h₁]; decide,
    fun r hr ↦ by rw [hp₂ r hr, hk₁ r (mem_of_calleeSaved hr _)], hL₂, h10 ▸ post.vec,
    by rw [hlen, h12], ?_, ?_⟩⟩
  · rw [hel]
    congr 1
    simp only [optEAt, hnone, ↓reduceIte]
  · simp only [NewBuf] at hfresh ⊢
    rw [hn₁] at hfresh
    exact hfresh

end Rv64Verifier.Proofs.Bus.TableSumcheck
