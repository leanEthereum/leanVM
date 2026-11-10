import Rv64Verifier.Proofs.Walk.Tail
import Rv64Verifier.Proofs.Bus.TsStart

/-!
# `walk` from `0x800035f0` on: the `Err` exits

Past the layout, an `Err` path drops the `Vec<Vec<Form>>`s (`0x800041f0`, `0x800041f8`: no-ops)
and the `Layout` (`0x80004200`), then returns (`0x800012e4`). With the result's first word
`errNiche`, the function returns with its contract's post (`errTail`, `errTail₁`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

set_option maxRecDepth 8192 in
/-- From `0x80004200`: `drop_glue::<Layout>`, then the epilogue. -/
theorem errTail (hDL : DropLayoutSpec) {OI : MachineState → Word → List (List Opening) → Prop}
    {s u₀ u : MachineState} {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)}
    {lir : BitVec 64} {bus : BusResultRust} (hpre : WalkPre s)
    (h : AtR17 OI s u₀ layout rows lir bus) (R : Rest s u₀ u) (hpc : u.pc = 0x80004200)
    (he : u.getMem (s.getReg .x10) = errNiche) :
    ∃ t, Reaches Image.code u t ∧ (Done OI s t ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have I := R.inv
  have sp := I.sp
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80004200_spec hpc trivial
  have m₁ := b80004200_mem_same h₁
  have k₁ := b80004200_keeps h₁
  have I₁ := I.same m₁ (k₁ .x2 (by decide))
  have x10 : u₁.getReg .x10 = s.getReg .x2 - 2080 := by
    rw [b80004200_x10 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have LI := h.layoutIn
  have eP : vecPtr u₁ (s.getReg .x2 - 2080) = u₀.getMem (s.getReg .x2 - 2456) := by
    rw [vecPtr, m₁, show s.getReg .x2 - 2080 + 8 = s.getReg .x2 - BitVec.ofNat 64 2072 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1], R.get (keep_slot hpre (by omega)),
      show s.getReg .x2 - BitVec.ofNat 64 2072 = s.getReg .x2 - 2080 + 8 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
    exact LI.tablesVec.1
  have eL : vecLen u₁ (s.getReg .x2 - 2080) = 6 := by
    rw [vecLen, m₁, show s.getReg .x2 - 2080 + 16 = s.getReg .x2 - BitVec.ofNat 64 2064 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1], R.get (keep_slot hpre (by omega)),
      show s.getReg .x2 - BitVec.ofNat 64 2064 = s.getReg .x2 - 2080 + 16 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
    exact LI.tablesVec.2
  have hT := NewBuf.region LI.tables.newBuf hpre.heap h.inv.heap (by decide)
  have pre : DropLayoutPre u₁ := {
    self := by rw [x10]; valid_sub hval [hb1]
    elems := by
      rw [x10, eP, eL]
      exact Bus.TableSumcheck.region_range (n := 60) hT
    stack := calleeStack hpre I₁ (by decide) (by decide)
    selfStack := by rw [x10, stackLo_callee I₁]; simp only [dropLayoutStack]; addr_omega [hb1] }
  obtain ⟨u₂, hr₂, ⟨hpc₂, hp₂, post⟩ | hd⟩ := hDL.call hr₁ (b80004200_pc h₁) pre
  swap
  · exact ⟨u₂, hr₂, Or.inr hd⟩
  have hsl := stackLo_callee I₁ dropLayoutStack
  have fr : MemFrame u₁ u₂ (s.getReg .x2 - 2656 - BitVec.ofNat 64 dropLayoutStack) dropLayoutStack :=
    hsl ▸ post
  have st : Step s u₁ u₂ (s.getReg .x2 - 2656 - BitVec.ofNat 64 dropLayoutStack) 0 := by
    have hx := hpre.stack.next
    rw [stackLo_eq, stack_eq] at hx
    have hn : heapNext u₂ = heapNext u₁ := by
      simp only [heapNext]
      rw [fr nextAddr (by simp only [dropLayoutStack]; addr_omega [hb1, hx])]
    refine ⟨(DFrame.of_memFrame fr).mono fun a ha ↦ Or.inr (Or.inl ?_),
      ⟨hn ▸ I₁.heap.lo, hn ▸ I₁.heap.hi⟩, hn.ge, hp₂ .x2 (by decide)⟩
    simp only [dropLayoutStack] at ha; addr_omega [ha, hb1]
  have I₂ : Inv s u₂ := I₁.loc hpre (st.frame.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact absurd ha.2 (by have := ha.1; omega)
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ha)) st.heap st.mono st.sp
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000420c_spec
    (by rw [hpc₂, returnAddress_eq, b80004200_x1 h₁]; decide) trivial
  have m₃ := b8000420c_mem_same h₃
  have I₃ := I₂.same m₃ (b8000420c_keeps h₃ .x2 (by decide))
  have hO := hpre.outStack
  rw [stackLo_eq, stack_eq] at hO
  obtain ⟨t, hr₄, hdone⟩ := errExit (OI := OI) hpre I₃ (b8000420c_pc h₃) (by
    rw [m₃, fr _ (by simp only [dropLayoutStack]; addr_omega [hb1, hO]), m₁]
    exact he)
  exact ⟨t, hr₂.trans (hr₃.trans hr₄), Or.inl hdone⟩

set_option maxRecDepth 8192 in
/-- From `0x800041f0`: `drop_glue::<Vec<Vec<Form>>>`, then `errTail`. -/
theorem errTail₁ (hDN : DropNopSpec) (hDL : DropLayoutSpec)
    {OI : MachineState → Word → List (List Opening) → Prop}
    {s u₀ u : MachineState} {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)}
    {lir : BitVec 64} {bus : BusResultRust} (hpre : WalkPre s)
    (h : AtR17 OI s u₀ layout rows lir bus) (R : Rest s u₀ u) (hpc : u.pc = 0x800041f0)
    (he : u.getMem (s.getReg .x10) = errNiche) :
    ∃ t, Reaches Image.code u t ∧ (Done OI s t ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have sp := R.inv.sp
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800041f0_spec hpc (by
    rv_eval [sp]; valid_access hval [hb1])
  have m₁ := b800041f0_mem_same h₁
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800041f8_spec (b800041f0_pc h₁) trivial
  have m₂ := b800041f8_mem_same h₂
  obtain ⟨u₃, hr₃, ⟨hpc₃, hp₃, m₃⟩ | hd⟩ := hDN.call (hr₁.trans hr₂) (b800041f8_pc h₂) trivial
  swap
  · exact ⟨u₃, hr₃, Or.inr hd⟩
  have mm (a : Word) : u₃.getMem a = u.getMem a := by rw [m₃, m₂, m₁]
  have R₃ := R.same mm ((hp₃ .x2 (by decide)).trans ((b800041f8_keeps h₂ .x2 (by decide)).trans
    (b800041f0_keeps h₁ .x2 (by decide))))
  obtain ⟨t, hr₄, ht⟩ := errTail hDL hpre h R₃
    (by rw [hpc₃, returnAddress_eq, b800041f8_x1 h₂]; decide) (by rw [mm]; exact he)
  exact ⟨t, hr₃.trans hr₄, ht⟩

end Rv64Verifier.Proofs.Walk
