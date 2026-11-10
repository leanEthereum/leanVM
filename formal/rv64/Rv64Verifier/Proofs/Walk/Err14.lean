import Rv64Verifier.Proofs.Walk.ErrTail

/-!
# `walk`: the `Err` exits once the `Layout` exists, before the bus

`errTail0`: from `0x80004200` (drop the `Layout`, return) with the result's first word `errNiche`,
given the `Layout`'s `tables` `Vec` at `sp + 576`. `err14`: `stack_log` too large (`0x80003940`,
code `26`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

set_option maxRecDepth 8192 in
/-- From `0x80004200`: `drop_glue::<Layout>`, then the epilogue. -/
theorem errTail0 (hDL : DropLayoutSpec) {OI : MachineState → Word → List (List Opening) → Prop}
    {s u : MachineState} (hpre : WalkPre s) (I : Inv s u) (hpc : u.pc = 0x80004200) {B : Word}
    (hB : B.toNat % 8 = 0) (hB1 : 0x20000000 ≤ B.toNat) (hB2 : B.toNat + 480 ≤ 0x78000000)
    (eP : vecPtr u (s.getReg .x2 - 2080) = B) (eL : vecLen u (s.getReg .x2 - 2080) = 6)
    (he : u.getMem (s.getReg .x10) = errNiche) :
    ∃ t, Reaches Image.code u t ∧ (Done OI s t ∨ Dead Image.code t) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have sp := I.sp
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80004200_spec hpc trivial
  have m₁ := b80004200_mem_same h₁
  have k₁ := b80004200_keeps h₁
  have I₁ := I.same m₁ (k₁ .x2 (by decide))
  have x10 : u₁.getReg .x10 = s.getReg .x2 - 2080 := by
    rw [b80004200_x10 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have eP₁ : vecPtr u₁ (s.getReg .x2 - 2080) = B := by simp only [vecPtr, m₁]; exact eP
  have eL₁ : vecLen u₁ (s.getReg .x2 - 2080) = 6 := by simp only [vecLen, m₁]; exact eL
  have pre : DropLayoutPre u₁ := {
    self := by
      rw [x10]; exact Layout.validMemRange_of (by addr_omega [hb1, hb3]) (Or.inr ⟨by addr_omega [hb1],
        by addr_omega [hb1, hb2]⟩)
    elems := by
      rw [x10, eP₁, eL₁]
      exact Layout.validMemRange_of hB (Or.inl ⟨by omega, by simp; omega⟩)
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
/-- `0x80003940`: `Err(StackLogOutOfRange)`, code `26`. -/
theorem err14 (hDL : DropLayoutSpec) {OI : MachineState → Word → List (List Opening) → Prop}
    {s u : MachineState} (hpre : WalkPre s) (I : Inv s u) (hpc : u.pc = 0x80003940)
    (sret : u.getMem (s.getReg .x2 - 2488) = s.getReg .x10) {B : Word}
    (hB : B.toNat % 8 = 0) (hB1 : 0x20000000 ≤ B.toNat) (hB2 : B.toNat + 480 ≤ 0x78000000)
    (eP : vecPtr u (s.getReg .x2 - 2080) = B) (eL : vecLen u (s.getReg .x2 - 2080) = 6) :
    ∃ t, Reaches Image.code u t ∧ (Done OI s t ∨ Dead Image.code t) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have sp := I.sp
  have hR := hpre.out
  have hO := hpre.outStack
  rw [stackLo_eq, stack_eq] at hO
  have e168 : u.getReg .x2 + 168 = s.getReg .x2 - 2488 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b80003940_spec hpc (by
    rv_eval [sp]
    rw [sret]
    and_intros
    · exact Region.valid hR (by addr_omega [hR]) (by addr_omega [hR]) (by addr_omega [hR])
    · exact Region.valid hR (by addr_omega [hR]) (by addr_omega [hR]) (by addr_omega [hR])
    · simp only [Sym.validAccess_eight]; addr_omega [hb1, hb2, hb3])
  have fr₀ : MemFrame u t (s.getReg .x10) 16 := ht.memFrame (by
    rv_eval [e168, sret]; simp only [Within]; and_intros <;> addr_omega [hR])
  have fr := DFrame.of_memFrame fr₀
  have hx := hpre.outFree.2
  have hn : heapNext t = heapNext u := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr nextAddr fun i hi hw ↦ by addr_omega [hx, hw, hi])
  have It : Inv s t := I.step hpre fr
    (fun a ha ↦ ⟨Or.inl (by addr_omega [ha, hR]), by addr_omega [ha, hO, hb1]⟩)
    ⟨hn ▸ I.heap.lo, hn ▸ I.heap.hi⟩ hn.ge (b80003940_keeps ht .x2 (by decide))
  have g (o : Nat) (ho : o + 8 ≤ 24) : t.getMem (s.getReg .x2 - 2080 + BitVec.ofNat 64 o) =
      u.getMem (s.getReg .x2 - 2080 + BitVec.ofNat 64 o) :=
    fr₀ _ (by simp only [Within]; addr_omega [hR, hO, hb1, ho])
  have m1 := b80003940_m1 ht
  rw [e168, sret] at m1
  obtain ⟨t', hr', ht'⟩ := errTail0 (OI := OI) hDL hpre It (b80003940_pc ht) hB hB1 hB2
    (by rw [← eP]; exact g 8 (by decide)) (by rw [← eL]; exact g 16 (by decide)) m1
  exact ⟨t', hr.trans hr', ht'⟩

end Rv64Verifier.Proofs.Walk
