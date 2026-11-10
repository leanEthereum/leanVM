import Rv64Verifier.Proofs.Transcript.RoundPolyNoneHead

/-!
# `Transcript::sumcheck_round_poly` meets its contract

The frame and the branch on `eq_factor`'s tag (`entry`), then either path to `Ready` and
`finish`.
-/

namespace Rv64Verifier.Transcript.RoundPoly
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F44
  Rv64Verifier.Contracts LeanVM.Protocol.Verifier
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

set_option maxHeartbeats 1000000 in
/-- The frame, then on `eq_factor`'s tag. -/
theorem entry {s : MachineState} (hpc : s.pc = 0x8000c334) (hpre : RoundPolyPre s) :
    ∃ u, Reaches Image.code s u ∧ Fr s u ∧ u.getReg .x18 = s.getReg .x13 ∧
      (∀ r ∈ [Reg.x9, .x11, .x12, .x14, .x19, .x20, .x21, .x22, .x23, .x24],
        u.getReg r = s.getReg r) ∧
      (∀ T, TranscriptAt s (s.getReg .x11) T → TranscriptAt u (s.getReg .x11) T) ∧
      ((s.getMem (s.getReg .x14) = 0 ∧ u.pc = 0x8000c488) ∨
        (s.getMem (s.getReg .x14) ≠ 0 ∧ u.pc = 0x8000c370)) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have he := hpre.eqFactor
  obtain ⟨u, hr, h⟩ := Sym.BlockSpec.reaches b8000c334_spec hpc (by
    rv_eval []
    and_intros <;> first
      | addr_omega [hb, he, hpre.eqFactorStack]
      | valid_access hst.valid [hb]
      | (refine Region.valid he ?_ ?_ ?_ <;> addr_omega [he]))
  have k := b8000c334_keeps h
  have f := b8000c334_frame h (by addr_omega [hb])
  have nx : heapNext u = heapNext s := by
    simp only [heapNext]; rw [f _ (by addr_omega [hst.next, hb])]
  refine ⟨u, hr, {
    saved := {
      x2 := b8000c334_x2 h
      kept := fun r hr ↦ k r (mem_of_mem hr _)
      ra := b8000c334_m_x2_n8 h
      s0 := b8000c334_m_x2_n16 h
      s1 := b8000c334_m_x2_n24 h
      s2 := b8000c334_m_x2_n32 h
      s3 := b8000c334_m_x2_n40 h
      s4 := b8000c334_m_x2_n48 h
      s5 := b8000c334_m_x2_n56 h
      s6 := b8000c334_m_x2_n64 h
      s7 := b8000c334_m_x2_n72 h
      s8 := b8000c334_m_x2_n80 h }
    x8 := b8000c334_x8 h
    heap := ⟨nx ▸ hpre.heap.lo, nx ▸ hpre.heap.hi⟩
    mono := Nat.le_of_eq nx.symm
    frame := (DFrame.of_memFrame f).mono fun a ha ↦ Or.inr (Or.inl (by addr_omega [ha, hb])) },
    b8000c334_x18 h, fun r hr ↦ k r (mem_of_mem hr _), fun T hT ↦
      TLow.transcriptAt hpre.toTPre (hi := heapNext s) hpre.heap.hi hpre.heap.hi (DFrame.refl s _)
        ((DFrame.of_memFrame f).mono fun a ha ↦ Or.inl (by addr_omega [ha, hb])) hT, ?_⟩
  by_cases ht : s.getMem (s.getReg .x14) = 0
  · exact Or.inl ⟨ht, b8000c334_pc_taken h ht⟩
  · exact Or.inr ⟨ht, b8000c334_pc_not_taken h ht⟩

set_option maxHeartbeats 1000000 in
/-- **`Transcript::sumcheck_round_poly` meets its contract**, given `next_scalars`',
`next_scalar`'s, the allocator's, `E`'s product's and `concat`'s. -/
theorem round_poly_spec (hNS : NextScalarsSpec) (hN : NextScalarSpec) (hA : AllocSpec)
    (hM : MulSpec) (hC : ConcatSpec) : RoundPolySpec := by
  intro s hpc hpre
  obtain ⟨u, hr, Fu, x18, kr, hT, br⟩ := entry hpc hpre
  have kr' : ∀ r ∈ [Reg.x11, .x12, .x14], u.getReg r = s.getReg r :=
    fun r hr ↦ kr r (mem_of_mem hr _)
  rcases br with ⟨htag, hpcu⟩ | ⟨htag, hpcu⟩
  · obtain ⟨v₁, h₁, ⟨hpc₁, hv₁⟩ | hd⟩ := noneConst hN hpre hpcu Fu x18 kr' htag hT
    swap
    · exact ⟨v₁, hr.trans h₁, hd⟩
    obtain ⟨v₂, h₂, ⟨hpc₂, hv₂⟩ | hd⟩ := noneTail hNS hpre htag hpc₁ hv₁
    swap
    · exact ⟨v₂, hr.trans (h₁.trans h₂), hd⟩
    obtain ⟨v₃, h₃, ⟨hpc₃, hv₃⟩ | hd⟩ := noneSum hA hpre hpc₂ hv₂
    swap
    · exact ⟨v₃, hr.trans (h₁.trans (h₂.trans h₃)), hd⟩
    obtain ⟨v₄, h₄, hpc₄, hv₄⟩ := noneHead hpre htag hpc₃ hv₃
    obtain ⟨t, h₅, ht⟩ := finish hC hpre hpc₄ hv₄
    exact ⟨t, hr.trans (h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))), ht⟩
  · obtain ⟨v₁, h₁, ⟨hpc₁, hv₁⟩ | hd⟩ := someTail hNS hpre hpcu Fu x18 kr' htag hT
    swap
    · exact ⟨v₁, hr.trans h₁, hd⟩
    obtain ⟨v₂, h₂, ⟨hpc₂, hv₂⟩ | hd⟩ := someSum hA hpre hpc₁ hv₁
    swap
    · exact ⟨v₂, hr.trans (h₁.trans h₂), hd⟩
    obtain ⟨v₃, h₃, ⟨hpc₃, hv₃⟩ | hd⟩ := someMul hM hpre htag hpc₂ hv₂
    swap
    · exact ⟨v₃, hr.trans (h₁.trans (h₂.trans h₃)), hd⟩
    obtain ⟨t, h₄, ht⟩ := finish hC hpre hpc₃ hv₃
    exact ⟨t, hr.trans (h₁.trans (h₂.trans (h₃.trans h₄))), ht⟩

end Rv64Verifier.Transcript.RoundPoly
