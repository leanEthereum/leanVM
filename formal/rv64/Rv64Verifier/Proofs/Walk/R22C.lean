import Rv64Verifier.Proofs.Walk.R22B

/-!
# `walk` R22: `finish` and the return

`r22`: from `0x80004144`, `verify_stacked_opening` having returned `Ok`, `finish` compares the
stream's offset with its length and the openings' offset with their count (a mismatch is an `Err`,
`err41cc`); then the summary goes to the result, its first word `6`, and the function returns with
`ok`: the mirror's `finish` returns (`finish_tracks`), and so does `verifyExecutionRust`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- `finish` returns when both offsets are at their ends. -/
theorem finish_run (summary : SummaryRust) (T : TState)
    (h1 : T.streamOffset = T.proof.stream.length)
    (h2 : T.openingOffset = T.proof.openings.length) :
    (finishRust summary).run T = (pure summary : TM SummaryRust).run T := by
  simp only [finishRust, StateT.run_bind]
  simp [TM.finish, StateT.run, h1, h2]

/-- The checks passed: what is left is the summary. -/
theorem finish_tracks {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {summary : SummaryRust} (hpre : WalkPre s) (I : Inv s u)
    (hptr : u.getMem (tp s) = s.getReg .x13) (htr : TracksN OI s u (finishRust summary))
    (h1 : u.getMem (tp s + 344) = u.getMem (u.getMem (tp s) + 16))
    (h2 : u.getMem (tp s + 352) = u.getMem (u.getMem (tp s) + 40)) :
    TracksN OI s u (pure summary) := fun proof hp ↦ by
  obtain ⟨T, eT, hT, hr⟩ := htr proof hp
  refine ⟨T, eT, hT, hr.trans (finish_run summary T ?_ ?_)⟩
  · rw [← hT.streamOffset, ← hT.stream, eListAt_length, h1]
    simp only [streamLen, vecLen, proofAt]
  · have hP := hpre.proof
    have e : u.getMem (s.getReg .x13 + 40) = s.getMem (s.getReg .x13 + 40) :=
      I.word hpre.proofRO (by addr_omega [hP]) (by addr_omega [hP]) (by addr_omega [hP])
    rw [← hT.openingOffset, eT, ← hp.openingsLen, h2, hptr, e]
    simp only [vecLen]
    rw [BitVec.add_assoc]; rfl

set_option maxRecDepth 8192 in
/-- From `0x80004144` to the return, or a dead end. -/
theorem r22 (hDN : DropNopSpec) (hDL : DropLayoutSpec)
    {OI : MachineState → Word → List (List Opening) → Prop}
    {s u₀ u : MachineState} {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)}
    {lir : BitVec 64} {bus : BusResultRust} {summary : SummaryRust} (hpre : WalkPre s)
    (h : AtR17 OI s u₀ layout rows lir bus) (A : AtR22 OI s u₀ u summary) :
    ∃ t, Reaches Image.code u t ∧ (Done OI s t ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have I := A.rest.inv
  have sp := I.sp
  have hP := hpre.proof
  have hP1 := hP.1
  have hP2 := hP.2
  simp only [Mapped] at hP1
  have e208 : u.getReg .x2 + 208 = tp s := by rw [sp, tp]; bv_omega
  have e552 : u.getReg .x2 + 552 = tp s + 344 := by rw [sp, tp]; bv_omega
  have e560 : u.getReg .x2 + 560 = tp s + 352 := by rw [sp, tp]; bv_omega
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80004144_spec A.pc (by
    rv_eval [e208, A.proofPtr]
    refine ⟨Region.valid hP (by addr_omega [hP1]) (by addr_omega [hP1]) (by addr_omega [hP1, hP2]), ?_,
      ?_⟩ <;> valid_access hval [hb1, sp])
  have m₁ := b80004144_mem_same h₁
  have k₁ := b80004144_keeps h₁
  by_cases hc1 : u.getMem (tp s + 344) = u.getMem (u.getMem (tp s) + 16)
  swap
  · have pc₁ := b80004144_pc_taken h₁ (by rw [e208, e552]; exact hc1)
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800041c0_spec pc₁ (by rv_eval [])
    have m₂ := b800041c0_mem_same h₂
    have k₂ := b800041c0_keeps h₂
    refine err41cc hDN hDL hpre h ⟨b800041c0_pc h₂, ?_, ?_, ?_⟩ |>.elim fun t ⟨hr, ht⟩ ↦
      ⟨t, hr₁.trans (hr₂.trans hr), ht⟩
    · exact (A.rest.same m₁ (k₁ .x2 (by decide))).same m₂ (k₂ .x2 (by decide))
    · rw [k₂ .x23 (by decide), k₁ .x23 (by decide), A.x23]
    · left; rw [k₂ .x10 (by decide), b80004144_x10 h₁]
  have pc₁ := b80004144_pc_not_taken h₁ (by rw [e208, e552]; exact hc1)
  have x11₁ : u₁.getReg .x11 = s.getReg .x13 := by rw [b80004144_x11 h₁, e208, A.proofPtr]
  have sp₁ : u₁.getReg .x2 = u.getReg .x2 := k₁ .x2 (by decide)
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80004158_spec pc₁ (by
    rv_eval [x11₁, sp₁, sp]
    refine ⟨Region.valid hP (by addr_omega [hP1]) (by addr_omega [hP1]) (by addr_omega [hP1, hP2]), ?_⟩
    valid_access hval [hb1])
  have m₂ := b80004158_mem_same h₂
  have k₂ := b80004158_keeps h₂
  have R₂ := (A.rest.same m₁ (k₁ .x2 (by decide))).same m₂ (k₂ .x2 (by decide))
  by_cases hc2 : u.getMem (tp s + 352) = u.getMem (u.getMem (tp s) + 40)
  swap
  · have pc₂ := b80004158_pc_taken h₂ (by rw [sp₁, x11₁, m₁, m₁, e560, ← A.proofPtr]; exact hc2)
    obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800041c8_spec pc₂ (by rv_eval [])
    have m₃ := b800041c8_mem_same h₃
    have k₃ := b800041c8_keeps h₃
    refine err41cc hDN hDL hpre h ⟨b800041c8_pc h₃, R₂.same m₃ (k₃ .x2 (by decide)), ?_, ?_⟩
      |>.elim fun t ⟨hr, ht⟩ ↦ ⟨t, hr₁.trans (hr₂.trans (hr₃.trans hr)), ht⟩
    · rw [k₃ .x23 (by decide), k₂ .x23 (by decide), k₁ .x23 (by decide), A.x23]
    · left; rw [k₃ .x10 (by decide), k₂ .x10 (by decide), b80004144_x10 h₁]
  have pc₂ := b80004158_pc_not_taken h₂ (by rw [sp₁, x11₁, m₁, m₁, e560, ← A.proofPtr]; exact hc2)
  have ok := (finish_tracks hpre I A.proofPtr A.tracks hc1 hc2).done
  have sp₂ : u₂.getReg .x2 = s.getReg .x2 - 2656 := by rw [k₂ .x2 (by decide), sp₁, sp]
  have x23₂ : u₂.getReg .x23 = s.getReg .x10 := by
    rw [k₂ .x23 (by decide), k₁ .x23 (by decide), A.x23]
  have x24₂ : u₂.getReg .x24 = s.getReg .x2 - 512 := by
    rw [k₂ .x24 (by decide), k₁ .x24 (by decide), A.x24]
  have hR := hpre.out
  have hRb := hR.1
  have hRa := hR.2
  have hO := hpre.outStack
  rw [stackLo_eq, stack_eq] at hO
  simp only [Mapped] at hRb
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80004164_spec pc₂ (by
    rv_eval [sp₂, x23₂, x24₂]
    and_intros
    all_goals first
      | (refine Region.valid hR ?_ ?_ ?_ <;> addr_omega [hRb, hRa])
      | valid_access hval [hb1]
      | (intro he; have := congrArg BitVec.toNat he; addr_omega [this, hO, hb1, hRb]))
  have fr : DFrame u₂ u₃ (Within · (s.getReg .x10) 80) := by
    have := DFrame.of_memFrame (b80004164_frame h₃ (by rw [x23₂]; addr_omega [hRb]))
    rwa [x23₂] at this
  have R₃ := R₂.result hpre (by omega) fr (b80004164_keeps h₃ .x2 (by decide))
  obtain ⟨u₄, hr₄, ⟨hpc₄, hp₄, m₄⟩ | hd⟩ := hDN.call hr₃ (b80004164_pc h₃) trivial
  swap
  · exact ⟨u₄, hr₁.trans (hr₂.trans hr₄), Or.inr hd⟩
  have R₄ := R₃.same m₄ (hp₄ .x2 (by decide))
  have sp₄ : u₄.getReg .x2 = s.getReg .x2 - 2656 := R₄.inv.sp
  obtain ⟨u₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b800041b4_spec
    (by rw [hpc₄, returnAddress_eq, b80004164_x1 h₃]; decide) (by
      rv_eval [sp₄]; and_intros <;> valid_access hval [hb1])
  have m₅ := b800041b4_mem_same h₅
  obtain ⟨u₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b800041f8_spec (b800041b4_pc h₅) trivial
  have m₆ := b800041f8_mem_same h₆
  obtain ⟨u₇, hr₇, ⟨hpc₇, hp₇, m₇⟩ | hd⟩ := hDN.call (hr₅.trans hr₆) (b800041f8_pc h₆) trivial
  swap
  · exact ⟨u₇, hr₁.trans (hr₂.trans (hr₄.trans hr₇)), Or.inr hd⟩
  have R₇ := ((R₄.same m₅ (b800041b4_keeps h₅ .x2 (by decide))).same m₆
    (b800041f8_keeps h₆ .x2 (by decide))).same m₇ (hp₇ .x2 (by decide))
  obtain ⟨t, hr₈, ht⟩ := errTailN hDL hpre h R₇
    (by rw [hpc₇, returnAddress_eq, b800041f8_x1 h₆]; decide) fun _ ↦ ok
  exact ⟨t, hr₁.trans (hr₂.trans (hr₄.trans (hr₇.trans hr₈))), ht⟩

end Rv64Verifier.Proofs.Walk
