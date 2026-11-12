import LeanVM.Prover.EndChild

/-!
# leanVM's statements, locked

Statement locks of `LeanVM/Protocol/LeanVMRpm.lean`: knowledge soundness and completeness in the
random-permutation model (`Statement/LeanVm.lean`), the statements of the specification, and their
numbers, with the axioms each depends on.
-/

open LeanVM.Semantics LeanVM

example {A : RandomPermutationAdversary} {Q : ℕ} (hA : Common.QueryCostAtMost A Common.permutationCallCost Q)
    (hQ : Q ≤ 2 ^ 128) :
    Pr{let z ← knowledgeSoundnessExperiment A}[z.accepted = true ∧
      ¬ ∃ t, transcriptExtractor z.program z.input z.transcript z.proof = some t ∧
        ValidExecution z.program z.input t] ≤
      (Q + 2 ^ 14 : ENNReal) * (2 : ENNReal)⁻¹ ^ 125 +
        5 * (Q + 2 ^ 14 : ENNReal) ^ 2 * (2 : ENNReal)⁻¹ ^ 256 :=
  knowledgeSoundness_holds A Q hA hQ

/-- The numbers: `13708 · 2^30` permutation calls of the verifier, the transfer's `q² / 2^508`. -/
example (q : ℕ) : rpmError q = (q ^ 2 : ENNReal) / 2 ^ 508 := rfl

example : verifierPermCalls = 13708 * 2 ^ 30 := rfl

example : KnowledgeSoundness transcriptExtractor := knowledgeSoundness_holds

example : Completeness := completeness_holds

/--
info: 'LeanVM.knowledgeSoundness_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms knowledgeSoundness_holds

/--
info: 'LeanVM.completeness_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms completeness_holds

/--
info: 'LeanVM.Guest.Budget.guest_child_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LeanVM.Guest.Budget.guest_child_complete

/--
info: 'LeanVM.Prover.prove_eq_honestComp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LeanVM.Prover.prove_eq_honestComp
