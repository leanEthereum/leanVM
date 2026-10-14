import Whir.PublicCompressionCoupling

/-! Actual finite probability of a later fresh compression answer filling an
already queried CV position. This includes the backward-recognition mechanism.
It does not bound forward guesses of unrevealed construction chaining values
and must not be presented as the complete simulator distinguishing loss. -/
namespace Whir.PublicCompressionCoupling
open FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame
open PublicCompressionProgram TypedOracleCompiler
attribute [local instance] PublicMerkleLog.instDecidableEqNode

noncomputable def lateLinkAlarm {R : Type} (C : PrimitiveOracle) {Q : Nat} :
    Computation R Q → Log → Bool
  | .ret _, _ => false
  | .draw input next, log =>
      decide (PublicMerkleLog.lookup log input = none ∧
        C input ∈ PublicMerkleProbability.cvTargets log) ||
      lateLinkAlarm C (next (C input)) ((input,C input)::log)

theorem lateLinkAlarm_implies_table_alarm {R : Type} (C : PrimitiveOracle) {Q : Nat}
    (p : Computation R Q) (log : Log) (hit : lateLinkAlarm C p log = true) :
    PublicMerkleProbability.alarm (fun _ => ∅) C p log = true := by
  induction p generalizing log with
  | ret => simp [lateLinkAlarm] at hit
  | draw input next ih =>
    rcases Bool.or_eq_true_iff.mp hit with first | later
    · have event := of_decide_eq_true first
      have targets : C input ∈ PublicMerkleProbability.badTargets (fun _ => ∅) log := by
        simp only [PublicMerkleProbability.badTargets,PublicMerkleProbability.targets]
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr event.2)))
      apply Bool.or_eq_true_iff.mpr
      exact Or.inl (decide_eq_true ⟨event.1,targets⟩)
    · apply Bool.or_eq_true_iff.mpr
      exact Or.inr (ih (C input) ((input,C input)::log) later)

theorem actual_lateLink_probability {R : Type} {Q : Nat} (p : Computation R Q) :
    average (fun C : PrimitiveOracle => if lateLinkAlarm C p [] then (1:ℚ) else 0) ≤
      PublicMerkleProbability.bound Q 0 := by
  have tableBound := PublicMerkleProbability.random_compression_bound
    (fun _ => ∅) Q 0 (by intro log budget; simp) p
  apply le_trans _ tableBound
  apply average_mono
  intro C
  cases hit : lateLinkAlarm C p [] with
  | false =>
    split
    · rename_i impossible; cases impossible
    · split <;> norm_num
  | true =>
    simp only [lateLinkAlarm_implies_table_alarm C p [] hit,↓reduceIte]
    norm_num

set_option backward.isDefEq.respectTransparency false in
/-- All adaptive Program continuations and all uncached construction internals
are charged. The explicit factor four is conservative and actually derived. -/
theorem actual_mode_lateLink_probability {R : Type} (iv : Digest32) (program : Program R)
    (Q : Nat) (counted : Counts Q program) :
    average (fun C : PrimitiveOracle =>
      if lateLinkAlarm C (compile iv program Q counted) [] then (1:ℚ) else 0) ≤
      min 1 (4*(Q.choose 2 : ℚ)/2^256) := by
  apply le_min
  · calc
      _ ≤ average (fun _ : PrimitiveOracle => (1:ℚ)) := by
        apply average_mono
        intro C
        split <;> norm_num
      _ = 1 := average_const _
  · have h := actual_lateLink_probability (compile iv program Q counted)
    have ledger : PublicMerkleProbability.bound Q 0 = 4*(Q.choose 2 : ℚ)/2^256 := by
      rw [Nat.cast_choose_two]
      unfold PublicMerkleProbability.bound
      push_cast
      ring
    simpa only [ledger] using h

#print axioms lateLinkAlarm_implies_table_alarm
#print axioms actual_mode_lateLink_probability
end Whir.PublicCompressionCoupling
