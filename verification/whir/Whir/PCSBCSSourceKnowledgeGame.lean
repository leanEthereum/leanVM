import Whir.PCSBCSAdaptiveSourceKnowledgeProbability

/-! Exact PCS-only source compiler instantiation. Counts Q is the existing
aggregate source-work budget: ordinary primitive calls cost one, and each
construction request costs its complete compression path. No equality with a
smaller distinct cached native-compression count is asserted.
An observer endpoint exposes literal native/source witness refinement; it does
not turn that code-refinement obligation into a cryptographic or probability
assumption. The additive RBR source relation is proved, and the only transfer
loss here is the checked 256-bit duplex mode term. Merkle bad events, arbitrary
Rust inputs, concrete BLAKE2s security and whole-system knowledge are separate. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Whir.PCSBCSSourceKnowledgeGame
open Concrete FiatShamirGame DuplexModeGame TypedOracleCompiler RawOracleCoupling
open PCSBCSChallengeOracle PCSStateRestoration.Latent

variable {p : ParameterBounds.Profile} {Q : Nat} {iv : Digest32} {boundary : Nat}
local notation "part" => EnteredPacket.partition
  (p := p) (Q := Q) (iv := iv) (boundary := boundary)
local notation "Keys" => PCSBCSSourceRootCapture.Key
  (p := p) (Q := Q) (iv := iv) (boundary := boundary)
local notation "Answers" => PCSBCSSourceRootCapture.Answer
  (p := p) (Q := Q) (iv := iv) (boundary := boundary)
noncomputable local instance (key : Keys) : Fintype (Answers key) :=
  Restoration.instFintypeAnswer p Q iv boundary key

/-- Same indexed source program used by the checked whole-public-view mode
coupling, with one grouped packet allocation at its first physical disclosure.
Its index is Q, not Q times the number of protocol rounds. -/
noncomputable def source {R : Type} (program : Program R) (counted : Counts Q program) :
    Sampling Keys Answers (View R) Q :=
  Atomic.program (part) (PublicCompressionCouplingMixed.compile Q iv [] program Q (by rfl) counted)

open Classical in
theorem source_failure_probability {R : Type}
    (layout : WHIRCallerClaims.CallerLayout)
    (program : Program R) (counted : Counts Q program) :
    Soundness.uniformProb (Finset.univ.filter fun table : Table Keys Answers =>
      PCSBCSAdaptiveSourceKnowledgeProbability.Failed layout (source program counted) table) ≤
      (Q : ℚ) * PCSRoundByRoundKnowledge.rbrError :=
  PCSBCSAdaptiveSourceKnowledgeProbability.failure_probability layout (source program counted)

private theorem average_indicator {T : Type} [Fintype T] (test : T → Bool) :
    average (fun t => if test t then (1 : ℚ) else 0) =
      Soundness.uniformProb (Finset.univ.filter fun t => test t = true) := by
  classical
  simp only [average,Soundness.uniformProb,Finset.card_filter,Nat.cast_sum,
    Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

/-- Explicit source semantics contract for a whole-view observer. It requires
actual native acceptance, actual extraction failure, independently bound
original preparation and literal native codec/primitive evidence, not a
StatePath, compatible snapshot, bad-probability certificate or soundness premise.
This contract must be discharged for the selected verifier's supported source
inputs before interpreting the observer as deployed acceptance/extraction. -/
def ObserverRefines {R : Type}
    (layout : WHIRCallerClaims.CallerLayout)
    (program : Program R) (counted : Counts Q program) (observe : View R → Bool) : Prop :=
  ∀ table : Table Keys Answers, observe (Sampling.eval table (source program counted)) = true →
    PCSBCSAdaptiveSourceKnowledgeProbability.Failed layout (source program counted) table

open Classical in
theorem source_observer_probability {R : Type}
    (layout : WHIRCallerClaims.CallerLayout)
    (program : Program R) (counted : Counts Q program) (observe : View R → Bool)
    (refines : ObserverRefines (p := p) (iv := iv) (boundary := boundary)
      layout program counted observe) :
    average (fun table : Table Keys Answers =>
      if observe (Sampling.eval table (source program counted)) then (1 : ℚ) else 0) ≤
      (Q : ℚ) * PCSRoundByRoundKnowledge.rbrError := by
  rw [average_indicator]
  have subset : (Finset.univ.filter fun table : Table Keys Answers =>
      observe (Sampling.eval table (source program counted)) = true) ⊆
      (Finset.univ.filter (PCSBCSAdaptiveSourceKnowledgeProbability.Failed layout
        (source program counted))) := by
    intro table member
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,refines table (Finset.mem_filter.mp member).2⟩
  have monotone : Soundness.uniformProb (Finset.univ.filter fun table : Table Keys Answers =>
      observe (Sampling.eval table (source program counted)) = true) ≤
      Soundness.uniformProb (Finset.univ.filter fun table : Table Keys Answers =>
        PCSBCSAdaptiveSourceKnowledgeProbability.Failed layout (source program counted) table) := by
    unfold Soundness.uniformProb
    apply div_le_div_of_nonneg_right
    · exact_mod_cast Finset.card_le_card subset
    · positivity
  exact monotone.trans (source_failure_probability layout program counted)

open Classical in
/-- Actual atomic whole-public-view experiment. Native/source refinement is
explicit for each adversarial coin choice; there is no extra round-query factor. -/
theorem atomic_observer_probability {AdvCoins R : Type}
    [Fintype AdvCoins] [Nonempty AdvCoins]
    (layout : WHIRCallerClaims.CallerLayout)
    (adversary : AdvCoins → Program R) (counted : ∀ a, Counts Q (adversary a))
    (observe : View R → Bool)
    (refines : ∀ a, ObserverRefines (p := p) (iv := iv) (boundary := boundary)
      layout (adversary a) (counted a) observe) :
    atomicIdealProbability (part) iv adversary counted observe ≤
      (Q : ℚ) * PCSRoundByRoundKnowledge.rbrError := by
  unfold atomicIdealProbability
  have each (a : AdvCoins) :
      Sampling.expectation (fun result => if observe result.1 then (1 : ℚ) else 0)
        (RawOracleCoupling.memo (source (p := p) (iv := iv) (boundary := boundary)
          (adversary a) (counted a)) (fun _ => none)) ≤
        (Q : ℚ) * PCSRoundByRoundKnowledge.rbrError := by
    have tableMemo := RawOracleCoupling.empty_table_eq_memo
      (source (p := p) (iv := iv) (boundary := boundary) (adversary a) (counted a))
      (fun view => if observe view then (1 : ℚ) else 0)
    rw [← tableMemo]
    exact source_observer_probability layout (adversary a) (counted a) observe (refines a)
  have summed := average_mono each
  rw [average_const] at summed
  convert summed using 1
  congr 1
  funext a
  unfold source
  congr 2 <;> exact Subsingleton.elim _ _

open Classical in
/-- Transfer of an explicitly refined PCS source observer to random compression.
This bounds the good native-source event only: the omitted Merkle bad events
must still be included before claiming an overall PCS knowledge theorem. It
is not concrete BLAKE2s security, universal Rust refinement or whole-system knowledge. -/
theorem random_compression_observer_probability {AdvCoins R : Type}
    [Fintype AdvCoins] [Nonempty AdvCoins]
    (layout : WHIRCallerClaims.CallerLayout)
    (adversary : AdvCoins → Program R) (counted : ∀ a, Counts Q (adversary a))
    (observe : View R → Bool)
    (refines : ∀ a, ObserverRefines (p := p) (iv := iv) (boundary := boundary)
      layout (adversary a) (counted a) observe) :
    realProbability iv adversary observe ≤
      (Q : ℚ) * PCSRoundByRoundKnowledge.rbrError + duplexModeLoss Q := by
  have coupling := entered_source_atomic_game_bound p Q iv boundary adversary counted observe
  have deviation := (abs_le.mp coupling).2
  have ideal := atomic_observer_probability layout adversary counted observe refines
  linarith

#print axioms atomic_observer_probability
#print axioms random_compression_observer_probability

#print axioms source_failure_probability
#print axioms source_observer_probability
end Whir.PCSBCSSourceKnowledgeGame
