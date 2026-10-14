import Whir.PCSRoundByRoundKnowledgeState
import Whir.PCSRoundByRoundKnowledgeLedger
import Whir.PCSRoundByRoundKnowledgeRecovery
import Whir.PCSRewindKnowledgeOriginalChance
import Whir.PCSRoundByRoundSourceDecoderCost

/-! The ideal additive characteristic-two source IOP's causal RBR knowledge
endpoint. This is not the interactive reset extractor and not a BCS, Merkle,
Fiat-Shamir, or duplex transport theorem. Extractor inputs are the immutable
original public statement and the prover's full Root0 string only. -/
namespace Whir.PCSRoundByRoundKnowledge
open Concrete Protocol CausalGame CausalProbability ParameterBounds
open PCSRoundByRoundSource
open scoped BigOperators
open Classical

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
attribute [local irreducible] ParameterBounds.config
attribute [local irreducible] roundBad RingPCSGame.Escape

private theorem uniform_implication {A : Type} [Fintype A] (P Q : A → Prop)
    [DecidablePred P] [DecidablePred Q] (cover : ∀ x, P x → Q x) :
    Soundness.uniformProb (Finset.univ.filter P) ≤
      Soundness.uniformProb (Finset.univ.filter Q) := by
  unfold Soundness.uniformProb
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (show Finset.univ.filter P ⊆ Finset.univ.filter Q from
    fun x member => Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, cover x (Finset.mem_filter.mp member).2⟩)

section Source
variable {m : Nat} (p : Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : OriginalClaimsChecker.Prepared (config p) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy)

/-- There is no verifier randomness, strategy, transcript suffix, or reset
access in the implemented straight-line extractor's type. -/
def extract : Option (Witness (config p) lanes) :=
  PCSRoundByRoundSource.run p lanes family points anchorPoint anchorValue root

noncomputable def sourceState (ringSeen : Bool) (completed : Finset (Coordinate (config p)))
    (publicPrefix : RingPCSGame.Prefix) (t : Tape (config p)) : Bool :=
  if ringSeen = true ∧ RingPCSGame.Escape (config p) lanes root family publicPrefix then true else
    state (roundBad p lanes root (OriginalClaimsChecker.input prepared root publicPrefix).claims
      (strategy publicPrefix)) completed t
attribute [local irreducible] sourceState

@[simp] theorem sourceState_initial (publicPrefix : RingPCSGame.Prefix) (t : Tape (config p)) :
    sourceState p lanes family points anchorPoint anchorValue prepared root strategy false ∅ publicPrefix t = false := by
  simp [sourceState]

/-- Physical rectangularity is an actual accepting-verifier guard, not an
availability assumption or an honest-root equality. -/
theorem accepted_root_shape (publicPrefix : RingPCSGame.Prefix) (t : Tape (config p))
    (accepted : experiment (OriginalClaimsChecker.input prepared root publicPrefix) (strategy publicPrefix) t = true) :
    FullRoot (config p) lanes root := by
  let claims := (OriginalClaimsChecker.input prepared root publicPrefix).claims
  let i := SupportedCandidateProtocol.initialLevel p
  have valid : oracleValid (liftRoot root) (length (config p) 0) lanes = true := by
    simpa only [i, SupportedCandidateProtocol.initialLevel, CausalExecution.levelAt_zero,
      CausalExecution.initial, beq_self_eq_true, ↓reduceIte] using
      AcceptedShapes.accepted_oracle p lanes root claims (strategy publicPrefix) t accepted i
  have shape := valid
  simp only [oracleValid, Bool.and_eq_true, beq_iff_eq, liftRoot, Array.size_map] at shape
  have lengthEq : length (config p) 0 = SupportedCandidateExtraction.blockLength (config p) := by
    have dims : remaining (config p) 0 = (config p).logN - (config p).folds[0]! :=
      (InitialCandidates.production_initial_facts p).1
    change 2 ^ (remaining (config p) 0 + (config p).rates[0]!) =
      2 ^ ((config p).logN - (config p).folds[0]! + (config p).rates[0]!)
    rw [dims]
  refine ⟨shape.1.trans lengthEq, ?_⟩
  intro j
  have row := OracleReplay.oracleValid_row _ _ _ valid j.val (j.isLt.trans_eq shape.1)
  simpa [liftRoot, getElem!_pos, j.isLt] using row

/-- Acceptance together with failure of the actual implemented full-root
extractor implies final state one. All original slices, ordinary/strided point
claims and the saved original anchor occur in the conclusion's relation. -/
theorem accepted_extraction_failure_final
    (familyCap : m ≤ 2^64) (pointCap : points.size ≤ 2^64) (full : FullRoot (config p) lanes root)
    (publicPrefix : RingPCSGame.Prefix) (t : Tape (config p))
    (accepted : experiment (OriginalClaimsChecker.input prepared root publicPrefix) (strategy publicPrefix) t = true)
    (failure : ¬ ∃ w, extract p lanes family points anchorPoint anchorValue root = some w ∧
      PCSRewindSource.ExplainsOriginal (config p) lanes root family points anchorPoint anchorValue w) :
    sourceState p lanes family points anchorPoint anchorValue prepared root strategy true Finset.univ publicPrefix t = true := by
  classical
  by_cases ringBad : RingPCSGame.Escape (config p) lanes root family publicPrefix
  · simp [sourceState, ringBad]
  · by_cases any : ∃ q, roundBad p lanes root (OriginalClaimsChecker.input prepared root publicPrefix).claims
        (strategy publicPrefix) q t
    · simp only [sourceState, ringBad, and_false, ↓reduceIte]
      exact (state_final _ t).mpr any
    · have safe : ¬ SupportedCandidateProtocol.KnowledgeBad p lanes root
          (OriginalClaimsChecker.input prepared root publicPrefix).claims (strategy publicPrefix) t :=
        fun bad => any (knowledgeBad_cover _ _ _ _ _ _ bad)
      have notLow : ¬ LowSupportQuery p lanes root (OriginalClaimsChecker.input prepared root publicPrefix).claims
          (strategy publicPrefix) t := fun low => any ⟨_, lowSupport_cover _ _ _ _ _ _ low⟩
      exact (failure (accepted_safe_run p lanes family points anchorPoint anchorValue prepared root publicPrefix
        (strategy publicPrefix) t familyCap pointCap full accepted ringBad safe notLow)).elim

/-- Actual accepting-path endpoint: rectangularity is derived from the verifier
guard. No availability, safe-event cover, or RBR-soundness premise remains. -/
theorem accepted_extraction_failure_final_actual
    (familyCap : m ≤ 2^64) (claimCap : points.size + 2 ≤ 2^64)
    (publicPrefix : RingPCSGame.Prefix) (t : Tape (config p))
    (accepted : experiment (OriginalClaimsChecker.input prepared root publicPrefix) (strategy publicPrefix) t = true)
    (failure : ¬ ∃ w, extract p lanes family points anchorPoint anchorValue root = some w ∧
      PCSRewindSource.ExplainsOriginal (config p) lanes root family points anchorPoint anchorValue w) :
    sourceState p lanes family points anchorPoint anchorValue prepared root strategy true Finset.univ publicPrefix t = true :=
  accepted_extraction_failure_final p lanes family points anchorPoint anchorValue prepared root strategy
    familyCap (by omega) (accepted_root_shape p lanes family points anchorPoint anchorValue prepared root strategy
      publicPrefix t accepted) publicPrefix t accepted failure

open Classical in
/-- Ring gamma and the six actual map scalars are one grouped public-coin
message: no prover string is sent between them. Root0 and original metadata
are fixed before this message, while the subsequent strategy may depend on it. -/
theorem ring_conditional_transition (t : Tape (config p)) (failure : RingPCSGame.Prefix → Prop) :
    Soundness.uniformProb (Finset.univ.filter fun publicPrefix : RingPCSGame.Prefix =>
      failure publicPrefix ∧ sourceState p lanes family points anchorPoint anchorValue prepared root strategy
        true ∅ publicPrefix t = true) ≤ PCSRewindSource.ringEscapeLoss m := by
  apply le_trans ?_ (RingPCSGame.escape_probability p lanes root family)
  apply uniform_implication
  intro publicPrefix event
  by_contra absent
  have doomed := event.2
  simp [sourceState, absent] at doomed

open Classical in
/-- The exact Def31.1.6 fiber: arbitrary fixed previous public history, state
zero before the fresh message, arbitrary subsequent malicious continuation and
extractor failure. The bound is conditional, not a whole-game marginal. -/
theorem source_conditional_transition
    (completed : Finset (Coordinate (config p))) (q : Coordinate (config p))
    (publicPrefix : RingPCSGame.Prefix) (t : Tape (config p)) (failure : Sample q → Prop)
    (earlier : ∀ r ∈ completed, position r < position q)
    (before : sourceState p lanes family points anchorPoint anchorValue prepared root strategy
      true completed publicPrefix t = false) :
    Soundness.uniformProb (Finset.univ.filter fun x : Sample q => failure x ∧
      sourceState p lanes family points anchorPoint anchorValue prepared root strategy
        true (insert q completed) publicPrefix (set q t x) = true) ≤
      epsilon p lanes root (OriginalClaimsChecker.input prepared root publicPrefix).claims q := by
  have ringSafe : ¬ RingPCSGame.Escape (config p) lanes root family publicPrefix := by
    intro bad
    simp [sourceState, bad] at before
  have bodyBefore : state (roundBad p lanes root (OriginalClaimsChecker.input prepared root publicPrefix).claims
      (strategy publicPrefix)) completed t = false := by
    simpa only [sourceState, ringSafe, and_false, ↓reduceIte] using before
  simp only [sourceState, ringSafe, and_false, ↓reduceIte]
  apply conditional_state_transition _ completed q t failure _ bodyBefore
  · intro r member x
    exact roundBad_set_future p lanes root (OriginalClaimsChecker.input prepared root publicPrefix).claims
      (strategy publicPrefix) r q t x (earlier r member)
  · exact roundBad_fiber_bound p lanes root (OriginalClaimsChecker.input prepared root publicPrefix).claims
      (strategy publicPrefix) prepared.guards.2.2.2.1 (PCSRewindSource.input_shapes prepared root publicPrefix) q t

theorem source_conditional_transition_uniform
    (claimCap : points.size + 2 ≤ 2^64)
    (completed : Finset (Coordinate (config p))) (q : Coordinate (config p))
    (publicPrefix : RingPCSGame.Prefix) (t : Tape (config p)) (failure : Sample q → Prop)
    (earlier : ∀ r ∈ completed, position r < position q)
    (before : sourceState p lanes family points anchorPoint anchorValue prepared root strategy
      true completed publicPrefix t = false) :
    Soundness.uniformProb (Finset.univ.filter fun x : Sample q => failure x ∧
      sourceState p lanes family points anchorPoint anchorValue prepared root strategy
        true (insert q completed) publicPrefix (set q t x) = true) ≤ rbrError :=
  (source_conditional_transition p lanes family points anchorPoint anchorValue prepared root strategy
    completed q publicPrefix t failure earlier before).trans
    (epsilon_le_rbrError p lanes root (OriginalClaimsChecker.input prepared root publicPrefix).claims
      (by simpa only [PCSRewindSource.input_size] using claimCap) q)

theorem ring_conditional_transition_uniform (familyCap : m ≤ 2^64)
    (t : Tape (config p)) (failure : RingPCSGame.Prefix → Prop) :
    Soundness.uniformProb (Finset.univ.filter fun publicPrefix : RingPCSGame.Prefix =>
      failure publicPrefix ∧ sourceState p lanes family points anchorPoint anchorValue prepared root strategy
        true ∅ publicPrefix t = true) ≤ rbrError := by
  apply (ring_conditional_transition p lanes family points anchorPoint anchorValue prepared root strategy t failure).trans
  apply (PCSRewindSource.ringEscapeLoss_le m familyCap).trans
  norm_num [rbrError, SupportedCandidateExtraction.radiusEnvelope]

/-- Exact loss for the unchanged first wire message: gamma, six map scalars,
and the initial stacking lambda form one grouped eight-field draw. -/
noncomputable def initialLoss : ℚ := PCSRewindSource.ringEscapeLoss m +
  GroupedChallenges.initialBatch (config p) (estimates (config p)) (points.size + 2)

theorem initial_grouped_transition (t : Tape (config p))
    (failure : RingPCSGame.Prefix × E → Prop) :
    Soundness.uniformProb (Finset.univ.filter fun draw : RingPCSGame.Prefix × E =>
      failure draw ∧ sourceState p lanes family points anchorPoint anchorValue prepared root strategy
        true {.initial} draw.1 (set .initial t draw.2) = true) ≤ initialLoss (m := m) p points := by
  let ring : RingPCSGame.Prefix × E → Prop := fun draw =>
    RingPCSGame.Escape (config p) lanes root family draw.1
  let initialBad : RingPCSGame.Prefix × E → Prop := fun draw =>
    roundBad p lanes root (OriginalClaimsChecker.input prepared root draw.1).claims
      (strategy draw.1) .initial (set .initial t draw.2)
  have ringBound : Soundness.uniformProb (Finset.univ.filter ring) ≤ PCSRewindSource.ringEscapeLoss m := by
    have law := AuthenticatedResetProbability.product_left (B := E)
      (RingPCSGame.Escape (config p) lanes root family)
    rw [SamplingProbability.probability_eq_uniformProb,
      SamplingProbability.probability_eq_uniformProb] at law
    have exactLaw := (Rat.cast_inj (α := ℝ)).mp law
    exact exactLaw.trans_le (RingPCSGame.escape_probability p lanes root family)
  have initialBound : Soundness.uniformProb (Finset.univ.filter initialBad) ≤
      GroupedChallenges.initialBatch (config p) (estimates (config p)) (points.size + 2) := by
    rw [RingMapBatching.uniform_product initialBad]
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < Fintype.card RingPCSGame.Prefix)).mpr
    calc
      _ ≤ ∑ _publicPrefix : RingPCSGame.Prefix,
          GroupedChallenges.initialBatch (config p) (estimates (config p)) (points.size + 2) := by
        apply Finset.sum_le_sum
        intro publicPrefix _
        have fiber := roundBad_fiber_bound p lanes root
          (OriginalClaimsChecker.input prepared root publicPrefix).claims (strategy publicPrefix)
          prepared.guards.2.2.2.1 (PCSRewindSource.input_shapes prepared root publicPrefix) .initial t
        simpa only [initialBad, epsilon, extraLoss, CausalBadEvents.localError,
          ExecutionShapes.Input, PCSRewindSource.input_size, add_zero] using fiber
      _ = _ := by simp [mul_comm]
  apply le_trans ?_ (InitialKnowledgeSchedule.uniform_or_bound ring initialBad _ _ ringBound initialBound)
  apply uniform_implication
  intro draw event
  have doomed := event.2
  by_cases escaped : ring draw
  · exact Or.inl escaped
  · apply Or.inr
    simpa only [sourceState, ring, escaped, and_false, ↓reduceIte, state,
      Finset.mem_singleton, exists_eq_left, ite_eq_left_iff,
      Bool.false_eq_true, imp_false, not_not, initialBad] using doomed

theorem initialLoss_le_rbrError (familyCap : m ≤ 2^64) (claimCap : points.size + 2 ≤ 2^64) :
    initialLoss (m := m) p points ≤ rbrError := by
  have ring := PCSRewindSource.ringEscapeLoss_le m familyCap
  have initial := (le_max_left
    (GroupedChallenges.initialBatch (config p) (estimates (config p)) (points.size + 2)) _).trans
    (production_grouped p (points.size + 2) claimCap)
  have radiusNonnegative : (0 : ℚ) ≤ SupportedCandidateExtraction.radiusEnvelope := by
    unfold SupportedCandidateExtraction.radiusEnvelope
    positivity
  unfold initialLoss rbrError
  linarith

/-- The implemented extractor never outputs a word failing the original source
relation; this includes Root0 candidate membership and the literal anchor. -/
theorem extract_output_explains (w : Witness (config p) lanes)
    (output : extract p lanes family points anchorPoint anchorValue root = some w) :
    PCSRewindSource.ExplainsOriginal (config p) lanes root family points anchorPoint anchorValue w :=
  PCSRoundByRoundSource.run_output_explains _ _ _ _ _ _ _ w output

/-- Value-connected polynomial accounting for this very extractor. The actual
Gao backend, original checker and physical root scans are counted; the field
arithmetic term has degree seven. No record search or verifier tape is present. -/
theorem extract_polynomial_cost :
    (PCSRoundByRoundSource.countedRun p lanes family points anchorPoint anchorValue root).1 =
      extract p lanes family points anchorPoint anchorValue root ∧
    (PCSRoundByRoundSource.countedRun p lanes family points anchorPoint anchorValue root).2 ≤
      PCSRoundByRoundSource.resourcePolynomial (SupportedCandidateExtraction.blockLength (config p))
        (SupportedCandidateExtraction.laneCount (config p)) lanes m points.size :=
  ⟨PCSRoundByRoundSource.countedRun_value _ _ _ _ _ _ _,
    PCSRoundByRoundSource.countedRun_polynomial_cost _ _ _ _ _ _ _⟩

end Source

/-- The unchanged first message groups the ring prefix and stacking lambda;
each remaining coordinate is one actual message, including the last tail
draw. The external BCS/ROM budget does not alter this source round count. -/
def k (p : Profile) : Nat := Fintype.card (Coordinate (config p))

theorem k_exact (p : Profile) :
    k p = 1 + (∑ i : Fin (config p).folds.size,
      ((config p).folds[i.val]! + oodCount (config p) i.val + 1)) +
      ((config p).logN - (config p).folds.toList.sum) := by
  unfold k
  rw [Fintype.card_congr (Coordinate.proxyTypeEquiv (config p)).symm]
  simp only [Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin, Fintype.card_unit]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_id]
  omega

#print axioms accepted_extraction_failure_final
#print axioms ring_conditional_transition
#print axioms source_conditional_transition
#print axioms extract_output_explains
#print axioms accepted_extraction_failure_final_actual
#print axioms initial_grouped_transition
#print axioms initialLoss_le_rbrError
#print axioms source_conditional_transition_uniform
#print axioms k_exact
#print axioms extract_polynomial_cost
end Whir.PCSRoundByRoundKnowledge
