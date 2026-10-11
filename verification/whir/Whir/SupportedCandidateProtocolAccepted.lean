import Whir.SupportedCandidateProtocolHeavy
import Whir.SupportedCandidateProtocolProbability

/-! Derived deterministic interfaces for safe accepted FULL suffix resets.
No advertised-value correctness or acceptance bad-event cover is assumed. -/
namespace Whir.SupportedCandidateProtocol
open Concrete Protocol CausalGame CausalExecution CausalProbability ExecutionShapes
open CandidateFolding SupportedCandidateExtraction ParameterBounds InitialKnowledgeSchedule
open AuthenticatedResetSupport RewindBatchTarget
set_option maxRecDepth 100000
set_option maxHeartbeats 400000
attribute [local irreducible] ParameterBounds.config

theorem production_initial_next : ∀ p : Profile, 1 < (config p).folds.size := by
  decide +kernel

abbrev firstOOD (p : Profile) : Fin (oodCount (config p) 0) :=
  ⟨0, production_ood_positive p (initialLevel p) (production_initial_next p)⟩

def reset (p : Profile) (base fresh : Tape (config p))
    (draw : Sample (.query (initialLevel p))) : Tape (config p) :=
  set (.query (initialLevel p)) (resetSuffix (position (.query (initialLevel p))) base fresh) draw

/-- A single safe accepted continuation derives the prefix's unique advertised
OOD target and true boundary claim, plus all immutable guards. Arbitrary
malicious OOD answers with no matching target admit no such continuation. -/
theorem accepted_safe_target (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (base fresh : Tape (config p))
    (draw : Sample (.query (initialLevel p)))
    (accepted : experiment (Input p lanes root claims) strategy (reset p base fresh draw) = true)
    (safe : ¬ KnowledgeBad p lanes root claims strategy (reset p base fresh draw)) :
    ∃ target : Array E,
      Target (followingCandidates (Input p lanes root claims) strategy base 0)
        (challenges (config p) base).levels[0]!.oodPoints[0]!
        (proof (Input p lanes root claims) strategy base).levels[0]!.oods[0]!.value target ∧
      LevelBoundary.Separated (followingCandidates (Input p lanes root claims) strategy base 0)
        (challenges (config p) base).levels[0]!.oodPoints[0]! ∧
      target.size = width (config p) ∧
      dot target (CausalBoundary.boundary (Input p lanes root claims) strategy base (initialLevel p)).state.weight =
        (CausalBoundary.boundary (Input p lanes root claims) strategy base (initialLevel p)).state.claim ∧
      PriorGood p lanes root claims strategy base ∧
      oracleValid (liftRoot root) (length (config p) 0) lanes = true ∧
      lanes ≤ 2 ^ (config p).folds[0]! := by
  let input := Input p lanes root claims
  let i := initialLevel p
  let t := reset p base fresh draw
  have causal : ∀ q, ¬ CausalBadEvents.Bad input strategy q t := by
    intro q bad
    exact safe (Or.inl ⟨q, bad⟩)
  have collision : ¬ CollisionEvent p lanes root claims strategy t := by
    intro bad
    exact safe (Or.inr (Or.inr (Or.inr bad)))
  have collisionPrior := (collisionEvent_set p lanes root claims strategy
    (resetSuffix (position (.query i)) base fresh) draw).not.mp collision
  obtain ⟨target, matching, truth⟩ := Root0FixedTarget.accepted_reset_target_exists p lanes root claims
    strategy (resetSuffix (position (.query i)) base fresh) i (production_initial_next p) draw
    accepted causal collisionPrior
  have fixed := Root0FixedTarget.snapshot_fullReset input strategy base fresh i draw
  have suffixFixed := Root0FixedTarget.snapshot_resetCoordinates input strategy base fresh i
    (visibleCoordinates input.config ++ List.ofFn (fun j : Fin (input.config.logN-input.config.folds.toList.sum) => Coordinate.tail j))
  change Root0FixedTarget.snapshot input strategy (resetSuffix (position (.query i)) base fresh) i =
    Root0FixedTarget.snapshot input strategy base i at suffixFixed
  have list := congrArg (fun s => s.1) suffixFixed
  have boundary := congrArg (fun s => s.2.1) suffixFixed
  have answers := congrArg (fun s => s.2.2.2.1) suffixFixed
  have points := congrArg (fun s => s.2.2.2.2.2) suffixFixed
  dsimp only [Root0FixedTarget.snapshot] at list boundary answers points
  have matchingBase : Target (followingCandidates input strategy base i)
      (challenges (config p) base).levels[i.val]!.oodPoints[0]!
      (proof input strategy base).levels[i.val]!.oods[0]!.value target := by
    unfold Target at matching ⊢
    rw [list, points, answers] at matching
    exact matching
  have separated : LevelBoundary.Separated (followingCandidates input strategy t i)
      (challenges (config p) t).levels[i.val]!.oodPoints[0]! := by
    by_contra bad
    exact causal (.ood i (firstOOD p)) bad
  have separatedBase : LevelBoundary.Separated (followingCandidates input strategy base i)
      (challenges (config p) base).levels[i.val]!.oodPoints[0]! := by
    have list := congrArg (fun s => s.1) fixed
    have points := congrArg (fun s => s.2.2.2.2.2) fixed
    dsimp only [Root0FixedTarget.snapshot] at list points
    unfold t reset at separated
    rw [list, points] at separated
    exact separated
  have size := CausalBoundary.followingCandidates_sizes input strategy base p rfl i
    (by intro impossible; exact (impossible (production_initial_next p)).elim) target matchingBase.1
  have prior := priorGood_of_not_bad p lanes root claims strategy t safe
  have basePrior : PriorGood p lanes root claims strategy base := by
    unfold t reset at prior
    rw [priorGood_set p lanes root claims strategy _ (.query i) _ le_rfl] at prior
    exact (priorGood_resetCoordinates p lanes root claims strategy base fresh _).mp prior
  have valid := AcceptedShapes.accepted_oracle p lanes root claims strategy t accepted i
  have laneBound := AcceptedShapes.accepted_lane_bound input strategy t accepted
  refine ⟨target, matchingBase, separatedBase, ?_, ?_, basePrior, ?_, laneBound⟩
  · simpa only [input, i, initialLevel, width, (InitialCandidates.production_initial_facts p).1] using size
  · change dot target
      (CausalBoundary.boundary input strategy (resetSuffix (position (.query i)) base fresh) i).state.weight =
        (CausalBoundary.boundary input strategy (resetSuffix (position (.query i)) base fresh) i).state.claim at truth
    rw [boundary] at truth
    exact truth
  · simpa only [i, initialLevel, levelAt_zero, initial, beq_self_eq_true, ↓reduceIte] using valid

/-- Every other safe accepted full reset hits this same prefix-fixed target,
including when all future folds, OODs, queries and tail coins are replaced. -/
theorem accepted_safe_hits (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (base fresh : Tape (config p))
    (draw : Sample (.query (initialLevel p))) (target : Array E)
    (matching : Target (followingCandidates (Input p lanes root claims) strategy base 0)
      (challenges (config p) base).levels[0]!.oodPoints[0]!
      (proof (Input p lanes root claims) strategy base).levels[0]!.oods[0]!.value target)
    (separated : LevelBoundary.Separated (followingCandidates (Input p lanes root claims) strategy base 0)
      (challenges (config p) base).levels[0]!.oodPoints[0]!)
    (accepted : experiment (Input p lanes root claims) strategy (reset p base fresh draw) = true)
    (safe : ¬ KnowledgeBad p lanes root claims strategy (reset p base fresh draw)) :
    SamplingProbability.allQueriesHit (remaining (config p) 0 + (config p).rates[0]!) (config p).queries[0]!
      (LevelBoundary.agreeingColumns (remaining (config p) 0) (config p).rates[0]! target
        (QueryBatchSoundness.oldWord (remaining (config p) 0) (config p).rates[0]!
          (liftRoot root) true (challenges (config p) base).levels[0]!.folds)) draw.1 := by
  have causal : ∀ q, ¬ CausalBadEvents.Bad (Input p lanes root claims) strategy q (reset p base fresh draw) := by
    intro q bad
    exact safe (Or.inl ⟨q, bad⟩)
  have outside : ¬ CollisionEvent p lanes root claims strategy (reset p base fresh draw) := by
    intro bad
    exact safe (Or.inr (Or.inr (Or.inr bad)))
  have collision := (collisionEvent_set p lanes root claims strategy
    (resetSuffix (position (.query (initialLevel p))) base fresh) draw).not.mp outside
  exact Root0FixedTarget.accepted_full_reset_hits p lanes root claims strategy base fresh
    (initialLevel p) (production_initial_next p) draw target matching separated accepted causal collision

#print axioms accepted_safe_target
#print axioms accepted_safe_hits
end Whir.SupportedCandidateProtocol
