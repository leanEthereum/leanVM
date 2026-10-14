import Whir.PCSRoundByRoundTranscriptReplay
import Whir.PCSRoundByRoundKnowledgeLedger

/-! The initial query's extra knowledge events inspect the already advertised OOD values, prior folded state and candidate list, but not the response to their own query/lambda draw. -/
namespace Whir.PCSRoundByRoundTranscriptState
open Concrete Protocol CausalGame CausalExecution CausalProbability CausalStrategy
open ParameterBounds SupportedCandidateProtocol PCSRoundByRoundKnowledge ExecutionShapes
open CausalPositions

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem initial_query_history (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (left right : Array Reply) (t : Tape (config p))
    (same : ∀ n, n < position (.query (initialLevel p)) → left[n]! = right[n]!) :
    CausalBoundary.boundary (Input p lanes root claims) (indexedStrategy left) t (initialLevel p) =
      CausalBoundary.boundary (Input p lanes root claims) (indexedStrategy right) t (initialLevel p) ∧
    followingCandidates (Input p lanes root claims) (indexedStrategy left) t 0 =
      followingCandidates (Input p lanes root claims) (indexedStrategy right) t 0 ∧
    (proof (Input p lanes root claims) (indexedStrategy left) t).levels[0]!.oods =
      (proof (Input p lanes root claims) (indexedStrategy right) t).levels[0]!.oods := by
  let input := Input p lanes root claims
  let i := initialLevel p
  have boundaryPast (n : Nat) (bound : n < levelStart (challenges (config p) t) 0 + (config p).folds[0]!) :
      left[n]! = right[n]! := by
    apply same n
    rw [position_query (initialLevel p) t]
    simp only
    omega
  have folded := CausalStrategy.foldAt_eq input left right t i (config p).folds[0]!
    (by simp only [i]; exact le_rfl) boundaryPast
  have following := CausalStrategy.followingCandidates_eq input left right t i boundaryPast
  have oods := CausalStrategy.proof_oods_eq input left right t i same
  refine ⟨?_, ?_, ?_⟩
  · simpa only [CausalBoundary.boundary, input, i] using folded
  · simpa only [input, i, initialLevel] using following
  · simpa only [input, i, initialLevel] using oods

theorem targetAt_indexed_congr (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (left right : Array Reply) (t : Tape (config p))
    (same : ∀ n, n < position (.query (initialLevel p)) → left[n]! = right[n]!)
    (target : Array E) : TargetAt p lanes root claims (indexedStrategy left) t target ↔
      TargetAt p lanes root claims (indexedStrategy right) t target := by
  have history := initial_query_history p lanes root claims left right t same
  unfold TargetAt
  rw [history.2.1, history.2.2]

theorem lowSupport_indexed_congr (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (left right : Array Reply) (t : Tape (config p))
    (same : ∀ n, n < position (.query (initialLevel p)) → left[n]! = right[n]!) :
    LowSupportQuery p lanes root claims (indexedStrategy left) t ↔
      LowSupportQuery p lanes root claims (indexedStrategy right) t := by
  unfold LowSupportQuery
  apply exists_congr
  intro target
  rw [targetAt_indexed_congr p lanes root claims left right t same]

theorem collision_indexed_congr (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (left right : Array Reply) (t : Tape (config p))
    (same : ∀ n, n < position (.query (initialLevel p)) → left[n]! = right[n]!) :
    CollisionEvent p lanes root claims (indexedStrategy left) t ↔
      CollisionEvent p lanes root claims (indexedStrategy right) t := by
  have history := initial_query_history p lanes root claims left right t same
  have oracle : (levelAt (Input p lanes root claims) (indexedStrategy left) t 0).oracle =
      (levelAt (Input p lanes root claims) (indexedStrategy right) t 0).oracle := by
    rw [CausalExecution.levelAt_zero, CausalExecution.levelAt_zero]
    rfl
  unfold CollisionEvent RewindBatchTarget.Collision
  rw [oracle, history.1, history.2.1]
  apply exists_congr
  intro candidate
  have poly := queryPolynomial_oods_congr (remaining (config p) 0) (config p).rates[0]!
    (config p).queries[0]! 0
    (levelAt (Input p lanes root claims) (indexedStrategy right) t 0).oracle
    (challenges (config p) t).levels[0]!
    (proof (Input p lanes root claims) (indexedStrategy left) t).levels[0]!
    (proof (Input p lanes root claims) (indexedStrategy right) t).levels[0]!
    (CausalBoundary.boundary (Input p lanes root claims) (indexedStrategy right) t (initialLevel p)).state
    (get (.query (initialLevel p)) t).1 candidate history.2.2
  rw [poly]

theorem extra_indexed_congr (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (left right : Array Reply) (q : Coordinate (config p)) (t : Tape (config p))
    (same : ∀ n, n < position q → left[n]! = right[n]!) :
    extraBad p lanes root claims (indexedStrategy left) q t ↔
      extraBad p lanes root claims (indexedStrategy right) q t := by
  cases q with
  | fold i j =>
    unfold extraBad
    dsimp only
    split_ifs with first
    · subst i
      dsimp only
      rw [rawMCA_indexed_congr (Input p lanes root claims) left right t (initialLevel p) j same,
        claimEscape_indexed_congr (Input p lanes root claims) left right t (initialLevel p) j same]
    · rfl
  | query i =>
    by_cases first : i = initialLevel p
    · subst i
      unfold extraBad
      rw [collision_indexed_congr p lanes root claims left right t same,
        lowSupport_indexed_congr p lanes root claims left right t same]
    · simp only [extraBad, first, false_and]
  | initial => rfl
  | ood i j => rfl
  | tail j => rfl

theorem round_indexed_congr (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (left right : Array Reply) (q : Coordinate (config p)) (t : Tape (config p))
    (same : ∀ n, n < position q → left[n]! = right[n]!) :
    roundBad p lanes root claims (indexedStrategy left) q t ↔
      roundBad p lanes root claims (indexedStrategy right) q t := by
  unfold roundBad
  rw [core_indexed_congr (Input p lanes root claims) left right q t same,
    extra_indexed_congr p lanes root claims left right q t same]

#print axioms initial_query_history
#print axioms targetAt_indexed_congr
#print axioms lowSupport_indexed_congr
#print axioms collision_indexed_congr
#print axioms extra_indexed_congr
#print axioms round_indexed_congr
end Whir.PCSRoundByRoundTranscriptState
