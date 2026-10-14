import Whir.PCSRoundByRoundPublicState
import Whir.PCSRoundByRoundKnowledge

/-! The literal public trace predicate agrees with the checked source state. Replay and zero filling occur only in this proof bridge, not in the extractor's inputs. -/
namespace Whir.PCSRoundByRoundTranscriptState
open Concrete Protocol CausalGame CausalProbability CausalExecution CausalStrategy
open ParameterBounds SupportedCandidateProtocol PCSRoundByRoundKnowledge ExecutionShapes
open Classical PublicTrace

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem state_replay (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (t : Tape (config p))
    (done : Finset (Coordinate (config p))) :
    state (roundBad p lanes root claims (indexedStrategy (replies (Input p lanes root claims) strategy t))) done t =
      state (roundBad p lanes root claims strategy) done t := by
  have same := proof_replay (Input p lanes root claims) strategy t
  have event : (∃ q ∈ done, roundBad p lanes root claims
      (indexedStrategy (replies (Input p lanes root claims) strategy t)) q t) ↔
      (∃ q ∈ done, roundBad p lanes root claims strategy q t) := by
    apply exists_congr
    intro q
    exact and_congr_right fun _ => round_proof_congr p lanes root claims _ strategy t same q
  unfold state
  simp only [event]

theorem snapshot_publicState_source {m : Nat} (p : Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : OriginalClaimsChecker.Prepared (config p) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy)
    (ring : RingPCSGame.Prefix) (t : Tape (config p)) (boundary : Coordinate (config p)) :
    publicState p lanes family points anchorPoint anchorValue prepared root
      (snapshot ring t (replies (Input p lanes root (OriginalClaimsChecker.input prepared root ring).claims) (strategy ring) t) boundary) =
      sourceState p lanes family points anchorPoint anchorValue prepared root strategy true (past boundary) ring t := by
  unfold publicState sourceState
  simp only [snapshot_ring, true_and]
  split_ifs with bad
  · rfl
  · rw [snapshot_state_congr]
    exact state_replay p lanes root (OriginalClaimsChecker.input prepared root ring).claims
      (strategy ring) t (past boundary)

#print axioms state_replay
#print axioms snapshot_publicState_source
end Whir.PCSRoundByRoundTranscriptState
