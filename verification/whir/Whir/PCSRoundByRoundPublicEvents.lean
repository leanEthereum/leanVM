import Whir.PCSRoundByRoundPublicTrace
import Whir.PCSRoundByRoundKnowledgeLedger

/-! Concrete RBR events are insensitive to a hidden strategy once its public replies are fixed, and to challenge coordinates after their own boundary. -/
namespace Whir.PCSRoundByRoundTranscriptState
open Concrete Protocol CausalGame CausalProbability CausalExecution CausalStrategy
open ParameterBounds SupportedCandidateProtocol PCSRoundByRoundKnowledge ExecutionShapes

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem targetAt_proof_congr (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (left right : Strategy) (t : Tape (config p))
    (same : proof (Input p lanes root claims) left t = proof (Input p lanes root claims) right t)
    (target : Array E) : TargetAt p lanes root claims left t target ↔
      TargetAt p lanes root claims right t target := by
  unfold TargetAt
  rw [following_proof_congr (Input p lanes root claims) left right t same, same]

theorem lowSupport_proof_congr (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (left right : Strategy) (t : Tape (config p))
    (same : proof (Input p lanes root claims) left t = proof (Input p lanes root claims) right t) :
    LowSupportQuery p lanes root claims left t ↔ LowSupportQuery p lanes root claims right t := by
  unfold LowSupportQuery
  apply exists_congr
  intro target
  rw [targetAt_proof_congr p lanes root claims left right t same]

theorem collision_proof_congr (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (left right : Strategy) (t : Tape (config p))
    (same : proof (Input p lanes root claims) left t = proof (Input p lanes root claims) right t) :
    CollisionEvent p lanes root claims left t ↔ CollisionEvent p lanes root claims right t := by
  unfold CollisionEvent
  rw [level_proof_congr (Input p lanes root claims) left right t same, same,
    boundary_proof_congr (Input p lanes root claims) left right t same,
    following_proof_congr (Input p lanes root claims) left right t same]

theorem extra_proof_congr (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (left right : Strategy) (t : Tape (config p))
    (same : proof (Input p lanes root claims) left t = proof (Input p lanes root claims) right t)
    (q : Coordinate (config p)) : extraBad p lanes root claims left q t ↔
      extraBad p lanes root claims right q t := by
  cases q with
  | fold i j =>
    unfold extraBad
    dsimp only
    split_ifs
    · rw [rawMCA_proof_congr (Input p lanes root claims) left right t same,
        claimEscape_proof_congr (Input p lanes root claims) left right t same]
    · rfl
  | query i =>
    unfold extraBad
    rw [collision_proof_congr p lanes root claims left right t same,
      lowSupport_proof_congr p lanes root claims left right t same]
  | initial => rfl
  | ood i j => rfl
  | tail j => rfl

theorem round_proof_congr (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (left right : Strategy) (t : Tape (config p))
    (same : proof (Input p lanes root claims) left t = proof (Input p lanes root claims) right t)
    (q : Coordinate (config p)) : roundBad p lanes root claims left q t ↔
      roundBad p lanes root claims right q t := by
  unfold roundBad
  rw [core_proof_congr (Input p lanes root claims) left right t same,
    extra_proof_congr p lanes root claims left right t same]

theorem round_prefix_congr (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (q : Coordinate (config p))
    (t u : Tape (config p))
    (same : ∀ r, position r ≤ position q → get r t = get r u) :
    roundBad p lanes root claims strategy q t ↔ roundBad p lanes root claims strategy q u := by
  exact prefix_event_congr (roundBad p lanes root claims strategy q) q
    (fun r tape draw later => roundBad_set_future p lanes root claims strategy q r tape draw later)
    t u same

#print axioms targetAt_proof_congr
#print axioms lowSupport_proof_congr
#print axioms collision_proof_congr
#print axioms extra_proof_congr
#print axioms round_proof_congr
#print axioms round_prefix_congr
end Whir.PCSRoundByRoundTranscriptState
