import Whir.PCSRoundByRoundPublicEndpoint
import Whir.PCSBCSRounds

/-! A noninitial message updates the literal public predicate on its exact uniform incoming-history fiber. Both trace snapshots stop before the following prover response. -/
namespace Whir.PCSRoundByRoundTranscriptState
open Concrete Protocol CausalGame CausalProbability CausalExecution CausalStrategy
open ParameterBounds SupportedCandidateProtocol PCSRoundByRoundKnowledge ExecutionShapes
open Classical PublicTrace CausalPositions CausalPrefix

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def predecessor {c : Config} (q : Coordinate c) (positive : 0 < position q) : Coordinate c :=
  PCSBCSRounds.rounds c ⟨position q - 1, by
    have bound : position q < PCSBCSRounds.k c := by
      simpa only [PCSBCSRounds.depth_eq_k] using WHIRHistory.position_lt_depth q
    omega⟩

theorem predecessor_position {c : Config} (q : Coordinate c) (positive : 0 < position q) :
    position (predecessor q positive) = position q - 1 := by
  let index : Fin (PCSBCSRounds.k c) := ⟨position q - 1, by
    have bound : position q < PCSBCSRounds.k c := by
      simpa only [PCSBCSRounds.depth_eq_k] using WHIRHistory.position_lt_depth q
    omega⟩
  have inverse := congrArg Fin.val ((PCSBCSRounds.rounds c).left_inv index)
  exact inverse

theorem past_insert_predecessor {c : Config} (q : Coordinate c) (positive : 0 < position q) :
    past q = insert q (past (predecessor q positive)) := by
  ext r
  simp only [past, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    predecessor_position]
  constructor
  · intro bound
    by_cases equal : position r = position q
    · exact Or.inl (position_injective c equal)
    · exact Or.inr (by omega)
  · rintro (rfl | bound) <;> omega

theorem literal_conditional_transition {m : Nat} (p : Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : OriginalClaimsChecker.Prepared (config p) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy)
    (claimCap : points.size + 2 ≤ 2^64) (q : Coordinate (config p)) (positive : 0 < position q)
    (ring : RingPCSGame.Prefix) (t : Tape (config p)) (failure : Sample q → Prop)
    (before : publicState p lanes family points anchorPoint anchorValue prepared root
      (snapshot ring t (replies (Input p lanes root (OriginalClaimsChecker.input prepared root ring).claims) (strategy ring) t)
        (predecessor q positive)) = false) :
    Soundness.uniformProb (Finset.univ.filter fun x : Sample q => failure x ∧
      publicState p lanes family points anchorPoint anchorValue prepared root
        (snapshot ring (set q t x)
          (replies (Input p lanes root (OriginalClaimsChecker.input prepared root ring).claims) (strategy ring) (set q t x)) q) = true) ≤
      rbrError := by
  have incoming : sourceState p lanes family points anchorPoint anchorValue prepared root strategy
      true (past (predecessor q positive)) ring t = false := by
    rw [← snapshot_publicState_source]
    exact before
  have earlier : ∀ r ∈ past (predecessor q positive), position r < position q := by
    intro r member
    simp only [past, Finset.mem_filter, Finset.mem_univ, true_and] at member
    rw [predecessor_position] at member
    omega
  have bound := source_conditional_transition_uniform p lanes family points anchorPoint anchorValue
    prepared root strategy claimCap (past (predecessor q positive)) q ring t failure earlier incoming
  simpa only [snapshot_publicState_source, past_insert_predecessor q positive] using bound

#print axioms predecessor_position
#print axioms past_insert_predecessor
#print axioms literal_conditional_transition
end Whir.PCSRoundByRoundTranscriptState
