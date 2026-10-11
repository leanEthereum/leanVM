import Whir.PCSRoundByRoundPublicEvents
import Whir.PCSRoundByRoundPublicQuery
import Whir.PCSRoundByRoundKnowledgeState
import Whir.PCSRewindKnowledgeOriginalChance

/-! The state predicate's inputs contain only the original public statement, the prover's Root0 oracle string and an observed strict public trace. Its zero-filled reconstruction does not supply hidden future verifier randomness. -/
namespace Whir.PCSRoundByRoundTranscriptState
open Concrete Protocol CausalGame CausalExecution CausalProbability CausalStrategy
open ParameterBounds SupportedCandidateProtocol PCSRoundByRoundKnowledge
open Classical PublicTrace

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

noncomputable def completed {c : Config} (trace : PublicTrace c) : Finset (Coordinate c) :=
  Finset.univ.filter fun q => (trace.samples q).isSome

@[simp] theorem mem_completed {c : Config} (trace : PublicTrace c) (q : Coordinate c) :
    q ∈ completed trace ↔ (trace.samples q).isSome = true := by
  simp [completed]

@[simp] theorem snapshot_completed {c : Config} (ring : RingPCSGame.Prefix) (t : Tape c)
    (answers : Array Reply) (boundary q : Coordinate c) :
    q ∈ completed (snapshot ring t answers boundary) ↔ position q ≤ position boundary := by
  by_cases observed : position q ≤ position boundary
  · simp [completed, snapshot, observed]
  · simp [completed, snapshot, observed]

theorem snapshot_past {c : Config} (ring : RingPCSGame.Prefix) (t : Tape c)
    (answers : Array Reply) (boundary q : Coordinate c) (observed : position q ≤ position boundary) :
    get q (tape (snapshot ring t answers boundary)) = get q t := by
  rw [get_tape]
  simp [snapshot, observed]

theorem snapshot_round_congr (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (ring : RingPCSGame.Prefix) (t : Tape (config p))
    (answers : Array Reply) (boundary q : Coordinate (config p))
    (observed : position q ≤ position boundary) :
    roundBad p lanes root claims (indexedStrategy (snapshot ring t answers boundary).answers) q
        (tape (snapshot ring t answers boundary)) ↔
      roundBad p lanes root claims (indexedStrategy answers) q t := by
  have history : ∀ n, n < position q →
      (snapshot ring t answers boundary).answers[n]! = answers[n]! := by
    intro n bound
    exact priorAnswers_get answers (position boundary) n (bound.trans_le observed)
  have observedCoords : ∀ r, position r ≤ position q →
      get r (tape (snapshot ring t answers boundary)) = get r t := by
    intro r earlier
    exact snapshot_past ring t answers boundary r (earlier.trans observed)
  exact (round_prefix_congr p lanes root claims
    (indexedStrategy (snapshot ring t answers boundary).answers) q
    (tape (snapshot ring t answers boundary)) t observedCoords).trans
    (round_indexed_congr p lanes root claims (snapshot ring t answers boundary).answers
      answers q t history)

noncomputable def past {c : Config} (boundary : Coordinate c) : Finset (Coordinate c) :=
  Finset.univ.filter fun q => position q ≤ position boundary

theorem snapshot_state_congr (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (ring : RingPCSGame.Prefix) (t : Tape (config p))
    (answers : Array Reply) (boundary : Coordinate (config p)) :
    state (roundBad p lanes root claims (indexedStrategy (snapshot ring t answers boundary).answers))
        (completed (snapshot ring t answers boundary)) (tape (snapshot ring t answers boundary)) =
      state (roundBad p lanes root claims (indexedStrategy answers)) (past boundary) t := by
  have event : (∃ q ∈ completed (snapshot ring t answers boundary),
      roundBad p lanes root claims (indexedStrategy (snapshot ring t answers boundary).answers) q
        (tape (snapshot ring t answers boundary))) ↔
      (∃ q ∈ past boundary, roundBad p lanes root claims (indexedStrategy answers) q t) := by
    constructor
    · rintro ⟨q, member, bad⟩
      have observed := (snapshot_completed ring t answers boundary q).mp member
      exact ⟨q, by simpa only [past, Finset.mem_filter, Finset.mem_univ, true_and] using observed,
        (snapshot_round_congr p lanes root claims ring t answers boundary q observed).mp bad⟩
    · rintro ⟨q, member, bad⟩
      have observed : position q ≤ position boundary := by
        simpa only [past, Finset.mem_filter, Finset.mem_univ, true_and] using member
      exact ⟨q, (snapshot_completed ring t answers boundary q).mpr observed,
        (snapshot_round_congr p lanes root claims ring t answers boundary q observed).mpr bad⟩
  unfold state
  simp only [event]

noncomputable def publicState {m : Nat} (p : Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : OriginalClaimsChecker.Prepared (config p) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (trace : PublicTrace (config p)) : Bool :=
  match trace.ring with
  | none => false
  | some ring =>
    if RingPCSGame.Escape (config p) lanes root family ring then true else
      state (roundBad p lanes root (OriginalClaimsChecker.input prepared root ring).claims
        (indexedStrategy trace.answers)) (completed trace) (tape trace)

@[simp] theorem publicState_initial {m : Nat} (p : Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : OriginalClaimsChecker.Prepared (config p) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) :
    publicState p lanes family points anchorPoint anchorValue prepared root (PublicTrace.initial (config p)) = false := by
  rfl

#print axioms snapshot_completed
#print axioms snapshot_past
#print axioms publicState_initial
#print axioms snapshot_round_congr
#print axioms snapshot_state_congr
end Whir.PCSRoundByRoundTranscriptState
