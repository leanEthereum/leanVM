import Whir.PCSBCSRestorationCertificate
import Whir.PCSBCSRoundsAdapter

/-! Source path metadata captures only prior public draws and the already supplied prover response. Agreement below discards every hidden future coordinate. -/
namespace Whir.PCSBCSRestorationHazard
open Concrete Protocol CausalGame CausalProbability CausalExecution CausalStrategy
open ParameterBounds SupportedCandidateProtocol PCSRoundByRoundKnowledge
open PCSRoundByRoundTranscriptState PCSStateRestoration.Adaptive
open Classical PublicTrace

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def incomingTrace {c : Config} (ring : RingPCSGame.Prefix) (t : Tape c)
    (answers : Array Reply) (q : Coordinate c) : PublicTrace c :=
  ⟨if q = .initial then none else some ring,
    (fun r => if position r < position q then some (get r t) else none),
    priorAnswers answers (position q)⟩

theorem incoming_get {c : Config} (ring : RingPCSGame.Prefix) (t : Tape c)
    (answers : Array Reply) (q r : Coordinate c) (observed : position r < position q) :
    get r (incomingTrace ring t answers q).tape = get r t := by
  simp [incomingTrace, observed]

theorem incoming_after_get {c : Config} (ring : RingPCSGame.Prefix) (t : Tape c)
    (answers : Array Reply) (q r : Coordinate c) (observed : position r ≤ position q) :
    get r (set q (incomingTrace ring t answers q).tape (get q t)) = get r t := by
  by_cases same : r = q
  · subst r
    exact get_set q _ _
  · rw [get_set_ne q r _ _ same]
    apply incoming_get
    have unequal : position r ≠ position q := fun eq => same (CausalPrefix.position_injective c eq)
    omega

theorem past_state_prefix (p : Profile) (lanes : Nat) (root : BaseOracle) (claims : Array Claim)
    (left right : Array Reply) (t u : Tape (config p)) (q : Coordinate (config p))
    (samples : ∀ r, position r ≤ position q → get r t = get r u)
    (answers : ∀ n, n < position q → left[n]! = right[n]!) :
    state (roundBad p lanes root claims (indexedStrategy left)) (past q) t =
      state (roundBad p lanes root claims (indexedStrategy right)) (past q) u := by
  have event : (∃ r ∈ past q, roundBad p lanes root claims (indexedStrategy left) r t) ↔
      (∃ r ∈ past q, roundBad p lanes root claims (indexedStrategy right) r u) := by
    apply exists_congr
    intro r
    apply and_congr_right
    intro member
    have observed : position r ≤ position q := by
      simpa only [past, Finset.mem_filter, Finset.mem_univ, true_and] using member
    exact (round_prefix_congr p lanes root claims (indexedStrategy left) r t u
      (fun s earlier => samples s (earlier.trans observed))).trans
      (round_indexed_congr p lanes root claims left right r u
        (fun n prior => answers n (prior.trans_le observed)))
  unfold state
  simp only [event]

section Source
variable {m : Nat} (p : Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : OriginalClaimsChecker.Prepared (config p) lanes m family points anchorPoint anchorValue)

theorem public_snapshot_prefix (root : BaseOracle) (ring : RingPCSGame.Prefix)
    (left right : Array Reply) (t u : Tape (config p)) (q : Coordinate (config p))
    (samples : ∀ r, position r ≤ position q → get r t = get r u)
    (answers : ∀ n, n < position q → left[n]! = right[n]!) :
    publicState p lanes family points anchorPoint anchorValue prepared root (snapshot ring t left q) =
      publicState p lanes family points anchorPoint anchorValue prepared root (snapshot ring u right q) := by
  unfold publicState
  simp only [snapshot_ring]
  split_ifs
  · rfl
  · rw [snapshot_state_congr, snapshot_state_congr]
    exact past_state_prefix p lanes root (OriginalClaimsChecker.input prepared root ring).claims
      left right t u q samples answers

def incomingData (root : BaseOracle) (ring : RingPCSGame.Prefix) (t : Tape (config p))
    (answers : Array Reply) (q : Coordinate (config p)) : PublicData (config p) :=
  ⟨root, incomingTrace ring t answers q⟩

theorem incoming_before (root : BaseOracle) (ring : RingPCSGame.Prefix) (t : Tape (config p))
    (answers : Array Reply) (q : Coordinate (config p)) (different : q ≠ .initial) :
    (certificate p lanes family points anchorPoint anchorValue prepared).before
        (incomingData p root ring t answers q) q =
      publicState p lanes family points anchorPoint anchorValue prepared root
        (snapshot ring t answers (predecessor q (noninitial_positive q different))) := by
  unfold certificate before laterBefore incomingData
  simp only [dite_eq_right different, incomingTrace, ite_eq_right different]
  apply public_snapshot_prefix p lanes family points anchorPoint anchorValue prepared
  · intro r observed
    apply incoming_get ring t answers q r
    rw [predecessor_position] at observed
    have positive := noninitial_positive q different
    omega
  · intro n prior
    apply priorAnswers_get
    rw [predecessor_position] at prior
    omega

theorem incoming_after_initial (root : BaseOracle) (ring : RingPCSGame.Prefix)
    (t : Tape (config p)) (answers : Array Reply) :
    (certificate p lanes family points anchorPoint anchorValue prepared).after
        (incomingData p root ring t answers .initial) .initial (ring,get .initial t) =
      publicState p lanes family points anchorPoint anchorValue prepared root
        (snapshot ring t answers .initial) := by
  unfold certificate after incomingData
  apply public_snapshot_prefix p lanes family points anchorPoint anchorValue prepared
  · exact fun r observed => incoming_after_get ring t answers .initial r observed
  · exact fun n prior => priorAnswers_get answers (position (.initial : Coordinate (config p))) n prior

theorem incoming_after_later (root : BaseOracle) (ring : RingPCSGame.Prefix) (t : Tape (config p))
    (answers : Array Reply) (q : Coordinate (config p)) (different : q ≠ .initial) :
    laterAfter p lanes family points anchorPoint anchorValue prepared
        (incomingData p root ring t answers q) q (get q t) =
      publicState p lanes family points anchorPoint anchorValue prepared root (snapshot ring t answers q) := by
  unfold laterAfter incomingData
  simp only [incomingTrace, ite_eq_right different]
  apply public_snapshot_prefix p lanes family points anchorPoint anchorValue prepared
  · exact fun r observed => incoming_after_get ring t answers q r observed
  · exact fun n prior => priorAnswers_get answers (position q) n prior

end Source
#print axioms incoming_after_get
#print axioms past_state_prefix
#print axioms public_snapshot_prefix
#print axioms incoming_before
#print axioms incoming_after_later
#print axioms incoming_after_initial
end Whir.PCSBCSRestorationHazard
