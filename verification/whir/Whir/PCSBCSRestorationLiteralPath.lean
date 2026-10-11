import Whir.PCSBCSRestorationTrace
import Whir.PCSBCSCallerBinding

/-! Literal before/after identities used to link a source verifier's observed
packets to the additive RBR predicate. They do not assume a failure-probability
bound or silently identify a byte parser with the verifier. -/
set_option autoImplicit false
namespace Whir.PCSBCSRestorationHazard
open Concrete Protocol CausalGame CausalProbability CausalExecution CausalStrategy
open ParameterBounds PCSRoundByRoundKnowledge PCSRoundByRoundTranscriptState
open PCSBCSCallerBinding

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def literalRaw {c : Config} (ring : RingPCSGame.Prefix) (t : Tape c)
    (q : Coordinate c) : PCSBCSRounds.Raw q :=
  match q with
  | .initial => (ring,get .initial t)
  | .fold i j => get (.fold i j) t
  | .ood i j => get (.ood i j) t
  | .query i => get (.query i) t
  | .tail j => get (.tail j) t

def literalCallerData (p : Profile) (original : CallerInput p) (root : BaseOracle)
    (ring : RingPCSGame.Prefix) (t : Tape (config p)) (answers : Array Reply)
    (q : Coordinate (config p)) : CallerData p :=
  ⟨original,incomingData p root ring t answers q⟩

noncomputable def literalState (p : Profile) (original : CallerInput p) (root : BaseOracle)
    (ring : RingPCSGame.Prefix) (t : Tape (config p)) (answers : Array Reply)
    (q : Coordinate (config p)) : Bool :=
  publicState p original.lanes original.family original.points original.anchorPoint
    original.anchorValue original.prepared root (snapshot ring t answers q)

attribute [local irreducible] ParameterBounds.config

theorem literal_after (p : Profile) (original : CallerInput p) (root : BaseOracle)
    (ring : RingPCSGame.Prefix) (t : Tape (config p)) (answers : Array Reply)
    (q : Coordinate (config p)) :
    (callerCertificate p).after (literalCallerData p original root ring t answers q)
      q (literalRaw ring t q) = literalState p original root ring t answers q := by
  unfold callerCertificate fixedCertificate literalCallerData literalState
  cases q with
  | initial =>
    exact incoming_after_initial p original.lanes original.family original.points
      original.anchorPoint original.anchorValue original.prepared root ring t answers
  | fold i j =>
    exact incoming_after_later p original.lanes original.family original.points
      original.anchorPoint original.anchorValue original.prepared root ring t answers (.fold i j) (by intro h; cases h)
  | ood i j =>
    exact incoming_after_later p original.lanes original.family original.points
      original.anchorPoint original.anchorValue original.prepared root ring t answers (.ood i j) (by intro h; cases h)
  | query i =>
    exact incoming_after_later p original.lanes original.family original.points
      original.anchorPoint original.anchorValue original.prepared root ring t answers (.query i) (by intro h; cases h)
  | tail j =>
    exact incoming_after_later p original.lanes original.family original.points
      original.anchorPoint original.anchorValue original.prepared root ring t answers (.tail j) (by intro h; cases h)

theorem literal_before (p : Profile) (original : CallerInput p) (root : BaseOracle)
    (ring : RingPCSGame.Prefix) (t : Tape (config p)) (answers : Array Reply)
    (q : Coordinate (config p)) (different : q ≠ .initial) :
    (callerCertificate p).before (literalCallerData p original root ring t answers q) q =
      literalState p original root ring t answers (predecessor q (noninitial_positive q different)) :=
  incoming_before p original.lanes original.family original.points original.anchorPoint
    original.anchorValue original.prepared root ring t answers q different

#print axioms literal_after
#print axioms literal_before
end Whir.PCSBCSRestorationHazard
