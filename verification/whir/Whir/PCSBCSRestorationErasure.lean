import Whir.PCSBCSRestorationTrace

/-! Incoming literal metadata is invariant under its own draw and every future coordinate. This is a strict-prefix fact, not an assertion that actual raw source keys already identify those coordinates. -/
namespace Whir.PCSBCSRestorationHazard
open Concrete Protocol CausalGame CausalProbability CausalExecution
open PCSRoundByRoundTranscriptState PublicTrace

set_option autoImplicit false

 theorem incomingTrace_set_unobserved {c : Config} (ring : RingPCSGame.Prefix) (t : Tape c)
    (answers : Array Reply) (q r : Coordinate c) (value : Sample r)
    (unobserved : position q ≤ position r) :
    incomingTrace ring (set r t value) answers q = incomingTrace ring t answers q := by
  classical
  unfold incomingTrace
  congr 1
  funext s
  split_ifs with observed
  · have different : s ≠ r := by
      intro same
      subst s
      omega
    rw [get_set_ne r s t value different]
  · rfl

 theorem incomingTrace_initial_ring_independent {c : Config} (left right : RingPCSGame.Prefix)
    (t : Tape c) (answers : Array Reply) :
    incomingTrace left t answers (.initial : Coordinate c) = incomingTrace right t answers .initial := by
  rfl

 theorem incomingData_set_unobserved (p : ParameterBounds.Profile) (root : BaseOracle)
    (ring : RingPCSGame.Prefix) (t : Tape (ParameterBounds.config p)) (answers : Array Reply)
    (q r : Coordinate (ParameterBounds.config p)) (value : Sample r)
    (unobserved : position q ≤ position r) :
    incomingData p root ring (set r t value) answers q = incomingData p root ring t answers q := by
  unfold incomingData
  rw [incomingTrace_set_unobserved ring t answers q r value unobserved]

#print axioms incomingTrace_set_unobserved
#print axioms incomingTrace_initial_ring_independent
#print axioms incomingData_set_unobserved
end Whir.PCSBCSRestorationHazard
