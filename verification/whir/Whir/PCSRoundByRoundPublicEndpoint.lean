import Whir.PCSRoundByRoundPublicCertificate
import Mathlib.Data.Finset.Max

/-! Initial grouped challenge and final acceptance use the same literal public predicate, before the following prover response. No hidden continuation is an input of that predicate. -/
namespace Whir.PCSRoundByRoundTranscriptState
open Concrete Protocol CausalGame CausalProbability CausalExecution CausalStrategy
open ParameterBounds SupportedCandidateProtocol PCSRoundByRoundKnowledge ExecutionShapes
open Classical PublicTrace CausalPositions CausalPrefix

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

@[simp] theorem past_initial (c : Config) : past (.initial : Coordinate c) = {.initial} := by
  ext q
  simp only [past, Finset.mem_filter, Finset.mem_univ, true_and, position_initial,
    Finset.mem_singleton]
  constructor
  · intro bound
    exact position_injective c (by rw [position_initial]; omega)
  · rintro rfl
    simp

theorem greatest_coordinate_exists (c : Config) :
    ∃ q : Coordinate c, ∀ r : Coordinate c, position r ≤ position q := by
  obtain ⟨q, _, largest⟩ := Finset.exists_max_image Finset.univ (@position c)
    (show (Finset.univ : Finset (Coordinate c)).Nonempty from ⟨.initial, Finset.mem_univ _⟩)
  exact ⟨q, fun r => largest r (Finset.mem_univ _)⟩

noncomputable def lastCoordinate (c : Config) : Coordinate c :=
  Classical.choose (greatest_coordinate_exists c)

theorem lastCoordinate_max (c : Config) (r : Coordinate c) :
    position r ≤ position (lastCoordinate c) :=
  Classical.choose_spec (greatest_coordinate_exists c) r

@[simp] theorem past_lastCoordinate (c : Config) : past (lastCoordinate c) = Finset.univ := by
  ext q
  simp [past, lastCoordinate_max c q]

section Source
variable {m : Nat} (p : Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : OriginalClaimsChecker.Prepared (config p) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (strategy : RingPCSGame.Prefix → Strategy)

theorem literal_initial_grouped_transition (familyCap : m ≤ 2^64)
    (claimCap : points.size + 2 ≤ 2^64) (t : Tape (config p))
    (failure : RingPCSGame.Prefix × E → Prop) :
    Soundness.uniformProb (Finset.univ.filter fun draw : RingPCSGame.Prefix × E =>
      failure draw ∧ publicState p lanes family points anchorPoint anchorValue prepared root
        (snapshot draw.1 (set .initial t draw.2)
          (replies (Input p lanes root (OriginalClaimsChecker.input prepared root draw.1).claims) (strategy draw.1)
            (set .initial t draw.2)) .initial) = true) ≤ rbrError := by
  simp only [snapshot_publicState_source, past_initial]
  exact (initial_grouped_transition p lanes family points anchorPoint anchorValue prepared root strategy
    t failure).trans (initialLoss_le_rbrError (m := m) p points familyCap claimCap)

theorem literal_accepted_extraction_failure_final (familyCap : m ≤ 2^64)
    (claimCap : points.size + 2 ≤ 2^64) (ring : RingPCSGame.Prefix) (t : Tape (config p))
    (accepted : experiment (OriginalClaimsChecker.input prepared root ring) (strategy ring) t = true)
    (failure : ¬ ∃ w, extract p lanes family points anchorPoint anchorValue root = some w ∧
      PCSRewindSource.ExplainsOriginal (config p) lanes root family points anchorPoint anchorValue w) :
    publicState p lanes family points anchorPoint anchorValue prepared root
      (snapshot ring t (replies (Input p lanes root (OriginalClaimsChecker.input prepared root ring).claims) (strategy ring) t)
        (lastCoordinate (config p))) = true := by
  rw [snapshot_publicState_source, past_lastCoordinate]
  exact accepted_extraction_failure_final_actual p lanes family points anchorPoint anchorValue prepared root
    strategy familyCap claimCap ring t accepted failure
end Source

#print axioms past_initial
#print axioms greatest_coordinate_exists
#print axioms literal_initial_grouped_transition
#print axioms literal_accepted_extraction_failure_final
end Whir.PCSRoundByRoundTranscriptState
