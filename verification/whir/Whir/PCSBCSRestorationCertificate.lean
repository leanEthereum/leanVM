import Whir.PCSBCSRestorationHazard

/-! The complete uniform-fiber certificate covers the unchanged grouped initial draw and every later source coordinate. It retains the original family, ordinary/strided points and anchor. -/
namespace Whir.PCSBCSRestorationHazard
open Concrete Protocol CausalGame CausalProbability CausalExecution CausalStrategy
open ParameterBounds SupportedCandidateProtocol PCSRoundByRoundKnowledge
open PCSRoundByRoundTranscriptState PCSStateRestoration.Adaptive
open Classical

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

instance raw_nonempty {c : Config} (q : Coordinate c) : Nonempty (PCSBCSRounds.Raw q) := by
  cases q <;> unfold PCSBCSRounds.Raw WHIRHistory.StackSample Sample <;> infer_instance

section Source
variable {m : Nat} (p : Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : OriginalClaimsChecker.Prepared (config p) lanes m family points anchorPoint anchorValue)

theorem snapshot_indexed_answers (root : BaseOracle) (ring : RingPCSGame.Prefix)
    (t : Tape (config p)) (answers : Array Reply) (q : Coordinate (config p)) :
    publicState p lanes family points anchorPoint anchorValue prepared root
      (snapshot ring t
        (replies (ExecutionShapes.Input p lanes root (OriginalClaimsChecker.input prepared root ring).claims)
          (indexedStrategy answers) t) q) =
      publicState p lanes family points anchorPoint anchorValue prepared root (snapshot ring t answers q) := by
  rw [snapshot_publicState_source p lanes family points anchorPoint anchorValue prepared root
    (fun _ => indexedStrategy answers) ring t q]
  unfold publicState sourceState
  simp only [snapshot_ring, true_and]
  split_ifs
  · rfl
  · rw [snapshot_state_congr]

theorem initial_fiber (familyCap : m ≤ 2^64) (claimCap : points.size + 2 ≤ 2^64)
    (data : PublicData (config p)) :
    Soundness.uniformProb (Finset.univ.filter fun draw : PCSBCSRounds.Raw (.initial : Coordinate (config p)) =>
      (certificate p lanes family points anchorPoint anchorValue prepared).after data .initial draw = true) ≤
      rbrError := by
  let strategy : RingPCSGame.Prefix → Strategy := fun _ => indexedStrategy data.trace.answers
  have source := literal_initial_grouped_transition p lanes family points anchorPoint anchorValue prepared
    data.root strategy familyCap claimCap data.trace.tape (fun _ => True)
  have event (draw : RingPCSGame.Prefix × E) :
      publicState p lanes family points anchorPoint anchorValue prepared data.root
        (snapshot draw.1 (set .initial data.trace.tape draw.2)
          (replies (ExecutionShapes.Input p lanes data.root
            (OriginalClaimsChecker.input prepared data.root draw.1).claims) (strategy draw.1)
            (set .initial data.trace.tape draw.2)) .initial) =
      (certificate p lanes family points anchorPoint anchorValue prepared).after data .initial draw := by
    exact snapshot_indexed_answers p lanes family points anchorPoint anchorValue prepared data.root draw.1
      (set .initial data.trace.tape draw.2) data.trace.answers .initial
  simpa only [true_and, event] using source

theorem noninitial_fiber (claimCap : points.size + 2 ≤ 2^64) (data : PublicData (config p))
    (q : Coordinate (config p)) (different : q ≠ .initial)
    (undoomed : (certificate p lanes family points anchorPoint anchorValue prepared).before data q = false) :
    Soundness.uniformProb (Finset.univ.filter fun answer : PCSBCSRounds.Raw q =>
      (certificate p lanes family points anchorPoint anchorValue prepared).after data q answer = true) ≤ rbrError := by
  have positive := noninitial_positive q different
  have incoming : laterBefore p lanes family points anchorPoint anchorValue prepared data q positive = false := by
    simpa only [certificate, before, dite_eq_right different] using undoomed
  have bound := later_fiber p lanes family points anchorPoint anchorValue prepared claimCap data q positive incoming
  cases q with
  | initial => exact False.elim (different rfl)
  | fold i j =>
    simp only [certificate, after]
    convert bound using 1; congr 1
  | ood i j =>
    simp only [certificate, after]
    convert bound using 1; congr 1
  | query i =>
    simp only [certificate, after]
    convert bound using 1; congr 1
  | tail j =>
    simp only [certificate, after]
    convert bound using 1; congr 1

theorem source_conditionalHazard (familyCap : m ≤ 2^64) (claimCap : points.size + 2 ≤ 2^64) :
    ConditionalHazard (certificate p lanes family points anchorPoint anchorValue prepared) rbrError := by
  apply conditionalHazard_of_uniform
  intro data q incoming
  by_cases initial : q = .initial
  · subst q
    exact initial_fiber p lanes family points anchorPoint anchorValue prepared familyCap claimCap data
  · exact noninitial_fiber p lanes family points anchorPoint anchorValue prepared claimCap data q initial incoming

noncomputable def keyedCertificate {Key : Type*} (round : Key → Coordinate (config p)) :
    Certificate Key (fun key => PCSBCSRounds.Raw (round key)) (PublicData (config p)) :=
  ⟨fun data key => (certificate p lanes family points anchorPoint anchorValue prepared).before data (round key),
    fun data key answer => (certificate p lanes family points anchorPoint anchorValue prepared).after data
      (round key) answer⟩

theorem keyed_conditionalHazard {Key : Type*} [DecidableEq Key]
    (round : Key → Coordinate (config p)) (familyCap : m ≤ 2^64) (claimCap : points.size + 2 ≤ 2^64) :
    ConditionalHazard (keyedCertificate p lanes family points anchorPoint anchorValue prepared round) rbrError := by
  intro data key incoming
  exact source_conditionalHazard p lanes family points anchorPoint anchorValue prepared
    familyCap claimCap data (round key) incoming
end Source

#print axioms snapshot_indexed_answers
#print axioms initial_fiber
#print axioms noninitial_fiber
#print axioms source_conditionalHazard
#print axioms keyed_conditionalHazard
end Whir.PCSBCSRestorationHazard
