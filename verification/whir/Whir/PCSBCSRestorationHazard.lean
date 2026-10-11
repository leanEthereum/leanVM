import Whir.PCSRoundByRoundPublicTransition
import Whir.PCSStateRestorationAdaptive

/-! The restoration hazard is instantiated with the actual additive source RBR predicate, not an assumed soundness probability. Metadata contains only a frozen raw root and an observed public trace. -/
namespace Whir.PCSBCSRestorationHazard
open Concrete Protocol CausalGame CausalProbability CausalExecution CausalStrategy
open ParameterBounds SupportedCandidateProtocol PCSRoundByRoundKnowledge
open PCSRoundByRoundTranscriptState PCSStateRestoration.Adaptive
open Classical

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

structure PublicData (c : Config) where
  root : BaseOracle
  trace : PublicTrace c

theorem noninitial_positive {c : Config} (q : Coordinate c) (different : q ≠ .initial) :
    0 < position q := by
  by_contra absent
  apply different
  exact CausalPrefix.position_injective c (by rw [CausalPositions.position_initial]; omega)

section Source
variable {m : Nat} (p : Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : OriginalClaimsChecker.Prepared (config p) lanes m family points anchorPoint anchorValue)

noncomputable def laterBefore (data : PublicData (config p)) (q : Coordinate (config p))
    (positive : 0 < position q) : Bool :=
  match data.trace.ring with
  | none => false
  | some ring => publicState p lanes family points anchorPoint anchorValue prepared data.root
      (snapshot ring data.trace.tape data.trace.answers (predecessor q positive))

noncomputable def laterAfter (data : PublicData (config p)) (q : Coordinate (config p))
    (answer : Sample q) : Bool :=
  match data.trace.ring with
  | none => false
  | some ring => publicState p lanes family points anchorPoint anchorValue prepared data.root
      (snapshot ring (set q data.trace.tape answer) data.trace.answers q)

noncomputable def before (data : PublicData (config p)) (q : Coordinate (config p)) : Bool :=
  if initial : q = .initial then false else
    laterBefore p lanes family points anchorPoint anchorValue prepared data q (noninitial_positive q initial)

noncomputable def after (data : PublicData (config p)) (q : Coordinate (config p)) :
    PCSBCSRounds.Raw q → Bool :=
  match q with
  | .initial => fun draw => publicState p lanes family points anchorPoint anchorValue prepared data.root
      (snapshot draw.1 (set .initial data.trace.tape draw.2) data.trace.answers .initial)
  | .fold i j => laterAfter p lanes family points anchorPoint anchorValue prepared data (.fold i j)
  | .ood i j => laterAfter p lanes family points anchorPoint anchorValue prepared data (.ood i j)
  | .query i => laterAfter p lanes family points anchorPoint anchorValue prepared data (.query i)
  | .tail j => laterAfter p lanes family points anchorPoint anchorValue prepared data (.tail j)

noncomputable def certificate : Certificate (Coordinate (config p)) PCSBCSRounds.Raw (PublicData (config p)) :=
  ⟨before p lanes family points anchorPoint anchorValue prepared,
    after p lanes family points anchorPoint anchorValue prepared⟩

theorem later_fiber (claimCap : points.size + 2 ≤ 2^64) (data : PublicData (config p))
    (q : Coordinate (config p)) (positive : 0 < position q)
    (undoomed : laterBefore p lanes family points anchorPoint anchorValue prepared data q positive = false) :
    Soundness.uniformProb (Finset.univ.filter fun answer : Sample q =>
      laterAfter p lanes family points anchorPoint anchorValue prepared data q answer = true) ≤ rbrError := by
  cases ringEq : data.trace.ring with
  | none =>
    simp only [laterAfter, ringEq, Bool.false_eq_true, Finset.filter_false, Soundness.uniformProb,
      Finset.card_empty, Nat.cast_zero, zero_div]
    unfold rbrError SupportedCandidateExtraction.radiusEnvelope
    positivity
  | some ring =>
    let strategy : RingPCSGame.Prefix → Strategy := fun _ => indexedStrategy data.trace.answers
    have beforeEq : publicState p lanes family points anchorPoint anchorValue prepared data.root
        (snapshot ring data.trace.tape
          (replies (ExecutionShapes.Input p lanes data.root
            (OriginalClaimsChecker.input prepared data.root ring).claims) (strategy ring) data.trace.tape)
          (predecessor q positive)) = false := by
      rw [snapshot_publicState_source]
      have direct : state (roundBad p lanes data.root (OriginalClaimsChecker.input prepared data.root ring).claims
          (indexedStrategy data.trace.answers)) (past (predecessor q positive)) data.trace.tape = false := by
        have congruence := snapshot_state_congr p lanes data.root
          (OriginalClaimsChecker.input prepared data.root ring).claims ring data.trace.tape data.trace.answers
          (predecessor q positive)
        -- Ring escape and the source state are retained by the same literal predicate.
        unfold laterBefore at undoomed
        rw [ringEq] at undoomed
        unfold publicState at undoomed
        simp only [snapshot_ring] at undoomed
        split_ifs at undoomed with escaped
        rw [congruence] at undoomed
        exact undoomed
      unfold sourceState
      dsimp only [strategy]
      have ringSafe : ¬ RingPCSGame.Escape (config p) lanes data.root family ring := by
        intro escaped
        unfold laterBefore at undoomed
        simp only [ringEq, publicState, snapshot_ring, escaped, ↓reduceIte] at undoomed
        contradiction
      simp only [ringSafe, and_false, ↓reduceIte]
      exact direct
    have source := literal_conditional_transition p lanes family points anchorPoint anchorValue prepared
      data.root strategy claimCap q positive ring data.trace.tape (fun _ => True) beforeEq
    have event (answer : Sample q) :
        publicState p lanes family points anchorPoint anchorValue prepared data.root
          (snapshot ring (set q data.trace.tape answer)
            (replies (ExecutionShapes.Input p lanes data.root
              (OriginalClaimsChecker.input prepared data.root ring).claims) (strategy ring)
              (set q data.trace.tape answer)) q) =
        laterAfter p lanes family points anchorPoint anchorValue prepared data q answer := by
      rw [snapshot_publicState_source]
      unfold laterAfter
      rw [ringEq]
      unfold publicState sourceState
      simp only [snapshot_ring, true_and]
      split_ifs
      · rfl
      · rw [snapshot_state_congr]
    simpa only [true_and, event] using source

end Source
#print axioms noninitial_positive
#print axioms later_fiber
end Whir.PCSBCSRestorationHazard
