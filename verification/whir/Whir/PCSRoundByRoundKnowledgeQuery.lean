import Whir.PCSRoundByRoundSourceDecoder
import Whir.SupportedCandidateProtocolAccepted
import Whir.PCSRewindKnowledgeOriginalRecovery

/-! The Root0 query loss is conditional on an arbitrary fixed incoming public
history. Separation fixes one target before querying; there is no candidate-list
factor in the heavy-query term. -/
namespace Whir.PCSRoundByRoundKnowledge
open Concrete Protocol CausalGame CausalExecution CausalProbability ExecutionShapes
open ParameterBounds SupportedCandidateProtocol RewindBatchTarget
open PCSRewindExtractor (heavyAgreementCap heavyQueryLoss production_heavy_static)
open SupportedCandidateExtraction (blockLength)

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
attribute [local irreducible] ParameterBounds.config

/-- Native query indexing; the production initial-dimension theorem identifies
this with `PCSRewindExtractor.initialDepth` without changing the query law. -/
abbrev initialDepth (p : Profile) := remaining (config p) 0 + (config p).rates[0]!

noncomputable def TargetAt (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (t : Tape (config p))
    (target : Array E) : Prop :=
  Target (followingCandidates (Input p lanes root claims) strategy t 0)
    (challenges (config p) t).levels[0]!.oodPoints[0]!
    (proof (Input p lanes root claims) strategy t).levels[0]!.oods[0]!.value target ∧
  LevelBoundary.Separated (followingCandidates (Input p lanes root claims) strategy t 0)
    (challenges (config p) t).levels[0]!.oodPoints[0]!

noncomputable def scalarSupport (p : Profile) (root : BaseOracle)
    (t : Tape (config p)) (target : Array E) :=
  LevelBoundary.agreeingColumns (remaining (config p) 0) (config p).rates[0]! target
    (QueryBatchSoundness.oldWord (remaining (config p) 0) (config p).rates[0]!
      (liftRoot root) true (challenges (config p) t).levels[0]!.folds)

noncomputable def LowSupportQuery (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (t : Tape (config p)) : Prop :=
  ∃ target, TargetAt p lanes root claims strategy t target ∧
    (scalarSupport p root t target).card ≤ heavyAgreementCap p ∧
    SamplingProbability.allQueriesHit (initialDepth p) (config p).queries[0]!
      (scalarSupport p root t target) (get (.query (initialLevel p)) t).1

theorem targetAt_set (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (t : Tape (config p))
    (draw : Sample (.query (initialLevel p))) (target : Array E) :
    TargetAt p lanes root claims strategy (set (.query (initialLevel p)) t draw) target ↔
      TargetAt p lanes root claims strategy t target := by
  have fixed := Root0FixedTarget.snapshot_set (Input p lanes root claims) strategy t
    (initialLevel p) (.query (initialLevel p)) draw le_rfl
  have list := congrArg (fun s => s.1) fixed
  have answers := congrArg (fun s => s.2.2.2.1) fixed
  have points := congrArg (fun s => s.2.2.2.2.2) fixed
  dsimp only [Root0FixedTarget.snapshot, initialLevel] at list answers points
  unfold TargetAt
  rw [list, answers, points]

theorem scalarSupport_set (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (t : Tape (config p))
    (draw : Sample (.query (initialLevel p))) (target : Array E) :
    scalarSupport p root (set (.query (initialLevel p)) t draw) target =
      scalarSupport p root t target := by
  have fixed := Root0FixedTarget.snapshot_set (Input p lanes root claims) strategy t
    (initialLevel p) (.query (initialLevel p)) draw le_rfl
  have folds := congrArg (fun s => s.2.2.2.2.1) fixed
  dsimp only [Root0FixedTarget.snapshot, initialLevel] at folds
  unfold scalarSupport
  rw [folds]

open Classical in
theorem lowSupportQuery_fiber_bound (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (t : Tape (config p)) :
    Soundness.uniformProb (Finset.univ.filter fun draw : Sample (.query (initialLevel p)) =>
      LowSupportQuery p lanes root claims strategy (set (.query (initialLevel p)) t draw)) ≤
        heavyQueryLoss p := by
  by_cases existsTarget : ∃ target, TargetAt p lanes root claims strategy t target ∧
      (scalarSupport p root t target).card ≤ heavyAgreementCap p
  · obtain ⟨target, matching, small⟩ := existsTarget
    have included : (Finset.univ.filter fun draw : Sample (.query (initialLevel p)) =>
        LowSupportQuery p lanes root claims strategy (set (.query (initialLevel p)) t draw)) ⊆
        Finset.univ.filter (fun draw : Sample (.query (initialLevel p)) =>
          SamplingProbability.allQueriesHit (initialDepth p) (config p).queries[0]!
            (scalarSupport p root t target) draw.1) := by
      intro draw member
      obtain ⟨other, hm, hs, hit⟩ := (Finset.mem_filter.mp member).2
      have otherMatch := (targetAt_set p lanes root claims strategy t draw other).mp hm
      have same := target_unique _ _ _ matching.2 other target otherMatch.1 matching.1
      subst other
      rw [scalarSupport_set p lanes root claims strategy t draw, get_set] at hit
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hit⟩
    have positive : 0 < initialDepth p := by
      simpa only [initialDepth, (InitialCandidates.production_initial_facts p).1] using
        (production_heavy_static p).1
    have noWrap : initialDepth p ≤ 64 := by
      simpa only [initialDepth, (InitialCandidates.production_initial_facts p).1] using
        (InitialCandidates.production_initial_facts p).2.2.1
    have bound := SamplingProbability.actual_query_bound_rat (initialDepth p)
      (config p).queries[0]! positive noWrap (scalarSupport p root t target)
    have product : Soundness.uniformProb (Finset.univ.filter
        (fun draw : Sample (.query (initialLevel p)) =>
          SamplingProbability.allQueriesHit (initialDepth p) (config p).queries[0]!
            (scalarSupport p root t target) draw.1)) =
        Soundness.uniformProb (Finset.univ.filter
          (SamplingProbability.allQueriesHit (initialDepth p) (config p).queries[0]!
            (scalarSupport p root t target))) := by
      have realLaw := AuthenticatedResetProbability.product_left (B := E)
        (SamplingProbability.allQueriesHit (initialDepth p) (config p).queries[0]!
          (scalarSupport p root t target))
      rw [SamplingProbability.probability_eq_uniformProb,
        SamplingProbability.probability_eq_uniformProb] at realLaw
      exact (Rat.cast_inj (α := ℝ)).mp realLaw
    have uniform : Soundness.uniformProb (Finset.univ.filter
        (fun draw : Sample (.query (initialLevel p)) =>
          SamplingProbability.allQueriesHit (initialDepth p) (config p).queries[0]!
            (scalarSupport p root t target) draw.1)) ≤ heavyQueryLoss p := by
      rw [product]
      apply bound.trans
      unfold heavyQueryLoss
      have dims : blockLength (config p) = 2 ^ initialDepth p := by
        simp only [blockLength, initialDepth, (InitialCandidates.production_initial_facts p).1]
      rw [dims]
      gcongr
    apply le_trans ?_ uniform
    unfold Soundness.uniformProb
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card included)) (by positivity)
  · have empty : (Finset.univ.filter fun draw : Sample (.query (initialLevel p)) =>
        LowSupportQuery p lanes root claims strategy (set (.query (initialLevel p)) t draw)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro draw member
      obtain ⟨target, matching, small, _⟩ := (Finset.mem_filter.mp member).2
      apply existsTarget
      refine ⟨target, (targetAt_set p lanes root claims strategy t draw target).mp matching, ?_⟩
      simpa only [scalarSupport_set p lanes root claims strategy t draw target] using small
    rw [empty]
    simp only [Soundness.uniformProb, Finset.card_empty, Nat.cast_zero, zero_div]
    unfold heavyQueryLoss
    positivity

theorem lowSupportQuery_set_future (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (t : Tape (config p))
    (q : Coordinate (config p)) (x : Sample q)
    (later : position (.query (initialLevel p)) < position q) :
    LowSupportQuery p lanes root claims strategy (set q t x) ↔
      LowSupportQuery p lanes root claims strategy t := by
  have fixed := Root0FixedTarget.snapshot_set (Input p lanes root claims) strategy t
    (initialLevel p) q x later.le
  have list := congrArg (fun s => s.1) fixed
  have answers := congrArg (fun s => s.2.2.2.1) fixed
  have folds := congrArg (fun s => s.2.2.2.2.1) fixed
  have points := congrArg (fun s => s.2.2.2.2.2) fixed
  dsimp only [Root0FixedTarget.snapshot, initialLevel] at list answers folds points
  have draw := get_set_ne q (.query (initialLevel p)) t x (by
    intro same
    rw [same] at later
    exact (lt_irrefl _ later))
  unfold LowSupportQuery TargetAt scalarSupport
  rw [list, answers, folds, points, draw]

end Whir.PCSRoundByRoundKnowledge
