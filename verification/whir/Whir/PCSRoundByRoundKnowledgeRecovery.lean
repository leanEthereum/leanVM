import Whir.PCSRoundByRoundKnowledgeQuery
import Whir.PCSRoundByRoundSourceDecoderCorrectness

/-! Deterministic accepted-path bridge. The SAME OOD target, its backward-lifted
Root0 witness, every original slice/point, and the literal saved anchor are all
kept distinct from the probabilistic transition ledger. -/
namespace Whir.PCSRoundByRoundKnowledge
open Concrete Protocol CausalGame CausalExecution CausalProbability ExecutionShapes
open ParameterBounds SupportedCandidateProtocol RewindBatchTarget
open PCSRewindExtractor (heavyAgreementCap production_heavy_static)
open SupportedCandidateExtraction (width blockLength)
open PCSRoundByRoundSource

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
attribute [local irreducible] ParameterBounds.config

/-- Safe acceptance either pays the real low-support query event or identifies
one strongly supported Root0 word explaining the original immutable statement. -/
theorem accepted_safe_strong_original {m : Nat} (p : Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : OriginalClaimsChecker.Prepared (config p) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (publicPrefix : RingPCSGame.Prefix) (strategy : Strategy)
    (t : Tape (config p))
    (accepted : experiment (OriginalClaimsChecker.input prepared root publicPrefix) strategy t = true)
    (ringSafe : ¬ RingPCSGame.Escape (config p) lanes root family publicPrefix)
    (safe : ¬ KnowledgeBad p lanes root (OriginalClaimsChecker.input prepared root publicPrefix).claims strategy t)
    (notLow : ¬ LowSupportQuery p lanes root (OriginalClaimsChecker.input prepared root publicPrefix).claims strategy t) :
    ∃ w : Witness (config p) lanes, StrongRootSupport p lanes root w ∧
      PCSRewindSource.ExplainsOriginal (config p) lanes root family points anchorPoint anchorValue w := by
  classical
  let claims := (OriginalClaimsChecker.input prepared root publicPrefix).claims
  let input := Input p lanes root claims
  let i := initialLevel p
  have dims : remaining (config p) 0 = (config p).logN - (config p).folds[0]! :=
    (InitialCandidates.production_initial_facts p).1
  have acc : experiment input strategy t = true := accepted
  have causal : ∀ q, ¬ CausalBadEvents.Bad input strategy q t := by
    intro q bad
    exact safe (Or.inl ⟨q, bad⟩)
  have collision : ¬ CollisionEvent p lanes root claims strategy t := by
    intro bad
    exact safe (Or.inr (Or.inr (Or.inr bad)))
  have outside := (collisionEvent_set p lanes root claims strategy t (get (.query i) t)).not.mp
    (show CollisionEvent p lanes root claims strategy (set (.query i) t (get (.query i) t)) → False by
      simpa only [set_get] using collision)
  obtain ⟨target, matching, truth⟩ := Root0FixedTarget.accepted_reset_target_exists p lanes root claims
    strategy t i (production_initial_next p) (get (.query i) t)
    (by simpa only [set_get] using acc) (by simpa only [set_get] using causal) outside
  have separated : LevelBoundary.Separated (followingCandidates input strategy t 0)
      (challenges (config p) t).levels[0]!.oodPoints[0]! := by
    by_contra absent
    exact causal (.ood i (firstOOD p)) absent
  have hit := RewindRadiusExtraction.accepted_reset_fixed_target p lanes root claims strategy t i
    (production_initial_next p) (get (.query i) t) target matching separated
    (by simpa only [set_get] using acc) (by simpa only [set_get] using causal) outside
  have hit' : SamplingProbability.allQueriesHit (initialDepth p) (config p).queries[0]!
      (scalarSupport p root t target) (get (.query i) t).1 := by
    simpa only [scalarSupport, initialDepth, i, initialLevel, levelAt_zero, initial,
      beq_self_eq_true, ↓reduceIte, Input] using hit
  have above : heavyAgreementCap p < (scalarSupport p root t target).card := by
    by_contra small
    exact notLow ⟨target, ⟨matching, separated⟩, Nat.le_of_not_gt small, hit'⟩
  have valid : oracleValid (liftRoot root) (length (config p) 0) lanes = true := by
    simpa only [i, initialLevel, levelAt_zero, initial, beq_self_eq_true, ↓reduceIte] using
      AcceptedShapes.accepted_oracle p lanes root claims strategy t acc i
  have laneBound := AcceptedShapes.accepted_lane_bound input strategy t acc
  have prior := priorGood_of_not_bad p lanes root claims strategy t safe
  have size : target.size = width (config p) := by
    have size := CausalBoundary.followingCandidates_sizes input strategy t p rfl i
      (by intro impossible; exact (impossible (production_initial_next p)).elim) target matching.1
    change target.size = 2 ^ remaining (config p) 0 at size
    simpa only [width, dims] using size
  let H := LevelBoundary.agreeingColumns ((config p).logN - (config p).folds[0]!)
    (config p).rates[0]! target
    (QueryBatchSoundness.oldWord ((config p).logN - (config p).folds[0]!) (config p).rates[0]!
      (liftRoot root) true (challenges (config p) t).levels[0]!.folds)
  have aboveH : heavyAgreementCap p < H.card := by
    dsimp only [scalarSupport] at above
    rw [dims] at above
    exact above
  obtain ⟨w, explains, rows⟩ := same_w_on_support p lanes root claims strategy t valid laneBound
    (fun j => (prior.1 j).1) (fun j => (prior.1 j).2) prior.2.1 prior.2.2 target size truth
    H
    ((production_heavy_static p).2.2.trans (by omega)) (by
      intro q member
      exact (Finset.mem_filter.mp member).2)
  have strong : StrongRootSupport p lanes root w := by
    apply aboveH.trans_le
    apply Finset.card_le_card
    intro q member
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rows q member⟩
  have checked := PCSRewindSource.input_checked_of_explains prepared root publicPrefix w ringSafe explains
  have original := (OriginalClaimsChecker.check_iff prepared w).mp checked
  exact ⟨w, strong, explains.1, original.1, original.2⟩

/-- The decoder is the implemented direct-index full-root Gao decoder. No
strategy, tape, post-root randomness, availability certificate, or abstract
recovery function is an extractor input or a premise of this endpoint. -/
theorem accepted_safe_run {m : Nat} (p : Profile) (lanes : Nat)
    (family : Fin m → RingPCSGame.FamilyClaim) (points : Array RingPCSGame.PointClaim)
    (anchorPoint : Array E) (anchorValue : E)
    (prepared : OriginalClaimsChecker.Prepared (config p) lanes m family points anchorPoint anchorValue)
    (root : BaseOracle) (publicPrefix : RingPCSGame.Prefix) (strategy : Strategy)
    (t : Tape (config p)) (familyCap : m ≤ 2^64) (pointCap : points.size ≤ 2^64)
    (full : FullRoot (config p) lanes root)
    (accepted : experiment (OriginalClaimsChecker.input prepared root publicPrefix) strategy t = true)
    (ringSafe : ¬ RingPCSGame.Escape (config p) lanes root family publicPrefix)
    (safe : ¬ KnowledgeBad p lanes root (OriginalClaimsChecker.input prepared root publicPrefix).claims strategy t)
    (notLow : ¬ LowSupportQuery p lanes root (OriginalClaimsChecker.input prepared root publicPrefix).claims strategy t) :
    ∃ w : Witness (config p) lanes,
      PCSRoundByRoundSource.run p lanes family points anchorPoint anchorValue root = some w ∧
      PCSRewindSource.ExplainsOriginal (config p) lanes root family points anchorPoint anchorValue w := by
  obtain ⟨w, heavy, original⟩ := accepted_safe_strong_original p lanes family points anchorPoint anchorValue
    prepared root publicPrefix strategy t accepted ringSafe safe notLow
  exact ⟨w, PCSRoundByRoundSource.run_recovers_heavy p lanes family points anchorPoint anchorValue root
    prepared familyCap pointCap full w heavy original.original original.anchor, original⟩

end Whir.PCSRoundByRoundKnowledge
