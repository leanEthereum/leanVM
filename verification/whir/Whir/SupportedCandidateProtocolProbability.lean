import Whir.Root0FixedTarget
import Whir.SupportedCandidateProtocol
import Whir.RingMapBatching

/-! Knowledge-only exclusions on the actual finite causal tape. These are
source-independent fixed-list events, not assumed acceptance-failure covers. -/
namespace Whir.SupportedCandidateProtocol
open Concrete Protocol CausalGame CausalExecution CausalProbability ExecutionShapes
open CandidateFolding SupportedCandidateExtraction ParameterBounds InitialKnowledgeSchedule
open SamplingProbability AuthenticatedResetProbability RewindBatchTarget
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 400000
attribute [local irreducible] ParameterBounds.config
attribute [local irreducible] RawMCA ClaimEscape

abbrev FoldRest (c : Config) (i : Fin c.folds.size) :=
  E × (Fin (oodCount c i.val) → Fin (remaining c i.val) → E) ×
    (Fin (queryChunks c i.val) → E) × E ×
    (∀ j : {j : Fin c.folds.size // j ≠ i}, LevelTape c j.val) ×
    (Fin (c.logN-c.folds.toList.sum) → E)

noncomputable def foldSeedEquiv (c : Config) (i : Fin c.folds.size) :
    Tape c ≃ (Fin c.folds[i.val]! → E) × FoldRest c i where
  toFun t := ((t.2.1 i).1, t.1, (t.2.1 i).2.1, (t.2.1 i).2.2.1,
    (t.2.1 i).2.2.2, (Equiv.piSplitAt i (LevelTape c) t.2.1).2, t.2.2)
  invFun x := (x.2.1,
    (Equiv.piSplitAt i (LevelTape c)).symm
      ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1), x.2.2.2.2.2.1), x.2.2.2.2.2.2)
  left_inv t := by
    rcases t with ⟨batch, levels, tail⟩
    change (batch, (Equiv.piSplitAt i (LevelTape c)).symm
      ((Equiv.piSplitAt i (LevelTape c)) levels), tail) = (batch, levels, tail)
    rw [Equiv.symm_apply_apply]
  right_inv x := by
    dsimp only
    let pair := ((x.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1), x.2.2.2.2.2.1)
    have inverse := (Equiv.piSplitAt i (LevelTape c)).apply_symm_apply pair
    have selected := congrArg Prod.fst inverse
    change ((Equiv.piSplitAt i (LevelTape c)).symm pair) i = pair.1 at selected
    have other := congrArg Prod.snd inverse
    rw [selected, other]

noncomputable def CancellationEvent (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (t : Tape (config p)) : Prop :=
  initialRowCancellation (Input p lanes root claims) (t.2.1 (initialLevel p)).1

open Classical in
 theorem cancellation_probability (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) :
    Soundness.uniformProb (Finset.univ.filter (CancellationEvent p lanes root claims)) ≤
      (2 ^ 32 : ℚ) * blockLength (config p) * (6 / 2 ^ 192) := by
  have law := probability_equiv (foldSeedEquiv (config p) (initialLevel p))
    (fun x => initialRowCancellation (Input p lanes root claims) x.1)
  rw [product_left] at law
  change probability (CancellationEvent p lanes root claims) = _ at law
  rw [probability_eq_uniformProb, probability_eq_uniformProb] at law
  have rational := (Rat.cast_inj (α := ℝ)).mp law
  rw [rational]
  calc
    _ ≤ (2 ^ 32 : ℚ) * blockLength (config p) * ((config p).folds[0]! / (2 ^ 192 : ℚ)) :=
      production_rowCancellation_probability p lanes root claims
    _ = _ := congrArg (fun n : Nat =>
      (2 ^ 32 : ℚ) * blockLength (config p) * (n / (2 ^ 192 : ℚ))) (production_initial_six p)

/-- Full actual-query lambda collision event; adaptive response rows disappear
from its error polynomial by authenticated substitution. -/
noncomputable def CollisionEvent (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (t : Tape (config p)) : Prop :=
  Collision (remaining (config p) 0) (config p).rates[0]! (config p).queries[0]! 0
    (levelAt (Input p lanes root claims) strategy t 0).oracle
    (challenges (config p) t).levels[0]!
    (proof (Input p lanes root claims) strategy t).levels[0]!
    (CausalBoundary.boundary (Input p lanes root claims) strategy t (initialLevel p)).state
    (followingCandidates (Input p lanes root claims) strategy t 0)
    (get (.query (initialLevel p)) t).1 (get (.query (initialLevel p)) t).2

theorem collisionEvent_set (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (t : Tape (config p))
    (draw : Sample (.query (initialLevel p))) :
    CollisionEvent p lanes root claims strategy (set (.query (initialLevel p)) t draw) ↔
      Collision (remaining (config p) 0) (config p).rates[0]! (config p).queries[0]! 0
        (levelAt (Input p lanes root claims) strategy t 0).oracle
        (challenges (config p) t).levels[0]!
        (proof (Input p lanes root claims) strategy t).levels[0]!
        (CausalBoundary.boundary (Input p lanes root claims) strategy t (initialLevel p)).state
        (followingCandidates (Input p lanes root claims) strategy t 0) draw.1 draw.2 := by
  let input := Input p lanes root claims
  let i := initialLevel p
  have fixed := Root0FixedTarget.snapshot_set input strategy t i (.query i) draw le_rfl
  have list := congrArg (fun s => s.1) fixed
  have boundary := congrArg (fun s => s.2.1) fixed
  have oracle := congrArg (fun s => s.2.2.1) fixed
  have answers := congrArg (fun s => s.2.2.2.1) fixed
  have folds := congrArg (fun s => s.2.2.2.2.1) fixed
  have points := congrArg (fun s => s.2.2.2.2.2) fixed
  dsimp only [Root0FixedTarget.snapshot, i, initialLevel] at list boundary oracle answers folds points
  unfold CollisionEvent Collision QueryBatchSoundness.polynomial BatchingRefinement.errorPolynomial
    BatchingRefinement.oodError BatchingRefinement.queryError
  rw [get_set, list, boundary, oracle, answers, folds, points]

open Classical in
theorem collisionEvent_fiber_bound (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (t : Tape (config p)) :
    Soundness.uniformProb (Finset.univ.filter fun draw : Sample (.query (initialLevel p)) =>
      CollisionEvent p lanes root claims strategy (set (.query (initialLevel p)) t draw)) ≤
      (2 ^ 32 : ℚ) * ((oodCount (config p) 0 + (config p).queries[0]! : Nat) / 2 ^ 192) := by
  simp_rw [collisionEvent_set]
  let event := fun draw : Sample (.query (initialLevel p)) =>
    Collision (remaining (config p) 0) (config p).rates[0]! (config p).queries[0]! 0
      (levelAt (Input p lanes root claims) strategy t 0).oracle
      (challenges (config p) t).levels[0]!
      (proof (Input p lanes root claims) strategy t).levels[0]!
      (CausalBoundary.boundary (Input p lanes root claims) strategy t (initialLevel p)).state
      (followingCandidates (Input p lanes root claims) strategy t 0) draw.1 draw.2
  change Soundness.uniformProb (Finset.univ.filter event) ≤ _
  have average := RingMapBatching.uniform_product event
  have cap : ((followingCandidates (Input p lanes root claims) strategy t 0).card : ℚ) ≤ 2 ^ 32 := by
    exact_mod_cast CausalBoundary.followingCandidates_card (Input p lanes root claims) strategy t p rfl (initialLevel p)
  have each (query : LevelBoundary.QueryTape (remaining (config p) 0 + (config p).rates[0]!)
      (config p).queries[0]!) :
      Soundness.uniformProb (Finset.univ.filter fun lambda => event (query, lambda)) ≤
        (2 ^ 32 : ℚ) * ((oodCount (config p) 0 + (config p).queries[0]! : Nat) / 2 ^ 192) := by
    have bound := collision_probability (remaining (config p) 0) (config p).rates[0]!
      (config p).queries[0]! 0 (levelAt (Input p lanes root claims) strategy t 0).oracle
      (challenges (config p) t).levels[0]! (proof (Input p lanes root claims) strategy t).levels[0]!
      (CausalBoundary.boundary (Input p lanes root claims) strategy t (initialLevel p)).state
      (followingCandidates (Input p lanes root claims) strategy t 0) query
    rw [CausalBoundary.decoded_oods_size (Input p lanes root claims) strategy t (initialLevel p)] at bound
    exact bound.trans (mul_le_mul_of_nonneg_right cap (by positivity))
  rw [average]
  apply (div_le_iff₀ (by positivity : (0 : ℚ) <
    Fintype.card (Fin (queryChunks (config p) (initialLevel p).val) → E))).mpr
  calc
    _ ≤ ∑ _query, ((2 ^ 32 : ℚ) *
      ((oodCount (config p) 0 + (config p).queries[0]! : Nat) / 2 ^ 192)) :=
      Finset.sum_le_sum (by intro query _; exact each query)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

open Classical in
theorem collisionEvent_probability (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) :
    Soundness.uniformProb (Finset.univ.filter (CollisionEvent p lanes root claims strategy)) ≤
      (2 ^ 32 : ℚ) * ((oodCount (config p) 0 + (config p).queries[0]! : Nat) / 2 ^ 192) := by
  apply fiber_event_bound (.query (initialLevel p))
  intro rest
  exact collisionEvent_fiber_bound p lanes root claims strategy rest.val

noncomputable def KnowledgeBad (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (t : Tape (config p)) : Prop :=
  (∃ q, CausalBadEvents.Bad (Input p lanes root claims) strategy q t) ∨
    InitialFoldBad p lanes root claims strategy t ∨
    CancellationEvent p lanes root claims t ∨ CollisionEvent p lanes root claims strategy t

/-- Exact production ledger, retaining the real initial query/OOD batch width. -/
def knowledgeLedger (p : Profile) (claims : Nat) : ℚ :=
  GroupedChallenges.interactiveError (config p) (estimates (config p)) claims +
    6 * ((2 ^ 108 : ℚ) / 2 ^ 192 + 2 ^ 33 / 2 ^ 192) +
    (2 ^ 32 : ℚ) * blockLength (config p) * (6 / 2 ^ 192) +
    (2 ^ 32 : ℚ) * ((oodCount (config p) 0 + (config p).queries[0]! : Nat) / 2 ^ 192)

open Classical in
theorem knowledgeBad_probability (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy)
    (laneBound : lanes ≤ 2 ^ (config p).folds[0]!)
    (shape : ∀ j : Fin claims.size, claims[j].weight.size = 2 ^ (config p).logN) :
    Soundness.uniformProb (Finset.univ.filter (KnowledgeBad p lanes root claims strategy)) ≤
      knowledgeLedger p claims.size := by
  have tail := uniform_or_bound (CancellationEvent p lanes root claims)
    (CollisionEvent p lanes root claims strategy)
    ((2 ^ 32 : ℚ) * blockLength (config p) * (6 / 2 ^ 192))
    ((2 ^ 32 : ℚ) * ((oodCount (config p) 0 + (config p).queries[0]! : Nat) / 2 ^ 192))
    (cancellation_probability p lanes root claims)
    (collisionEvent_probability p lanes root claims strategy)
  have folds := uniform_or_bound (InitialFoldBad p lanes root claims strategy)
    (fun t => CancellationEvent p lanes root claims t ∨ CollisionEvent p lanes root claims strategy t)
    (6 * ((2 ^ 108 : ℚ) / 2 ^ 192 + 2 ^ 33 / 2 ^ 192)) _ 
    (initialFoldBad_probability p lanes root claims strategy) tail
  have all := uniform_or_family_bound (KnowledgeBad p lanes root claims strategy)
    (fun _ : Unit => fun t : Tape (config p) =>
      ∃ q, CausalBadEvents.Bad (Input p lanes root claims) strategy q t)
    (fun _ : Unit => fun t => InitialFoldBad p lanes root claims strategy t ∨
      CancellationEvent p lanes root claims t ∨ CollisionEvent p lanes root claims strategy t)
    (by intro t; simp only [KnowledgeBad, exists_const])
    (GroupedChallenges.interactiveError (config p) (estimates (config p)) claims.size) _
    (fun _ => CausalBadEvents.bad_probability p lanes root claims strategy laneBound shape)
    (fun _ => folds)
  simpa only [Fintype.card_unique, Nat.cast_one, one_mul, knowledgeLedger, add_assoc,
    Nat.cast_ofNat, Nat.cast_pow] using all

/-- Kernel-checked arithmetic for every actual supported configuration. -/
theorem production_extra_ledger : ∀ p : Profile,
    6 * ((2 ^ 108 : ℚ) / 2 ^ 192 + 2 ^ 33 / 2 ^ 192) +
      (2 ^ 32 : ℚ) * blockLength (config p) * (6 / 2 ^ 192) +
      (2 ^ 32 : ℚ) * ((oodCount (config p) 0 + (config p).queries[0]! : Nat) / 2 ^ 192) ≤
        (1 / 2 ^ 80 : ℚ) := by
  decide +kernel

/-- Conservative derived event budget, distinct from the success cutoff and
from any whole-system cryptographic security claim. The public source claims
may number up to the existing actual source cap 2^64. -/
theorem production_knowledgeLedger (p : Profile) (claims : Nat) (cap : claims ≤ 2 ^ 64) :
    knowledgeLedger p claims ≤ (1 / 2 ^ 72 : ℚ) := by
  have main := production_interactive p claims cap
  have extra := production_extra_ledger p
  unfold knowledgeLedger
  have total := add_le_add main extra
  have arithmetic : (1 / 2 ^ 73 : ℚ) + 1 / 2 ^ 80 ≤ 1 / 2 ^ 72 := by norm_num
  calc
    _ ≤ (1 / 2 ^ 73 : ℚ) + 1 / 2 ^ 80 := by
      simpa only [add_assoc, Nat.cast_ofNat, Nat.cast_pow] using total
    _ ≤ _ := arithmetic

open Classical in
theorem production_knowledgeBad (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy)
    (laneBound : lanes ≤ 2 ^ (config p).folds[0]!)
    (shape : ∀ j : Fin claims.size, claims[j].weight.size = 2 ^ (config p).logN)
    (cap : claims.size ≤ 2 ^ 64) :
    Soundness.uniformProb (Finset.univ.filter (KnowledgeBad p lanes root claims strategy)) ≤
      (1 / 2 ^ 72 : ℚ) :=
  (knowledgeBad_probability p lanes root claims strategy laneBound shape).trans
    (production_knowledgeLedger p claims.size cap)

noncomputable def PriorGood (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (t : Tape (config p)) : Prop :=
  (∀ j : Fin (config p).folds[0]!,
    ¬ RawMCA (Input p lanes root claims) strategy (initialLevel p) j t ∧
      ¬ ClaimEscape (Input p lanes root claims) strategy (initialLevel p) j t) ∧
  t.1 ∉ InitialBatching.candidateEscape
    (InitialCandidates.extensionCandidates (config p) lanes root) claims ∧
  ¬ CancellationEvent p lanes root claims t

theorem priorGood_of_not_bad (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (t : Tape (config p))
    (safe : ¬ KnowledgeBad p lanes root claims strategy t) :
    PriorGood p lanes root claims strategy t := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    constructor
    · intro bad
      apply safe
      apply Or.inr
      apply Or.inl
      refine ⟨j, Or.inl ?_⟩
      simpa only [initialLevel] using bad
    · intro bad
      apply safe
      apply Or.inr
      apply Or.inl
      refine ⟨j, Or.inr ?_⟩
      simpa only [initialLevel] using bad
  · intro bad
    exact safe (Or.inl ⟨.initial, bad⟩)
  · intro bad
    exact safe (Or.inr (Or.inr (Or.inl bad)))

theorem priorGood_set (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (t : Tape (config p))
    (q : Coordinate (config p)) (x : Sample q)
    (later : position (.query (initialLevel p)) ≤ position q) :
    PriorGood p lanes root claims strategy (set q t x) ↔ PriorGood p lanes root claims strategy t := by
  have cut := CausalPositions.position_query (initialLevel p) t
  have first : (set q t x).1 = t.1 := by
    change get .initial (set q t x) = get .initial t
    apply get_set_ne q .initial t x
    intro same
    subst q
    change position (.query (initialLevel p)) ≤ 0 at later
    rw [cut] at later
    change levelStart (challenges (config p) t) 0 +
      (config p).folds[0]! + oodCount (config p) 0 ≤ 0 at later
    have positive := CausalStateCausality.levelStart_pos (challenges (config p) t) 0
    omega
  have seeds : ((set q t x).2.1 (initialLevel p)).1 = (t.2.1 (initialLevel p)).1 := by
    funext j
    change get (.fold (initialLevel p) j) (set q t x) = get (.fold (initialLevel p) j) t
    apply get_set_ne q (.fold (initialLevel p) j) t x
    intro same
    have hp := congrArg position same
    rw [CausalPositions.position_fold (initialLevel p) j t] at hp
    omega
  unfold PriorGood CancellationEvent
  rw [first, seeds]
  apply and_congr_left
  intro _
  apply forall_congr'
  intro j
  have foldPosition := CausalPositions.position_fold (initialLevel p) j t
  exact and_congr
    (not_congr (knowledgeEvents_set_future (Input p lanes root claims) strategy t
      (initialLevel p) j q x (by
        change levelStart (challenges (config p) t) (initialLevel p).val+j.val+1 ≤ position q
        omega)).1)
    (not_congr (knowledgeEvents_set_future (Input p lanes root claims) strategy t
      (initialLevel p) j q x (by
        change levelStart (challenges (config p) t) (initialLevel p).val+j.val+1 ≤ position q
        omega)).2)

theorem priorGood_resetCoordinates (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (base fresh : Tape (config p))
    (qs : List (Coordinate (config p))) :
    PriorGood p lanes root claims strategy
      (AuthenticatedResetSupport.resetCoordinates (position (.query (initialLevel p))) fresh qs base) ↔
      PriorGood p lanes root claims strategy base := by
  induction qs generalizing base with
  | nil => rfl
  | cons q qs ih =>
    unfold AuthenticatedResetSupport.resetCoordinates
    rw [ih]
    split_ifs with later
    · exact priorGood_set p lanes root claims strategy base q (get q fresh) later
    · rfl

theorem priorGood_fullResetTape (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (base : Tape (config p))
    (depth : Nat) (chunks) (query) (suffix) :
    PriorGood p lanes root claims strategy
      (AuthenticatedResetSupport.fullResetTape (Input p lanes root claims) base
        (initialLevel p) depth chunks query suffix) ↔ PriorGood p lanes root claims strategy base := by
  unfold AuthenticatedResetSupport.fullResetTape
  rw [priorGood_set p lanes root claims strategy _ (.query (initialLevel p)) _ le_rfl]
  exact priorGood_resetCoordinates p lanes root claims strategy base suffix.2 _

#print axioms knowledgeBad_probability
#print axioms production_knowledgeLedger

end Whir.SupportedCandidateProtocol
