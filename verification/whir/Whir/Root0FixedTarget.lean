import Whir.AuthenticatedResetLaw
import Whir.RewindRadiusExtraction

/-! Full-suffix legal resets preserve the whole following coefficient table list,
not merely a query-only replacement. Root1 replay at j=0 reads no future fold
scalar, even though its type mentions the future fold array. -/
namespace Whir.Root0FixedTarget
open Concrete Protocol CausalGame CausalExecution CausalProbability ExecutionShapes
open AuthenticatedResetSupport CausalStateCausality ParameterBounds RewindBatchTarget

set_option maxRecDepth 100000
set_option maxHeartbeats 200000
attribute [local irreducible] ParameterBounds.config

noncomputable def snapshot (input : Public) (strategy : Strategy) (t : Tape input.config)
    (i : Fin input.config.folds.size) :
    Finset (Array E) × CheckedState × Oracle × Array OodClaim × Array E × Array (Array E) :=
  (followingCandidates input strategy t i,
    CausalBoundary.boundary input strategy t i,
    (levelAt input strategy t i).oracle,
    (proof input strategy t).levels[i.val]!.oods,
    (challenges input.config t).levels[i.val]!.folds,
    (challenges input.config t).levels[i.val]!.oodPoints)

theorem snapshot_set (input : Public) (strategy : Strategy) (t : Tape input.config)
    (i : Fin input.config.folds.size) (q : Coordinate input.config) (x : Sample q)
    (later : position (.query i) ≤ position q) :
    snapshot input strategy (set q t x) i = snapshot input strategy t i := by
  have cut := CausalPositions.position_query i t
  have folds : (challenges input.config (set q t x)).levels[i.val]!.folds =
      (challenges input.config t).levels[i.val]!.folds := by
    simp only [challenges, _root_.getElem!_pos, Array.size_ofFn, i.isLt, Array.getElem_ofFn]
    apply congrArg Array.ofFn
    funext j
    change get (.fold i j) (set q t x) = get (.fold i j) t
    apply get_set_ne q (.fold i j) t x
    intro equal
    have hp := congrArg position equal
    rw [CausalPositions.position_fold i j t] at hp
    omega
  have oods : (challenges input.config (set q t x)).levels[i.val]!.oodPoints =
      (challenges input.config t).levels[i.val]!.oodPoints := by
    simp only [challenges, _root_.getElem!_pos, Array.size_ofFn, i.isLt, Array.getElem_ofFn]
    apply congrArg Array.ofFn
    funext j
    apply congrArg Array.ofFn
    change get (.ood i j) (set q t x) = get (.ood i j) t
    apply get_set_ne q (.ood i j) t x
    intro equal
    have hp := congrArg position equal
    rw [CausalPositions.position_ood i j t] at hp
    omega
  unfold snapshot CausalBoundary.boundary
  rw [CausalBoundary.followingCandidates_set input strategy t q x i (by omega),
    foldAt_set input strategy q t x i _ le_rfl (by omega),
    levelAt_set input strategy q t x i i.isLt.le (by omega),
    CausalBoundary.oods_set input strategy t q x i (by omega), folds, oods]

theorem snapshot_resetCoordinates (input : Public) (strategy : Strategy)
    (base fresh : Tape input.config) (i : Fin input.config.folds.size)
    (qs : List (Coordinate input.config)) :
    snapshot input strategy (resetCoordinates (position (.query i)) fresh qs base) i =
      snapshot input strategy base i := by
  induction qs generalizing base with
  | nil => rfl
  | cons q qs ih =>
    unfold resetCoordinates
    rw [ih]
    split_ifs with later
    · exact snapshot_set input strategy base i q (get q fresh) later
    · rfl

theorem snapshot_fullReset (input : Public) (strategy : Strategy)
    (base fresh : Tape input.config) (i : Fin input.config.folds.size)
    (draw : Sample (.query i)) :
    snapshot input strategy (set (.query i) (resetSuffix (position (.query i)) base fresh) draw) i =
      snapshot input strategy base i := by
  rw [snapshot_set input strategy _ i (.query i) _ le_rfl]
  exact snapshot_resetCoordinates input strategy base fresh i _

theorem snapshot_fullResetTape (input : Public) (strategy : Strategy)
    (base : Tape input.config) (i : Fin input.config.folds.size) (depth : Nat)
    (chunks) (query) (suffix) :
    snapshot input strategy (fullResetTape input base i depth chunks query suffix) i =
      snapshot input strategy base i := by
  unfold fullResetTape
  rw [snapshot_set input strategy _ i (.query i) _ le_rfl]
  exact snapshot_resetCoordinates input strategy base suffix.2 i _

/-- Every accepted safe full reset hits the SAME prefix-fixed OOD target.
The separately charged lambda event uses the incoming suffix-reset tape; its
polynomial is prefix-fixed and does not assume honest OOD advertisements. -/
theorem accepted_full_reset_hits (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (base fresh : Tape (config p))
    (i : Fin (config p).folds.size) (hasNext : i.val+1 < (config p).folds.size)
    (draw : Sample (.query i)) (target : Array E)
    (matching : Target (followingCandidates (Input p lanes root claims) strategy base i)
      (challenges (config p) base).levels[i.val]!.oodPoints[0]!
      (proof (Input p lanes root claims) strategy base).levels[i.val]!.oods[0]!.value target)
    (separated : LevelBoundary.Separated (followingCandidates (Input p lanes root claims) strategy base i)
      (challenges (config p) base).levels[i.val]!.oodPoints[0]!)
    (accepted : experiment (Input p lanes root claims) strategy
      (set (.query i) (resetSuffix (position (.query i)) base fresh) draw) = true)
    (safe : ∀ q, ¬ CausalBadEvents.Bad (Input p lanes root claims) strategy q
      (set (.query i) (resetSuffix (position (.query i)) base fresh) draw))
    (outside : ¬ Collision (remaining (config p) i) (config p).rates[i.val]!
      (config p).queries[i.val]! i
      (levelAt (Input p lanes root claims) strategy (resetSuffix (position (.query i)) base fresh) i).oracle
      (challenges (config p) (resetSuffix (position (.query i)) base fresh)).levels[i.val]!
      (proof (Input p lanes root claims) strategy (resetSuffix (position (.query i)) base fresh)).levels[i.val]!
      (CausalBoundary.boundary (Input p lanes root claims) strategy
        (resetSuffix (position (.query i)) base fresh) i).state
      (followingCandidates (Input p lanes root claims) strategy
        (resetSuffix (position (.query i)) base fresh) i) draw.1 draw.2) :
    SamplingProbability.allQueriesHit (remaining (config p) i + (config p).rates[i.val]!)
      (config p).queries[i.val]!
      (LevelBoundary.agreeingColumns (remaining (config p) i) (config p).rates[i.val]! target
        (QueryBatchSoundness.oldWord (remaining (config p) i) (config p).rates[i.val]!
          (levelAt (Input p lanes root claims) strategy base i).oracle (i.val == 0)
          (challenges (config p) base).levels[i.val]!.folds)) draw.1 := by
  let input := Input p lanes root claims
  have fixed := snapshot_resetCoordinates input strategy base fresh i
    (visibleCoordinates input.config ++ List.ofFn (fun j : Fin (input.config.logN-input.config.folds.toList.sum) => Coordinate.tail j))
  change snapshot input strategy (resetSuffix (position (.query i)) base fresh) i = snapshot input strategy base i at fixed
  have list := congrArg (fun s => s.1) fixed
  have oracle := congrArg (fun s => s.2.2.1) fixed
  have answers := congrArg (fun s => s.2.2.2.1) fixed
  have folds := congrArg (fun s => s.2.2.2.2.1) fixed
  have points := congrArg (fun s => s.2.2.2.2.2) fixed
  dsimp only [snapshot] at list oracle answers folds points
  have matchingSuffix : Target (followingCandidates input strategy (resetSuffix (position (.query i)) base fresh) i)
      (challenges (config p) (resetSuffix (position (.query i)) base fresh)).levels[i.val]!.oodPoints[0]!
      (proof input strategy (resetSuffix (position (.query i)) base fresh)).levels[i.val]!.oods[0]!.value target := by
    unfold Target at matching ⊢
    rw [list, points, answers]
    exact matching
  have separatedSuffix : LevelBoundary.Separated
      (followingCandidates input strategy (resetSuffix (position (.query i)) base fresh) i)
      (challenges (config p) (resetSuffix (position (.query i)) base fresh)).levels[i.val]!.oodPoints[0]! := by
    rw [list, points]
    exact separated
  have hits := RewindRadiusExtraction.accepted_reset_fixed_target p lanes root claims strategy
    (resetSuffix (position (.query i)) base fresh) i hasNext draw target
    matchingSuffix separatedSuffix accepted safe outside
  rw [oracle, folds] at hits
  exact hits

/-- An arbitrary advertised OOD value is allowed. A safe accepted continuation
itself produces a matching candidate with the pre-query running claim; if the
advertised value matches none, such a continuation cannot exist. -/
theorem accepted_reset_target_exists (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (t : Tape (config p))
    (i : Fin (config p).folds.size) (hasNext : i.val+1 < (config p).folds.size)
    (draw : Sample (.query i))
    (accepted : experiment (Input p lanes root claims) strategy (set (.query i) t draw) = true)
    (safe : ∀ q, ¬ CausalBadEvents.Bad (Input p lanes root claims) strategy q (set (.query i) t draw))
    (outside : ¬ Collision (remaining (config p) i) (config p).rates[i.val]!
      (config p).queries[i.val]! i (levelAt (Input p lanes root claims) strategy t i).oracle
      (challenges (config p) t).levels[i.val]!
      (proof (Input p lanes root claims) strategy t).levels[i.val]!
      (CausalBoundary.boundary (Input p lanes root claims) strategy t i).state
      (followingCandidates (Input p lanes root claims) strategy t i) draw.1 draw.2) :
    ∃ target, Target (followingCandidates (Input p lanes root claims) strategy t i)
      (challenges (config p) t).levels[i.val]!.oodPoints[0]!
      (proof (Input p lanes root claims) strategy t).levels[i.val]!.oods[0]!.value target ∧
      dot target (CausalBoundary.boundary (Input p lanes root claims) strategy t i).state.weight =
        (CausalBoundary.boundary (Input p lanes root claims) strategy t i).state.claim := by
  let input := Input p lanes root claims
  have restored := accepted_reset_restores p lanes root claims strategy t i hasNext draw accepted safe
  have facts := CausalBoundary.production_boundary_facts p i
  have sizes := CausalBoundary.followingCandidates_sizes input strategy t p rfl i
    (by intro impossible; exact (impossible hasNext).elim)
  have weight : (CausalBoundary.boundary input strategy t i).state.weight.size =
      2 ^ remaining (config p) i := by
    have shape := (foldAt_shape p lanes root claims strategy t i (config p).folds[i.val]! le_rfl).2
    simpa only [CausalBoundary.boundary, input, Nat.sub_self, Nat.add_zero] using shape
  have oods : ∀ j < (proof input strategy t).levels[i.val]!.oods.size,
      (eqTable (challenges (config p) t).levels[i.val]!.oodPoints[j]!).size =
        2 ^ remaining (config p) i := by
    intro j bound
    rw [CausalBoundary.decoded_oods_size] at bound
    exact CausalBoundary.point_size input t i j bound
  have first : 0 < (proof input strategy t).levels[i.val]!.oods.size := by
    rw [CausalBoundary.decoded_oods_size]
    exact (facts.2.2 hasNext).2
  obtain ⟨target, member, zero⟩ := restores_zero_candidate _ _ _ _ _ _ _ _ _ _ _
    sizes weight oods draw restored outside
  have hits := zero_error_hits _ _ _ _ _ _ _ _ draw.1 target facts.1 facts.2.1 zero
  exact ⟨target, ⟨member, hits.2.1 0 first⟩, hits.1⟩

#print axioms snapshot_fullResetTape
#print axioms accepted_full_reset_hits
#print axioms accepted_reset_target_exists
end Whir.Root0FixedTarget
