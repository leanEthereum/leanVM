import Whir.WHIRFiatShamir
import Whir.PCSRoundByRoundCausalEvents

/-! General response-independent WHIR envelopes. There is no public claim-count
cap here: the local loss retains the actual public claim count. -/
namespace Whir.PCSRoundByRoundEnvelope
open Concrete Protocol CausalGame CausalProbability CausalExecution ParameterBounds
open CausalPositions CausalStateCausality WHIRFiatShamir
open scoped BigOperators
open Classical
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
attribute [local irreducible] ParameterBounds.config

noncomputable def core (input : Public) (strategy : Strategy) (q : Coordinate input.config)
    (t : Tape input.config) : Prop := Envelope input strategy q t (get q t)

 theorem query_bad_cover (p : Profile) (input : Public) (profile : input.config = config p)
    (strategy : Strategy) (i : Fin input.config.folds.size) (t : Tape input.config)
    (x : Sample (.query i))
    (bad : CausalBoundary.QueryEvent input strategy i (set (.query i) t x)) :
    QueryEnvelope input strategy i t x := by
  rcases input with ⟨c,lanes,root,claims⟩
  dsimp only at profile
  subst c
  let input : Public := ⟨config p,lanes,root,claims⟩
  have facts := CausalBoundary.production_boundary_facts p i
  obtain ⟨prior,restores⟩ := CausalBoundary.query_event_fiber input strategy t i x facts.1 facts.2.1 bad
  exact ⟨prior,canonical_query_restores _ _ _ _ _ _ _ _ _ _ _ _ restores⟩

 theorem query_fiber_bound (p : Profile) (input : Public) (profile : input.config = config p)
    (strategy : Strategy) (i : Fin input.config.folds.size) (t : Tape input.config) :
    Soundness.uniformProb (Finset.univ.filter (QueryEnvelope input strategy i t)) ≤
      GroupedChallenges.queryBatchError input.config (ParameterBounds.estimates input.config) i := by
  classical
  by_cases prior : CausalBoundary.QueryPrior input strategy i t
  · have bound := CausalBoundary.actual_transition input strategy t p profile i
      (fun tape _ => (QueryBatchSoundness.queries
        (remaining input.config i + input.config.rates[i.val]!) input.config.queries[i.val]! tape).map
        (fun q => (levelAt input strategy t i).oracle[q]!))
      (fun _ _ => default) prior.2.1 prior.2.2.1 prior.2.2.2
    unfold QueryEnvelope
    simp only [prior,true_and]
    exact bound
  · have empty : (Finset.univ.filter (QueryEnvelope input strategy i t)) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro x hx event
      exact prior event.1
    rw [empty]
    simp only [Soundness.uniformProb, Finset.card_empty, Nat.cast_zero, zero_div]
    have alphaBound : 0 < ParameterBounds.alpha input.config.rates[i.val]! := by
      rcases input with ⟨c,lanes,root,claims⟩
      dsimp only at profile
      subst c
      exact (production_level_facts p i).2.2.2.2.2.2.1
    unfold GroupedChallenges.queryBatchError ParameterBounds.estimates GroupedChallenges.fieldSize
    split_ifs <;> positivity

/-- Raw bad-event cover derived from the authenticated actual transition. -/
theorem bad_cover (p : Profile) (lanes : Nat) (root : BaseOracle) (claims : Array Claim)
    (strategy : Strategy) (q : Coordinate (config p)) (t : Tape (config p))
    (bad : CausalBadEvents.Bad (ExecutionShapes.Input p lanes root claims) strategy q t) :
    core (ExecutionShapes.Input p lanes root claims) strategy q t := by
  unfold core
  cases q with
  | query i =>
    change CausalBoundary.QueryEvent (ExecutionShapes.Input p lanes root claims) strategy i t at bad
    apply query_bad_cover p _ rfl
    simpa only [set_get] using bad
  | initial => simpa only [Envelope,set_get] using bad
  | fold i j => simpa only [Envelope,set_get] using bad
  | ood i j => simpa only [Envelope,set_get] using bad
  | tail j => simpa only [Envelope,set_get] using bad

private theorem restores_fields (n rate count i : Nat) (root : Oracle)
    (cs ds : LevelChallenges) (p q : LevelProof) (state : VerifierState E)
    (candidates : Finset (Array E))
    (rowsAt : LevelBoundary.QueryTape (n+rate) count → E → Oracle)
    (introAt : LevelBoundary.QueryTape (n+rate) count → E → Message E)
    (x : LevelBoundary.QueryTape (n+rate) count × E)
    (folds : cs.folds = ds.folds) (points : cs.oodPoints = ds.oodPoints)
    (oods : p.oods = q.oods) :
    QueryBatchSoundness.Restores n rate count i root cs p state candidates rowsAt introAt x ↔
      QueryBatchSoundness.Restores n rate count i root ds q state candidates rowsAt introAt x := by
  cases cs
  cases ds
  cases p
  cases q
  cases folds
  cases points
  cases oods
  rfl

/-- Replacing the current tape draw cannot reveal a current prover response in
an envelope: query rows are canonical, and the current intro is overwritten. -/
theorem Envelope_self_set (input : Public) (strategy : Strategy) (q : Coordinate input.config)
    (t : Tape input.config) (x y : Sample q) :
    Envelope input strategy q (set q t x) y ↔ Envelope input strategy q t y := by
  cases q with
  | query i =>
    change QueryEnvelope input strategy i (set (.query i) t x) y ↔ QueryEnvelope input strategy i t y
    dsimp only [QueryEnvelope]
    rw [CausalBoundary.query_prior_set, CausalBoundary.query_level_set,
      CausalBoundary.query_boundary_set,
      CausalBoundary.followingCandidates_set input strategy t (.query i) x i (by
        rw [position_query i t]; omega)]
    apply and_congr_right
    intro prior
    apply restores_fields
    · rw [CausalBoundary.query_challenges]
    · rw [CausalBoundary.query_challenges]
    · apply CausalBoundary.oods_set
      rw [position_query i t]
  | initial => simp only [Envelope,set_set]
  | fold i j => simp only [Envelope,set_set]
  | ood i j => simp only [Envelope,set_set]
  | tail j => simp only [Envelope,set_set]

open Classical in
 theorem envelope_fiber (p : Profile) (lanes : Nat) (root : BaseOracle) (claims : Array Claim)
    (laneBound : lanes ≤ 2^(config p).folds[0]!)
    (shape : ∀ j : Fin claims.size, claims[j].weight.size = 2^(config p).logN)
    (strategy : Strategy) (q : Coordinate (config p)) (t : Tape (config p)) :
    Soundness.uniformProb (Finset.univ.filter
      (Envelope (ExecutionShapes.Input p lanes root claims) strategy q t)) ≤
      CausalBadEvents.localError (ExecutionShapes.Input p lanes root claims) q := by
  cases q with
  | query i =>
    convert query_fiber_bound p (ExecutionShapes.Input p lanes root claims) rfl strategy i t using 1 <;> rfl
  | initial => exact CausalBadEvents.fiber_bound p lanes root claims laneBound shape strategy .initial t
  | fold i j => exact CausalBadEvents.fiber_bound p lanes root claims laneBound shape strategy (.fold i j) t
  | ood i j => exact CausalBadEvents.fiber_bound p lanes root claims laneBound shape strategy (.ood i j) t
  | tail j => exact CausalBadEvents.fiber_bound p lanes root claims laneBound shape strategy (.tail j) t

open Classical in
 theorem fiber_bound (p : Profile) (lanes : Nat) (root : BaseOracle) (claims : Array Claim)
    (laneBound : lanes ≤ 2^(config p).folds[0]!)
    (shape : ∀ j : Fin claims.size, claims[j].weight.size = 2^(config p).logN)
    (strategy : Strategy) (q : Coordinate (config p)) (t : Tape (config p)) :
    Soundness.uniformProb (Finset.univ.filter fun x : Sample q =>
      core (ExecutionShapes.Input p lanes root claims) strategy q (set q t x)) ≤
      CausalBadEvents.localError (ExecutionShapes.Input p lanes root claims) q := by
  unfold core
  simp_rw [get_set,Envelope_self_set]
  exact envelope_fiber p lanes root claims laneBound shape strategy q t

private theorem set_comm {c : Config} (q r : Coordinate c) (t : Tape c)
    (x : Sample q) (y : Sample r) (different : r ≠ q) :
    set r (set q t x) y = set q (set r t y) x := by
  apply (coordinates c).injective
  funext s
  change get s (set r (set q t x) y) = get s (set q (set r t y) x)
  by_cases sr : s = r
  · subst s
    rw [get_set, get_set_ne _ _ _ _ different, get_set]
  · by_cases sq : s = q
    · subst s
      rw [get_set_ne _ _ _ _ (Ne.symm different),get_set,get_set]
    · rw [get_set_ne _ _ _ _ sr,get_set_ne _ _ _ _ sq,
        get_set_ne _ _ _ _ sq,get_set_ne _ _ _ _ sr]

private theorem query_future (input : Public) (strategy : Strategy)
    (i : Fin input.config.folds.size) (q : Coordinate input.config) (t : Tape input.config)
    (x : Sample q) (y : Sample (.query i)) (later : position (.query i) < position q) :
    QueryEnvelope input strategy i (set q t x) y ↔ QueryEnvelope input strategy i t y := by
  have endBefore : levelStart (challenges input.config t) (i.val+1) ≤ position q := by
    rw [position_query i t] at later
    rw [CausalRefinement.levelStart_succ,challenge_folds_size,challenge_oods_size]
    omega
  have before : levelStart (challenges input.config t) i.val + input.config.folds[i.val]! ≤ position q := by
    rw [position_query i t] at later
    omega
  have level := levelAt_set input strategy q t x i i.isLt.le (by omega)
  have state := foldAt_set input strategy q t x i input.config.folds[i.val]! le_rfl before
  change CausalBoundary.boundary input strategy (set q t x) i = CausalBoundary.boundary input strategy t i at state
  have list := CausalBoundary.followingCandidates_set input strategy t q x i before
  have cs := challenge_level_set input.config q t x i endBefore
  have proofLevel := proof_level_set input strategy q t x i endBefore
  dsimp only [QueryEnvelope,CausalBoundary.QueryPrior]
  simp only [level,state,list,cs,proofLevel]
  by_cases last : i.val+1 < input.config.folds.size
  · simp only [last,ite_true]
  · simp only [last,ite_false,CausalBoundary.residual_set input strategy t q x i last before]

/-- The whole envelope function is invariant under every future coordinate. -/
theorem envelope_future (input : Public) (strategy : Strategy)
    (valid : input.config.valid = true) (r q : Coordinate input.config)
    (t : Tape input.config) (x : Sample q) (y : Sample r) (later : position r < position q) :
    Envelope input strategy r (set q t x) y ↔ Envelope input strategy r t y := by
  have different : r ≠ q := by intro h; subst r; omega
  cases r with
  | query i => exact query_future input strategy i q t x y later
  | initial =>
    dsimp only [Envelope]
    rw [set_comm q .initial t x y different]
    exact PCSRoundByRoundCausalEvents.bad_set_future input strategy valid .initial q _ x later
  | fold i j =>
    dsimp only [Envelope]
    rw [set_comm q (.fold i j) t x y different]
    exact PCSRoundByRoundCausalEvents.bad_set_future input strategy valid (.fold i j) q _ x later
  | ood i j =>
    dsimp only [Envelope]
    rw [set_comm q (.ood i j) t x y different]
    exact PCSRoundByRoundCausalEvents.bad_set_future input strategy valid (.ood i j) q _ x later
  | tail j =>
    dsimp only [Envelope]
    rw [set_comm q (.tail j) t x y different]
    exact PCSRoundByRoundCausalEvents.bad_set_future input strategy valid (.tail j) q _ x later

 theorem future_invariant (p : Profile) (lanes : Nat) (root : BaseOracle) (claims : Array Claim)
    (strategy : Strategy) (r q : Coordinate (config p)) (t : Tape (config p))
    (x : Sample q) (later : position r < position q) :
    core (ExecutionShapes.Input p lanes root claims) strategy r (set q t x) ↔
      core (ExecutionShapes.Input p lanes root claims) strategy r t := by
  unfold core
  rw [get_set_ne q r t x (by intro h; subst r; omega)]
  exact envelope_future (ExecutionShapes.Input p lanes root claims) strategy
    (production_config_valid p).1 r q t x (get r t) later

private theorem finite_pred_congr {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*}
    (P : ((i : I) → A i) → Prop) (locked : I → Prop)
    (step : ∀ f i, ¬ locked i → ∀ x, P (Function.update f i x) ↔ P f)
    (f g : (i : I) → A i) (same : ∀ i, locked i → f i = g i) : P f ↔ P g := by
  have repair (s : Finset I) : ∀ f g : (i : I) → A i,
      (∀ i, i ∉ s → f i = g i) →
      (∀ i, locked i → f i = g i) → (P f ↔ P g) := by
    induction s using Finset.induction_on with
    | empty =>
      intro f g outside _
      have equal : f = g := funext fun i => outside i (by simp)
      rw [equal]
    | @insert i s absent ih =>
      intro f g outside fixed
      by_cases equal : f i = g i
      · apply ih f g ?_ fixed
        intro j hj
        by_cases ji : j = i
        · subst j; exact equal
        · exact outside j (by simp [hj,ji])
      · have unlocked : ¬ locked i := fun h => equal (fixed i h)
        let mid := Function.update f i (g i)
        have outside' : ∀ j, j ∉ s → mid j = g j := by
          intro j hj
          by_cases ji : j = i
          · subst j; simp [mid]
          · simpa only [mid,Function.update_of_ne ji] using outside j (by simp [hj,ji])
        have fixed' : ∀ j, locked j → mid j = g j := by
          intro j hj
          have ji : j ≠ i := by intro equal; subst j; exact unlocked hj
          simpa only [mid,Function.update_of_ne ji] using fixed j hj
        exact (step f i unlocked (g i)).symm.trans (ih mid g outside' fixed')
  exact repair Finset.univ f g (by intro i impossible; simp at impossible) same

/-- The envelope function sees only strict-past draws. In particular neither
the current response nor any later random draw participates in allocation. -/
theorem Envelope_prefix_congr (input : Public) (strategy : Strategy)
    (valid : input.config.valid = true) (q : Coordinate input.config)
    (t u : Tape input.config) (y : Sample q)
    (same : ∀ r, position r < position q → get r t = get r u) :
    Envelope input strategy q t y ↔ Envelope input strategy q u y := by
  let P := fun f : (r : Coordinate input.config) → Sample r =>
    Envelope input strategy q ((coordinates input.config).symm f) y
  have step : ∀ f r, ¬ position r < position q → ∀ x,
      P (Function.update f r x) ↔ P f := by
    intro f r later x
    have replaced : (coordinates input.config).symm (Function.update f r x) =
        set r ((coordinates input.config).symm f) x := by
      simp only [CausalProbability.set,Equiv.apply_symm_apply]
    dsimp only [P]
    rw [replaced]
    by_cases equal : r = q
    · subst r
      exact Envelope_self_set input strategy q _ x y
    · have distinct : position r ≠ position q :=
        fun h => equal (CausalPrefix.position_injective input.config h)
      exact envelope_future input strategy valid q r _ x y (by omega)
  have result := finite_pred_congr P (fun r => position r < position q) step
    (coordinates input.config t) (coordinates input.config u) same
  simpa only [P,Equiv.symm_apply_apply] using result

theorem prefix_invariant (p : Profile) (lanes : Nat) (root : BaseOracle) (claims : Array Claim)
    (strategy : Strategy) (q : Coordinate (config p)) (t u : Tape (config p))
    (same : ∀ r, position r ≤ position q → get r t = get r u) :
    core (ExecutionShapes.Input p lanes root claims) strategy q t ↔
      core (ExecutionShapes.Input p lanes root claims) strategy q u := by
  unfold core
  rw [same q le_rfl]
  exact Envelope_prefix_congr (ExecutionShapes.Input p lanes root claims) strategy
    (production_config_valid p).1 q t u (get q u) (fun r hr => same r hr.le)

#print axioms bad_cover
#print axioms fiber_bound
#print axioms Envelope_self_set
#print axioms future_invariant
#print axioms Envelope_prefix_congr
#print axioms prefix_invariant
end Whir.PCSRoundByRoundEnvelope
