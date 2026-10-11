import Whir.RewindTrajectory
import Whir.QueryBatchSoundness

/-! Witness-specific reset batching: authentication fixes rows even for a prover seeing the entire query tape and lambda. A nonzero batched-error collision is charged explicitly. Outside that event, restoration implies actual all-query-hit for a candidate selected by an already advertised OOD answer. Wrong advertised OOD answers remain permitted; they make successful restoration impossible outside the charged event when no candidate matches. -/
namespace Whir.RewindBatchTarget
open Concrete Protocol CausalGame CausalExecution ExecutionShapes ParameterBounds VerifierInvariant
open LevelBoundary BatchingRefinement QueryBatchSoundness
open scoped BigOperators

open CausalProbability Classical
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
/-- Candidates, oracle, fold challenges, OOD points/answers and prior state are fixed before the adjacent query/lambda message. -/
def Collision (n rate count i : Nat) (root : Oracle) (cs : LevelChallenges)
    (p : LevelProof) (state : VerifierState E) (candidates : Finset (Array E))
    (tape : QueryTape (n + rate) count) (lambda : E) : Prop :=
  ∃ candidate ∈ candidates,
    polynomial n rate count i root cs p state tape candidate ≠ 0 ∧
      (polynomial n rate count i root cs p state tape candidate).eval lambda = 0

/-- The OOD target is determined by the fixed list and the actual advertised point/value, not by queries or lambda. -/
def Target (candidates : Finset (Array E)) (point : Array E) (answer : E) (candidate : Array E) : Prop :=
  candidate ∈ candidates ∧ Concrete.mle candidate point = answer

theorem target_unique (candidates : Finset (Array E)) (point : Array E) (answer : E)
    (separated : Separated candidates point) (left right : Array E)
    (hl : Target candidates point answer left) (hr : Target candidates point answer right) :
    left = right := separated left hl.1 right hr.1 (hl.2.trans hr.2.symm)

/-- Every coefficient is interpreted using the real query sampler and actual authenticated oracle rows. -/
theorem zero_error_hits (n rate count i : Nat) (root : Oracle)
    (cs : LevelChallenges) (p : LevelProof) (state : VerifierState E)
    (tape : QueryTape (n + rate) count) (candidate : Array E)
    (positive : 0 < n + rate) (noWrap : n + rate ≤ 64)
    (zero : polynomial n rate count i root cs p state tape candidate = 0) :
    dot candidate state.weight = state.claim ∧
      (∀ j < p.oods.size, Concrete.mle candidate cs.oodPoints[j]! = p.oods[j]!.value) ∧
      SamplingProbability.allQueriesHit (n + rate) count
        (agreeingColumns n rate candidate (oldWord n rate root (i == 0) cs.folds)) tape := by
  have coefficient := congrArg (fun x : Polynomial E => x.coeff 0) zero
  have residual : dot candidate state.weight = state.claim := by
    simpa [polynomial, errorPolynomial, batchPolynomial_coeff_zero, discrepancy,
      sub_eq_zero] using coefficient
  refine ⟨residual, ?_, queries (n + rate) count tape,
    queries_actual _ _ _ positive noWrap, ?_⟩
  · intro j hj
    have coefficient := congrArg (fun x : Polynomial E => x.coeff (j + 1)) zero
    simpa only [polynomial, errorPolynomial, batchPolynomial_coeff_ood _ _ _ _ _ _ hj,
      Polynomial.coeff_zero, oodError, Concrete.mle, sub_eq_zero] using coefficient
  · intro j
    have coefficient := congrArg (fun x : Polynomial E => x.coeff (p.oods.size + 1 + j.val)) zero
    have hj : j.val < (queries (n + rate) count tape).size := by
      rw [queries_size]
      exact j.isLt
    have error : queryError candidate n cs
        {p with rows := (queries (n + rate) count tape).map (fun q => root[q]!)}
        (queries (n + rate) count tape) (i == 0) j.val = 0 := by
      simpa only [polynomial, errorPolynomial,
        batchPolynomial_coeff_query _ _ _ _ _ _ hj, Polynomial.coeff_zero] using coefficient
    classical
    apply Finset.mem_image.mpr
    refine ⟨⟨_, queries_bound _ _ _ _ j.isLt⟩, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change (encode n rate candidate)[(queries (n + rate) count tape)[j.val]!]! = _
    rw [encode, ArrayLayout.getElem!_tab _ _ _ (queries_bound _ _ _ _ j.isLt)]
    simpa [queryError, oldWord, getElem!_pos, hj, sub_eq_zero] using error

/-- This conclusion holds for arbitrary adaptive query replies; rows are fixed only by the actual authentication guard. -/
theorem restores_zero_candidate (n rate count i : Nat) (root : Oracle)
    (cs : LevelChallenges) (p : LevelProof) (state : VerifierState E)
    (candidates : Finset (Array E))
    (rowsAt : QueryTape (n + rate) count → E → Oracle)
    (introAt : QueryTape (n + rate) count → E → Message E)
    (sizes : ∀ f ∈ candidates, f.size = 2 ^ n) (weight : state.weight.size = 2 ^ n)
    (oods : ∀ j < p.oods.size, (eqTable cs.oodPoints[j]!).size = 2 ^ n)
    (draw : QueryTape (n + rate) count × E)
    (restores : Restores n rate count i root cs p state candidates rowsAt introAt draw)
    (outside : ¬ Collision n rate count i root cs p state candidates draw.1 draw.2) :
    ∃ candidate ∈ candidates, polynomial n rate count i root cs p state draw.1 candidate = 0 := by
  classical
  obtain ⟨rows, auth, notLost⟩ := restores
  simp only [Lost, not_forall, not_not] at notLost
  obtain ⟨candidate, member, truth⟩ := notLost
  have identity := authenticated_batch_vary_lambda candidate n i cs p
    (queries (n + rate) count draw.1) root state (rowsAt draw.1) (introAt draw.1)
    (sizes candidate member) (weight.trans (sizes candidate member).symm)
    (by intro j hj; exact (oods j hj).trans (sizes candidate member).symm) draw.2 rows
    ((OperationalRefinement.authentication_ok_iff _ _ _).mp auth)
  have evaluated : (polynomial n rate count i root cs p state draw.1 candidate).eval draw.2 = 0 := by
    change (errorPolynomial candidate n i cs
      {p with rows := (queries (n + rate) count draw.1).map (fun q => root[q]!)}
      (queries (n + rate) count draw.1) state).eval draw.2 = 0
    rw [← identity]
    exact sub_eq_zero.mpr truth
  refine ⟨candidate, member, ?_⟩
  by_contra nonzero
  exact outside ⟨candidate, member, nonzero, evaluated⟩

/-- A restored candidate outside lambda collisions is the unique fixed advertised-OOD target and hits every actual query. No honest OOD-answer assumption is made. -/
theorem restores_fixed_target (n rate count i : Nat) (root : Oracle)
    (cs : LevelChallenges) (p : LevelProof) (state : VerifierState E)
    (candidates : Finset (Array E))
    (rowsAt : QueryTape (n + rate) count → E → Oracle)
    (introAt : QueryTape (n + rate) count → E → Message E)
    (sizes : ∀ f ∈ candidates, f.size = 2 ^ n) (weight : state.weight.size = 2 ^ n)
    (oods : ∀ j < p.oods.size, (eqTable cs.oodPoints[j]!).size = 2 ^ n)
    (positive : 0 < n + rate) (noWrap : n + rate ≤ 64) (first : 0 < p.oods.size)
    (target : Array E) (matching : Target candidates cs.oodPoints[0]! p.oods[0]!.value target)
    (separated : Separated candidates cs.oodPoints[0]!)
    (draw : QueryTape (n + rate) count × E)
    (restores : Restores n rate count i root cs p state candidates rowsAt introAt draw)
    (outside : ¬ Collision n rate count i root cs p state candidates draw.1 draw.2) :
    SamplingProbability.allQueriesHit (n + rate) count
      (agreeingColumns n rate target (oldWord n rate root (i == 0) cs.folds)) draw.1 := by
  obtain ⟨candidate, member, zero⟩ := restores_zero_candidate n rate count i root cs p state
    candidates rowsAt introAt sizes weight oods draw restores outside
  have hits := zero_error_hits n rate count i root cs p state draw.1 candidate positive noWrap zero
  have same := target_unique candidates cs.oodPoints[0]! p.oods[0]!.value separated
    candidate target ⟨member, hits.2.1 0 first⟩ matching
  simpa only [same] using hits.2.2

private theorem batch_fields_congr (n i : Nat) (cs : LevelChallenges)
    (p q : LevelProof) (qs : Array Nat) (state : VerifierState E)
    (oods : p.oods = q.oods) (rows : p.rows = q.rows) (intro : p.intro = q.intro) :
    queryBatch n i cs p qs (oodBatch cs p state) =
      queryBatch n i cs q qs (oodBatch cs q state) := by
  cases p
  cases q
  cases oods
  cases rows
  cases intro
  rfl

/-- Actual accepted reset continuations imply restoration in the same fixed-public causal interface. The committed next list, prior state and advertised OODs are fixed before the reset query draw; only adaptive rows and intro vary. -/
theorem accepted_reset_restores (profile : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (tape : Tape (config profile))
    (level : Fin (config profile).folds.size)
    (hasNext : level.val + 1 < (config profile).folds.size)
    (draw : Sample (.query level))
    (accepted : experiment (Input profile lanes root claims) strategy (set (.query level) tape draw) = true)
    (safe : ∀ q, ¬ CausalBadEvents.Bad (Input profile lanes root claims) strategy q
      (set (.query level) tape draw)) :
    Restores (remaining (config profile) level) (config profile).rates[level.val]!
      (config profile).queries[level.val]! level
      (levelAt (Input profile lanes root claims) strategy tape level).oracle
      (challenges (config profile) tape).levels[level.val]!
      (proof (Input profile lanes root claims) strategy tape).levels[level.val]!
      (CausalBoundary.boundary (Input profile lanes root claims) strategy tape level).state
      (followingCandidates (Input profile lanes root claims) strategy tape level)
      (CausalBoundary.queryRows (Input profile lanes root claims) strategy tape level)
      (CausalBoundary.queryIntro (Input profile lanes root claims) strategy tape level) draw := by
  let input := Input profile lanes root claims
  let reset := set (.query level) tape draw
  have candidate := RewindTrajectory.accepted_following_candidate profile lanes root claims strategy
    reset accepted level hasNext safe
  have failure : ¬ Lost (followingCandidates input strategy reset level)
      (levelAt input strategy reset (level.val + 1)).state := by
    obtain ⟨witness, member, truth⟩ := candidate
    intro lost
    exact lost witness member truth
  have checked := accepted_level input strategy reset accepted level level.isLt
  have result := OperationalRefinement.verifyLevel_success _ _ _ level _ _ checked
  dsimp only at result
  have endEq := foldAt_end input strategy reset level level.isLt
  dsimp only [block] at endEq
  rw [← endEq] at result
  have dims := (foldAt_shape profile lanes root claims strategy reset level
    (config profile).folds[level.val]! le_rfl).1
  simp only [Nat.sub_self, Nat.add_zero] at dims
  rw [dims, foldAt_oracle] at result
  obtain ⟨_, _, qs, sampled, rows, auth, _⟩ := result
  have derived : qs = (deriveQueries (remaining (config profile) level +
      (config profile).rates[level.val]!) (config profile).queries[level.val]!
      (challenges (config profile) reset).levels[level.val]!.querySqueezes).getD #[] := by
    rw [sampled]
    rfl
  rw [derived] at rows auth
  have bounds := CausalBoundary.production_boundary_facts profile level
  have sampledReset :
      (deriveQueries (remaining (config profile) level + (config profile).rates[level.val]!)
        (config profile).queries[level.val]!
        (challenges (config profile) reset).levels[level.val]!.querySqueezes).getD #[] =
      queries (remaining (config profile) level + (config profile).rates[level.val]!)
        (config profile).queries[level.val]! draw.1 := by
    rw [CausalBoundary.query_challenges input tape level draw]
    dsimp only
    erw [queries_actual _ _ draw.1 bounds.1 bounds.2.1]
    rfl
  have fixed := CausalBoundary.followingCandidates_set input strategy tape (.query level) draw level
    (by dsimp only [input]; rw [CausalPositions.position_query level tape]; omega)
  have answers := CausalBoundary.oods_set input strategy tape (.query level) draw level
    (by rw [CausalPositions.position_query])
  change ¬ Lost (followingCandidates input strategy (set (.query level) tape draw) level)
    (levelAt input strategy (set (.query level) tape draw) (level.val + 1)).state at failure
  have dimension : (CausalBoundary.boundary input strategy reset level).n =
      remaining (config profile) level := dims
  rw [CausalBoundary.next_state, dimension, sampledReset, fixed,
    CausalBoundary.query_boundary_set, CausalBoundary.query_challenges] at failure
  rw [sampledReset] at rows auth
  rw [CausalBoundary.query_level_set] at auth
  unfold Restores
  dsimp only [CausalBoundary.queryRows, CausalBoundary.queryIntro]
  refine ⟨rows, (OperationalRefinement.authentication_ok_iff _ _ _).mpr auth, ?_⟩
  have kernel := batch_fields_congr (remaining (config profile) level) level
    { (challenges (config profile) tape).levels[level.val]! with
      querySqueezes := Array.ofFn draw.1, lambda := draw.2 }
    (proof input strategy reset).levels[level.val]!
    { (proof input strategy tape).levels[level.val]! with
      rows := (proof input strategy reset).levels[level.val]!.rows
      intro := (proof input strategy reset).levels[level.val]!.intro }
    (queries (remaining (config profile) level + (config profile).rates[level.val]!)
      (config profile).queries[level.val]! draw.1)
    (CausalBoundary.boundary input strategy tape level).state answers rfl rfl
  erw [kernel] at failure
  exact failure

#print axioms accepted_reset_restores

private theorem nonzero_collision_bound {F I : Type*} [CommRing F] [IsDomain F] [Fintype F]
    [DecidableEq F] [DecidableEq I] (candidates : Finset I) (polynomials : I → Polynomial F)
    (degree : Nat) (degrees : ∀ candidate ∈ candidates, (polynomials candidate).natDegree ≤ degree)
    (event : F → Prop) [DecidablePred event]
    (covered : ∀ lambda, event lambda → ∃ candidate ∈ candidates, polynomials candidate ≠ 0 ∧
      (polynomials candidate).eval lambda = 0) :
    Soundness.uniformProb (Finset.univ.filter event) ≤
      (candidates.card : ℚ) * ((degree : ℚ) / Fintype.card F) := by
  classical
  let active := candidates.filter (fun candidate => polynomials candidate ≠ 0)
  let errors (candidate : active) := polynomials candidate.val
  have subset : Finset.univ.filter event ⊆ Finset.univ.biUnion (fun candidate : active =>
        Finset.univ.filter fun lambda : F => (errors candidate).eval lambda = 0) := by
    intro lambda member
    obtain ⟨candidate, belongs, nonzero, evaluated⟩ :=
      covered lambda (Finset.mem_filter.mp member).2
    exact Finset.mem_biUnion.mpr
      ⟨⟨candidate, Finset.mem_filter.mpr ⟨belongs, nonzero⟩⟩, Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, evaluated⟩⟩
  have nonzero (candidate : active) : errors candidate ≠ 0 :=
    (Finset.mem_filter.mp candidate.property).2
  have small (candidate : active) : (errors candidate).natDegree ≤ degree :=
    degrees candidate.val (Finset.mem_filter.mp candidate.property).1
  have first : Soundness.uniformProb (Finset.univ.filter event) ≤
      Soundness.uniformProb (Finset.univ.biUnion (fun candidate : active =>
        Finset.univ.filter fun lambda : F => (errors candidate).eval lambda = 0)) := by
    unfold Soundness.uniformProb
    apply div_le_div_of_nonneg_right
    · exact_mod_cast Finset.card_le_card subset
    · positivity
  have roots (candidate : active) :
      (Finset.univ.filter fun lambda : F => (errors candidate).eval lambda = 0).card ≤ degree := by
    have rootCount : (Finset.univ.filter fun lambda : F =>
        (errors candidate).eval lambda = 0).card ≤ (errors candidate).natDegree := by
      apply Polynomial.card_le_degree_of_subset_roots
      intro lambda member
      exact (Polynomial.mem_roots (nonzero candidate)).mpr (Finset.mem_filter.mp member).2
    exact rootCount.trans (small candidate)
  have rootBound (candidate : active) :
      Soundness.uniformProb (Finset.univ.filter fun lambda : F =>
        (errors candidate).eval lambda = 0) ≤ (degree : ℚ) / Fintype.card F := by
    unfold Soundness.uniformProb
    exact div_le_div_of_nonneg_right (by exact_mod_cast roots candidate) (by positivity)
  have listBound : Soundness.uniformProb (Finset.univ.biUnion (fun candidate : active =>
      Finset.univ.filter fun lambda : F => (errors candidate).eval lambda = 0)) ≤
      (Fintype.card active : ℚ) * ((degree : ℚ) / Fintype.card F) := by
    calc
      _ ≤ ∑ candidate : active, Soundness.uniformProb
          (Finset.univ.filter fun lambda : F => (errors candidate).eval lambda = 0) :=
        Soundness.union_bound _
      _ ≤ ∑ _candidate : active, (degree : ℚ) / Fintype.card F :=
        Finset.sum_le_sum (fun candidate _ => rootBound candidate)
      _ = _ := by simp
  have bound := first.trans listBound
  rw [Fintype.card_coe] at bound
  have countBound : (active.card : ℚ) ≤ candidates.card := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  have positive : (0 : ℚ) ≤ (degree : ℚ) / Fintype.card F := by positivity
  simpa only [Fintype.card_coe] using
    bound.trans (mul_le_mul_of_nonneg_right countBound positive)

/-- Exact lambda loss for each permitted fixed query tape. Candidate count and the actual batch width are charged; no 128-bit claim is inferred. -/
theorem collision_probability (n rate count i : Nat) (root : Oracle)
    (cs : LevelChallenges) (p : LevelProof) (state : VerifierState E)
    (candidates : Finset (Array E)) (tape : QueryTape (n + rate) count) :
    Soundness.uniformProb (Finset.univ.filter
      (Collision n rate count i root cs p state candidates tape)) ≤
        (candidates.card : ℚ) * ((p.oods.size + count : Nat) / (2 ^ 192 : ℚ)) := by
  have bound := @nonzero_collision_bound E (Array E) FieldModel.instCommRingE
    inferInstance inferInstance inferInstance inferInstance candidates
    (polynomial n rate count i root cs p state tape) (p.oods.size + count) (by
      intro candidate member
      simpa [polynomial] using errorPolynomial_degree candidate n i cs
        {p with rows := (queries (n + rate) count tape).map (fun q => root[q]!)}
        (queries (n + rate) count tape) state)
    (Collision n rate count i root cs p state candidates tape) inferInstance
    (by
      intro lambda member
      exact member)
  have card : (Fintype.card E : ℚ) = (2 ^ 192 : ℚ) := by
    rw [FieldModel.card_E, Nat.cast_pow, Nat.cast_ofNat]
  exact bound.trans_eq (by rw [card])

#print axioms collision_probability

#print axioms target_unique
#print axioms zero_error_hits
#print axioms restores_zero_candidate
#print axioms restores_fixed_target
end Whir.RewindBatchTarget
