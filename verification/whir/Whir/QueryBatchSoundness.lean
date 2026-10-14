import Whir.LevelBoundary
import Whir.BatchingRefinement
import Whir.RingMapBatching

/-! A query vector and its adjacent batching scalar form one challenge message.
Authentication, not restrictions on the prover's adaptive response, fixes rows. -/
namespace Whir.QueryBatchSoundness
open Concrete Protocol LevelBoundary BatchingRefinement
open scoped BigOperators

set_option maxRecDepth 2048
set_option maxHeartbeats 800000
open Classical

/-- Immutable scalar oracle after the preceding fold challenges. -/
def oldWord (n rate : Nat) (root : Oracle) (base : Bool) (folds : Array E)
    (q : Fin (2 ^ (n + rate))) : E :=
  dot (if base then root[q.val]!.reverse else root[q.val]!) (eqTable folds)

/-- The actual sampler's output, retaining repeated indices and their order. -/
def queries (depth count : Nat) (tape : QueryTape depth count) : Array Nat :=
  tab count fun j => SamplingProbability.concretePlace count depth j
    (Layout.rawQuery depth (fun k => (Array.ofFn tape)[k]!.toNat) j)

@[simp] theorem queries_size (depth count : Nat) (tape : QueryTape depth count) :
    (queries depth count tape).size = count := ArrayLayout.size_tab _ _

theorem queries_actual (depth count : Nat) (tape : QueryTape depth count)
    (hd : 0 < depth) (hb : depth ≤ 64) :
    deriveQueries depth count (Array.ofFn tape) = some (queries depth count tape) :=
  SamplingProbability.deriveQueries_eq depth count hd hb tape

theorem queries_bound (depth count : Nat) (tape : QueryTape depth count)
    (j : Nat) (hj : j < count) : (queries depth count tape)[j]! < 2 ^ depth := by
  rw [queries, ArrayLayout.getElem!_tab _ _ _ hj,
    SamplingProbability.concretePlace_eq count depth ⟨j, hj⟩]
  exact Layout.placeQuery_bound _ _

noncomputable def polynomial (n rate count i : Nat) (root : Oracle)
    (cs : LevelChallenges) (p : LevelProof) (s : VerifierState E)
    (tape : QueryTape (n + rate) count) (f : Array E) : Polynomial E :=
  errorPolynomial f n i cs
    {p with rows := (queries (n + rate) count tape).map (fun q => root[q]!)}
    (queries (n + rate) count tape) s

/-- Acceptance guards remain inside the event: malformed responses are rejected,
not ruled out globally. Both response functions see the whole query tape and lambda. -/
def Restores (n rate count i : Nat) (root : Oracle) (cs : LevelChallenges)
    (p : LevelProof) (s : VerifierState E) (candidates : Finset (Array E))
    (rowsAt : QueryTape (n + rate) count → E → Oracle)
    (introAt : QueryTape (n + rate) count → E → Message E)
    (draw : QueryTape (n + rate) count × E) : Prop :=
  let qs := queries (n + rate) count draw.1
  let proof := {p with rows := rowsAt draw.1 draw.2, intro := introAt draw.1 draw.2}
  let challenges := {cs with querySqueezes := Array.ofFn draw.1, lambda := draw.2}
  proof.rows.size = qs.size ∧
  runChecked (authenticateRow root qs proof) qs.size 0 () = .ok () ∧
  ¬ VerifierInvariant.Lost candidates
    (queryBatch n i challenges proof qs (oodBatch challenges proof s))

private theorem zero_hits (n rate count i : Nat) (root : Oracle)
    (cs : LevelChallenges) (p : LevelProof) (s : VerifierState E)
    (tape : QueryTape (n + rate) count) (f : Array E)
    (hd : 0 < n + rate) (hb : n + rate ≤ 64)
    (hz : polynomial n rate count i root cs p s tape f = 0) :
    dot f s.weight = s.claim ∧
    (∀ j < p.oods.size, Concrete.mle f cs.oodPoints[j]! = p.oods[j]!.value) ∧
    SamplingProbability.allQueriesHit (n + rate) count
      (agreeingColumns n rate f (oldWord n rate root (i == 0) cs.folds)) tape := by
  have hc := congrArg (fun x : Polynomial E => x.coeff 0) hz
  have residual : dot f s.weight = s.claim := by
    simpa [polynomial, errorPolynomial, batchPolynomial_coeff_zero, discrepancy,
      sub_eq_zero] using hc
  refine ⟨residual, ?_, queries (n + rate) count tape,
    queries_actual _ _ _ hd hb, ?_⟩
  · intro j hj
    have hc := congrArg (fun x : Polynomial E => x.coeff (j+1)) hz
    simpa only [polynomial, errorPolynomial, batchPolynomial_coeff_ood _ _ _ _ _ _ hj,
      Polynomial.coeff_zero, oodError, Concrete.mle, sub_eq_zero] using hc
  · intro j
    have hc := congrArg (fun x : Polynomial E => x.coeff (p.oods.size+1+j.val)) hz
    have hj : j.val < (queries (n + rate) count tape).size := by
      rw [queries_size]
      exact j.isLt
    have he : queryError f n cs
        {p with rows := (queries (n + rate) count tape).map (fun q => root[q]!)}
        (queries (n + rate) count tape) (i == 0) j.val = 0 := by
      simpa only [polynomial, errorPolynomial,
        batchPolynomial_coeff_query _ _ _ _ _ _ hj, Polynomial.coeff_zero] using hc
    classical
    apply Finset.mem_image.mpr
    refine ⟨⟨_, queries_bound _ _ _ _ j.isLt⟩, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change (encode n rate f)[(queries (n + rate) count tape)[j.val]!]! = _
    rw [encode, ArrayLayout.getElem!_tab _ _ _ (queries_bound _ _ _ _ j.isLt)]
    simpa [queryError, oldWord, getElem!_pos, hj, sub_eq_zero] using he

private theorem roots_cover_probability {F I : Type*} [Field F] [Fintype F]
    [DecidableEq F] [Fintype I] (P : F → Prop) (errors : I → Polynomial F) (d : Nat)
    (nonzero : ∀ f, errors f ≠ 0) (degree : ∀ f, (errors f).natDegree ≤ d)
    (cover : ∀ r, P r → ∃ f, (errors f).eval r = 0) :
    Soundness.uniformProb (Finset.univ.filter P) ≤
      (Fintype.card I : ℚ) * ((d : ℚ) / Fintype.card F) := by
  classical
  have subset : (Finset.univ.filter P) ⊆
      Finset.univ.biUnion (fun f => Finset.univ.filter fun r => (errors f).eval r = 0) := by
    intro r hr
    obtain ⟨f, hf⟩ := cover r (Finset.mem_filter.mp hr).2
    exact Finset.mem_biUnion.mpr
      ⟨f, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩⟩
  exact (div_le_div_of_nonneg_right
    (by exact_mod_cast Finset.card_le_card subset) (by positivity)).trans
      (Soundness.list_root_error errors d nonzero degree)

private theorem fiber_bound (n rate count i : Nat) (root : Oracle)
    (cs : LevelChallenges) (p : LevelProof) (s : VerifierState E)
    (candidates : Finset (Array E))
    (rowsAt : QueryTape (n + rate) count → E → Oracle)
    (introAt : QueryTape (n + rate) count → E → Message E)
    (sizes : ∀ f ∈ candidates, f.size = 2 ^ n)
    (weight : s.weight.size = 2 ^ n)
    (oods : ∀ j < p.oods.size, (eqTable cs.oodPoints[j]!).size = 2 ^ n)
    (tape : QueryTape (n + rate) count)
    (nonzero : ∀ f ∈ candidates, polynomial n rate count i root cs p s tape f ≠ 0) :
    Soundness.uniformProb (Finset.univ.filter fun r : E =>
      Restores n rate count i root cs p s candidates rowsAt introAt (tape, r)) ≤
        (candidates.card : ℚ) * ((p.oods.size + count : Nat) / (2 ^ 192 : ℚ)) := by
  classical
  have cover (r : E)
      (hr : Restores n rate count i root cs p s candidates rowsAt introAt (tape, r)) :
      ∃ f : candidates, (polynomial n rate count i root cs p s tape f.val).eval r = 0 := by
    obtain ⟨rows, auth, lost⟩ := hr
    simp only [VerifierInvariant.Lost, not_forall, not_not] at lost
    obtain ⟨f, hf, truth⟩ := lost
    refine ⟨⟨f, hf⟩, ?_⟩
    have identity := authenticated_batch_vary_lambda f n i cs p
      (queries (n + rate) count tape) root s (rowsAt tape) (introAt tape)
      (sizes f hf) (weight.trans (sizes f hf).symm)
      (by intro j hj; exact (oods j hj).trans (sizes f hf).symm) r rows
      ((OperationalRefinement.authentication_ok_iff _ _ _).mp auth)
    change (errorPolynomial f n i cs
      {p with rows := (queries (n + rate) count tape).map (fun q => root[q]!)}
      (queries (n + rate) count tape) s).eval r = 0
    rw [← identity]
    exact sub_eq_zero.mpr truth
  have bound := roots_cover_probability
    (fun r => Restores n rate count i root cs p s candidates rowsAt introAt (tape, r))
    (fun f : candidates => polynomial n rate count i root cs p s tape f.val)
    (p.oods.size + count) (fun f => nonzero f.val f.property)
    (by
      intro f
      simpa [polynomial] using errorPolynomial_degree f.val n i cs
        {p with rows := (queries (n + rate) count tape).map (fun q => root[q]!)}
        (queries (n + rate) count tape) s) cover
  simpa only [Fintype.card_coe, FieldModel.card_E, Nat.cast_pow, Nat.cast_ofNat] using bound

/-- Actual grouped Lost transition at a separated earlier OOD point. No sampler,
root-count, or batching-correctness assertion is supplied as a premise. -/
theorem grouped_transition (n rate count i threshold : Nat) (root : Oracle)
    (cs : LevelChallenges) (p : LevelProof) (s : VerifierState E)
    (candidates : Finset (Array E))
    (rowsAt : QueryTape (n + rate) count → E → Oracle)
    (introAt : QueryTape (n + rate) count → E → Message E)
    (alpha : ℚ) (ha : 0 ≤ alpha)
    (ht : threshold = ⌈(2 ^ (n + rate) : ℚ) * alpha⌉₊)
    (hd : 0 < n + rate) (hb : n + rate ≤ 64)
    (sizes : ∀ f ∈ candidates, f.size = 2 ^ n)
    (weight : s.weight.size = 2 ^ n)
    (oods : ∀ j < p.oods.size, (eqTable cs.oodPoints[j]!).size = 2 ^ n)
    (lost : CloseLost n rate threshold (oldWord n rate root (i == 0) cs.folds) s)
    (j : Nat) (hj : j < p.oods.size)
    (separated : Separated candidates cs.oodPoints[j]!) :
    Soundness.uniformProb (Finset.univ.filter
      (Restores n rate count i root cs p s candidates rowsAt introAt)) ≤
      alpha ^ count + (candidates.card : ℚ) *
        ((p.oods.size + count : Nat) / (2 ^ 192 : ℚ)) := by
  classical
  let escape := queryEscape n rate count (oldWord n rate root (i == 0) cs.folds)
    s candidates cs.oodPoints[j]! p.oods[j]!.value
  apply RingMapBatching.conditional_error (fun tape => tape ∈ escape) _ _ _ (by positivity)
  · simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter] using
      query_escape_probability n rate count threshold _ s candidates _ _ alpha ha ht hd hb
        sizes lost separated
  · intro tape outside
    apply fiber_bound n rate count i root cs p s candidates rowsAt introAt sizes weight oods tape
    intro f hf hz
    obtain ⟨residual, ood, hits⟩ := zero_hits n rate count i root cs p s tape f hd hb hz
    apply outside
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, f, hf, ood j hj, residual, hits⟩

/-- Final-level query escape for the already fixed residual. There is no OOD
message or auxiliary separation point in this event. -/
theorem final_transition (n rate count i threshold : Nat) (root : Oracle)
    (cs : LevelChallenges) (p : LevelProof) (s : VerifierState E) (f : Array E)
    (rowsAt : QueryTape (n + rate) count → E → Oracle)
    (introAt : QueryTape (n + rate) count → E → Message E)
    (alpha : ℚ) (ha : 0 ≤ alpha)
    (ht : threshold = ⌈(2 ^ (n + rate) : ℚ) * alpha⌉₊)
    (hd : 0 < n + rate) (hb : n + rate ≤ 64)
    (shape : f.size = 2 ^ n) (weight : s.weight.size = 2 ^ n)
    (zeroOOD : p.oods.size = 0)
    (lost : CloseLost n rate threshold (oldWord n rate root (i == 0) cs.folds) s) :
    Soundness.uniformProb (Finset.univ.filter
      (Restores n rate count i root cs p s {f} rowsAt introAt)) ≤
      alpha ^ count + (count : ℚ) / 2 ^ 192 := by
  classical
  let agree := agreeingColumns n rate f (oldWord n rate root (i == 0) cs.folds)
  let escape : QueryTape (n + rate) count → Prop := fun tape =>
    dot f s.weight = s.claim ∧ SamplingProbability.allQueriesHit (n + rate) count agree tape
  have escape_bound : Soundness.uniformProb (Finset.univ.filter escape) ≤ alpha ^ count := by
    by_cases truth : dot f s.weight = s.claim
    · have small : agree.card < threshold := by
        apply Nat.lt_of_not_ge
        intro close
        exact lost f shape close truth
      have density : (agree.card : ℚ) / (2 ^ (n + rate) : ℚ) ≤ alpha := by
        apply (div_le_iff₀ (by positivity : (0 : ℚ) < 2 ^ (n + rate))).mpr
        rw [ht] at small
        have h := Nat.lt_ceil.mp small
        nlinarith
      have bound := SamplingProbability.actual_query_bound_rat (n + rate) count hd hb agree
      simp only [Nat.cast_pow, Nat.cast_ofNat] at bound
      simpa only [escape, truth, true_and] using
        bound.trans (pow_le_pow_left₀ (by positivity) density count)
    · simp only [escape, truth, false_and, Finset.filter_false, Soundness.uniformProb,
        Finset.card_empty, Nat.cast_zero, zero_div]
      exact pow_nonneg ha count
  apply RingMapBatching.conditional_error escape _ _ _ (by positivity) escape_bound
  intro tape outside
  have bound := fiber_bound n rate count i root cs p s {f} rowsAt introAt
    (by simpa using shape) weight (by simp [zeroOOD]) tape (by
      intro g hg hz
      have hgf : g = f := Finset.mem_singleton.mp hg
      subst g
      obtain ⟨residual, _, hits⟩ := zero_hits n rate count i root cs p s tape f hd hb hz
      exact outside ⟨residual, hits⟩)
  simpa [zeroOOD] using bound

end Whir.QueryBatchSoundness
