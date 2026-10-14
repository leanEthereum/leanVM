import Whir.OperationalRefinement
import Whir.QueryRefinement
import Whir.Soundness
import Whir.FieldEquality

/-! The actual adjacent OOD/query batch uses one lambda. Its discrepancy is a
polynomial with disjoint coefficient positions; transmitted intros do not enter
claim/weight equality. Concrete identities use the checked ring bridge only.
Root counting is stated generically for a field, separately from these identities. -/
namespace Whir.BatchingRefinement
open Concrete Protocol ArrayAlgebra ArrayLayout QueryRefinement
open scoped BigOperators

/-- The discrepancy used by batching, without any pending-message assumption. -/
def discrepancy {R : Type*} [CommRing R] [Inhabited R]
    (f : Array R) (s : VerifierState R) : R := dot f s.weight - s.claim

theorem discrepancy_batch {R : Type*} [CommRing R] [Inhabited R]
    (f basis : Array R) (s : VerifierState R) (value scale : R) (intro : Message R)
    (hs : s.weight.size = f.size) (hb : basis.size = f.size) :
    discrepancy f (s.batch basis value scale intro) =
      discrepancy f s + scale * (dot f basis - value) := by
  unfold discrepancy
  simp only [VerifierState.batch]
  rw [dot_weightGlue f s.weight basis scale hs hb]
  ring

private theorem runSteps_add {S : Type*} (step : Nat → S → S)
    (a b start : Nat) (s : S) :
    runSteps step (a+b) start s = runSteps step b (start+a) (runSteps step a start s) := by
  induction a generalizing start s with
  | zero => simp [runSteps]
  | succ a ih =>
    simpa [runSteps, Nat.succ_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ih (start+1) (step start s)

theorem runSteps_succ_last {S : Type*} (step : Nat → S → S) (count : Nat) (s : S) :
    runSteps step (count+1) 0 s = step count (runSteps step count 0 s) := by
  rw [runSteps_add]
  simp [runSteps]

private theorem power_loop (a : E) (count : Nat) :
    (List.range count).foldl (fun s (_ : Nat) => (s.1.push s.2, s.2 * a))
      ((#[] : Array E), (1 : E)) =
      (tab count (fun j => a^j), a^count) := by
  induction count with
  | zero => simp [tab]
  | succ count ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, pow_succ]
    congr 1
    apply Array.toList_inj.mp
    simp [tab, List.range_succ]

theorem powers_eq_tab (a : E) (count : Nat) :
    powers a count = tab count (fun j => a^j) := by
  unfold powers
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range',
    List.forIn_pure_yield_eq_foldl, pure_bind]
  change ((List.range count).foldl
    (fun s (_ : Nat) => (s.1.push s.2, s.2 * a)) ((#[] : Array E), (1 : E))).1 = _
  rw [power_loop]

@[simp] theorem size_powers (a : E) (count : Nat) : (powers a count).size = count := by
  simp [powers_eq_tab]

theorem get_powers (a : E) (count j : Nat) (hj : j < count) :
    (powers a count)[j]! = a^j := by
  rw [powers_eq_tab, getElem!_tab _ _ _ hj]

def oodError (f : Array E) (cs : LevelChallenges) (p : LevelProof) (j : Nat) : E :=
  dot f (eqTable cs.oodPoints[j]!) - p.oods[j]!.value

def queryError (f : Array E) (n : Nat) (cs : LevelChallenges) (p : LevelProof)
    (qs : Array Nat) (base : Bool) (j : Nat) : E :=
  dot f (column n qs[j]!) -
    dot (if base then p.rows[j]!.reverse else p.rows[j]!) (eqTable cs.folds)

/-- Prefix induction for the actual OOD kernel, including its running scalar.
No truth assumption is made about an OOD value or its transmitted intro. -/
theorem ood_prefix (f : Array E) (cs : LevelChallenges) (p : LevelProof)
    (s : VerifierState E) (count : Nat) (hs : s.weight.size = f.size)
    (shape : ∀ j < count, (eqTable cs.oodPoints[j]!).size = f.size) :
    let out := runSteps (oodStep cs p) count 0 (s, E.one)
    out.1.weight.size = f.size ∧ out.2 = cs.lambda^count ∧
      discrepancy f out.1 = discrepancy f s +
        ∑ j ∈ Finset.range count, cs.lambda^(j+1) * oodError f cs p j := by
  induction count with
  | zero => simpa [runSteps, ← FieldModel.E_one_def] using hs
  | succ count ih =>
    obtain ⟨hw, scalar, err⟩ := ih (by intro j hj; exact shape j (by omega))
    dsimp only
    rw [runSteps_succ_last]
    simp only [oodStep]
    refine ⟨?_, ?_, ?_⟩
    · simpa only [VerifierState.batch, size_weightGlue] using hw
    · rw [scalar, pow_succ]
    · rw [discrepancy_batch _ _ _ _ _ _ hw (shape count (by omega))]
      rw [scalar, err, Finset.sum_range_succ]
      simp only [oodError, pow_succ]
      ring

/-- The authenticated-query discrepancy expands per row using the actual dense
column and enforced kernels; honesty of those rows is not assumed. -/
theorem query_error_sum (f : Array E) (n : Nat) (cs : LevelChallenges)
    (p : LevelProof) (qs : Array Nat) (base : Bool)
    (shape : f.size = 2^n) (rows : p.rows.size = qs.size) :
    dot f (induced n qs (powers cs.lambda qs.size)) -
        enforced p.rows cs.folds (powers cs.lambda qs.size) base =
      ∑ j ∈ Finset.range qs.size, cs.lambda^j * queryError f n cs p qs base j := by
  have hd := dot_inducedColumns f (qs.map (column n)) (powers cs.lambda qs.size)
    (by
      intro j hj
      have hj' : j < qs.size := by simpa using hj
      simp [getElem!_pos, hj', shape])
  rw [shape] at hd
  rw [induced, hd, enforced, tab_sum, rows]
  simp only [Array.size_map]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [get_powers _ _ _ hj']
  simp only [queryError]
  have hm : (qs.map (column n))[j]! = column n qs[j]! := by
    simp [getElem!_pos, hj']
  rw [hm]
  ring

/-- Exact final discrepancy after both adjacent batches, with a single lambda.
In particular a lambda-dependent `p.intro` changes neither side. -/
theorem batch_discrepancy (f : Array E) (n i : Nat) (cs : LevelChallenges)
    (p : LevelProof) (qs : Array Nat) (s : VerifierState E)
    (shape : f.size = 2^n) (hs : s.weight.size = f.size)
    (oods : ∀ j < p.oods.size, (eqTable cs.oodPoints[j]!).size = f.size)
    (rows : p.rows.size = qs.size) :
    discrepancy f (queryBatch n i cs p qs (oodBatch cs p s)) =
      discrepancy f s +
        (∑ j ∈ Finset.range p.oods.size, cs.lambda^(j+1) * oodError f cs p j) +
        ∑ j ∈ Finset.range qs.size,
          cs.lambda^(p.oods.size+1+j) * queryError f n cs p qs (i == 0) j := by
  obtain ⟨hw, scalar, err⟩ := ood_prefix f cs p s p.oods.size hs oods
  change (oodBatch cs p s).1.weight.size = f.size at hw
  change (oodBatch cs p s).2 = cs.lambda^p.oods.size at scalar
  change discrepancy f (oodBatch cs p s).1 = _ at err
  unfold queryBatch
  rw [discrepancy_batch _ _ _ _ _ _ hw (by simp [shape])]
  rw [query_error_sum f n cs p qs (i == 0) shape rows, err, scalar]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add, pow_succ]
  ring

open Polynomial

section Polynomial
variable {R : Type*} [CommRing R]

private noncomputable def coefficientBlock (start count : Nat) (a : Nat → R) : R[X] :=
  ∑ j ∈ Finset.range count, monomial (start+j) (a j)

private theorem coefficientBlock_at (start count j : Nat) (a : Nat → R) (hj : j < count) :
    (coefficientBlock start count a).coeff (start+j) = a j := by
  simp only [coefficientBlock, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hne
    simp [hne]
  · simp [hj]

private theorem coefficientBlock_outside (start count i : Nat) (a : Nat → R)
    (outside : i < start ∨ start+count ≤ i) :
    (coefficientBlock start count a).coeff i = 0 := by
  simp only [coefficientBlock, finsetSum_coeff, coeff_monomial]
  apply Finset.sum_eq_zero
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have hne : start+j ≠ i := by omega
  simp [hne]

private theorem coefficientBlock_degree (start count d : Nat) (a : Nat → R)
    (bound : ∀ j < count, start+j ≤ d) :
    (coefficientBlock start count a).natDegree ≤ d := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_monomial_le _).trans (bound j (Finset.mem_range.mp hj))

/-- Distinct monomial slots for the residual, each OOD, and each query error. -/
noncomputable def batchPolynomial (m k : Nat) (residual : R) (ood query : Nat → R) : R[X] :=
  C residual + coefficientBlock 1 m ood + coefficientBlock (m+1) k query

theorem batchPolynomial_eval (m k : Nat) (residual : R) (ood query : Nat → R) (r : R) :
    (batchPolynomial m k residual ood query).eval r =
      residual + (∑ j ∈ Finset.range m, r^(j+1) * ood j) +
        ∑ j ∈ Finset.range k, r^(m+1+j) * query j := by
  simp [batchPolynomial, coefficientBlock, eval_finsetSum, Nat.add_comm, mul_comm]

theorem batchPolynomial_coeff_zero (m k : Nat) (residual : R) (ood query : Nat → R) :
    (batchPolynomial m k residual ood query).coeff 0 = residual := by
  simp only [batchPolynomial, coeff_add, coeff_C_zero]
  rw [coefficientBlock_outside _ _ _ _ (Or.inl (by omega)),
    coefficientBlock_outside _ _ _ _ (Or.inl (by omega))]
  simp

theorem batchPolynomial_coeff_ood (m k j : Nat) (residual : R) (ood query : Nat → R)
    (hj : j < m) :
    (batchPolynomial m k residual ood query).coeff (j+1) = ood j := by
  simp only [batchPolynomial, coeff_add]
  rw [show j+1 = 1+j by omega, coefficientBlock_at _ _ _ _ hj,
    coefficientBlock_outside _ _ _ _ (Or.inl (by omega))]
  simp [coeff_C]

theorem batchPolynomial_coeff_query (m k j : Nat) (residual : R) (ood query : Nat → R)
    (hj : j < k) :
    (batchPolynomial m k residual ood query).coeff (m+1+j) = query j := by
  simp only [batchPolynomial, coeff_add]
  rw [coefficientBlock_at _ _ _ _ hj,
    coefficientBlock_outside _ _ _ _ (Or.inr (by omega))]
  simp [coeff_C]

theorem batchPolynomial_degree (m k : Nat) (residual : R) (ood query : Nat → R) :
    (batchPolynomial m k residual ood query).natDegree ≤ m+k := by
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply (natDegree_add_le _ _).trans
    apply max_le
    · simp
    · exact coefficientBlock_degree 1 m (m+k) ood (by intro j hj; omega)
  · exact coefficientBlock_degree (m+1) k (m+k) query (by intro j hj; omega)

/-- Any false constituent prevents the shared-lambda error polynomial from being
identically zero, including when the incoming residual discrepancy is zero. -/
theorem batchPolynomial_ne_zero (m k : Nat) (residual : R) (ood query : Nat → R)
    (bad : residual ≠ 0 ∨ (∃ j < m, ood j ≠ 0) ∨ (∃ j < k, query j ≠ 0)) :
    batchPolynomial m k residual ood query ≠ 0 := by
  intro h
  rcases bad with hr | ⟨j, hj, he⟩ | ⟨j, hj, he⟩
  · apply hr
    have hc := batchPolynomial_coeff_zero m k residual ood query
    simpa [h] using hc.symm
  · apply he
    have hc := batchPolynomial_coeff_ood m k j residual ood query hj
    simpa [h] using hc.symm
  · apply he
    have hc := batchPolynomial_coeff_query m k j residual ood query hj
    simpa [h] using hc.symm
end Polynomial

/-- This polynomial is fixed by the pre-lambda state, OOD values, and sampled
rows. Its definition does not inspect lambda or any transmitted intro. -/
noncomputable def errorPolynomial (f : Array E) (n i : Nat) (cs : LevelChallenges)
    (p : LevelProof) (qs : Array Nat) (s : VerifierState E) : E[X] :=
  batchPolynomial p.oods.size qs.size (discrepancy f s)
    (oodError f cs p) (queryError f n cs p qs (i == 0))

theorem batch_discrepancy_eq_eval (f : Array E) (n i : Nat) (cs : LevelChallenges)
    (p : LevelProof) (qs : Array Nat) (s : VerifierState E)
    (shape : f.size = 2^n) (hs : s.weight.size = f.size)
    (oods : ∀ j < p.oods.size, (eqTable cs.oodPoints[j]!).size = f.size)
    (rows : p.rows.size = qs.size) :
    discrepancy f (queryBatch n i cs p qs (oodBatch cs p s)) =
      (errorPolynomial f n i cs p qs s).eval cs.lambda := by
  rw [errorPolynomial, batchPolynomial_eval]
  exact batch_discrepancy f n i cs p qs s shape hs oods rows

theorem errorPolynomial_degree (f : Array E) (n i : Nat) (cs : LevelChallenges)
    (p : LevelProof) (qs : Array Nat) (s : VerifierState E) :
    (errorPolynomial f n i cs p qs s).natDegree ≤ p.oods.size+qs.size :=
  batchPolynomial_degree _ _ _ _ _

theorem errorPolynomial_ne_zero (f : Array E) (n i : Nat) (cs : LevelChallenges)
    (p : LevelProof) (qs : Array Nat) (s : VerifierState E)
    (bad : discrepancy f s ≠ 0 ∨
      (∃ j < p.oods.size, oodError f cs p j ≠ 0) ∨
      (∃ j < qs.size, queryError f n cs p qs (i == 0) j ≠ 0)) :
    errorPolynomial f n i cs p qs s ≠ 0 :=
  batchPolynomial_ne_zero _ _ _ _ _ bad

/-- The polynomial is chosen before lambda, even when the query intro is chosen
after seeing that same lambda. This is definitional, not an independence axiom. -/
theorem errorPolynomial_lambda_intro (f : Array E) (n i : Nat) (cs : LevelChallenges)
    (p : LevelProof) (qs : Array Nat) (s : VerifierState E) (r : E) (intro : Message E) :
    errorPolynomial f n i {cs with lambda := r} {p with intro := intro} qs s =
      errorPolynomial f n i cs p qs s := rfl

/-- Uniform-in-lambda operational identity for any adaptive query-intro function.
The rows and OOD values, not the pending intro, determine all coefficients. -/
theorem batch_discrepancy_vary_lambda (f : Array E) (n i : Nat) (cs : LevelChallenges)
    (p : LevelProof) (qs : Array Nat) (s : VerifierState E) (intro : E → Message E)
    (shape : f.size = 2^n) (hs : s.weight.size = f.size)
    (oods : ∀ j < p.oods.size, (eqTable cs.oodPoints[j]!).size = f.size)
    (rows : p.rows.size = qs.size) (r : E) :
    discrepancy f (queryBatch n i {cs with lambda := r} {p with intro := intro r} qs
      (oodBatch {cs with lambda := r} {p with intro := intro r} s)) =
        (errorPolynomial f n i cs p qs s).eval r := by
  exact batch_discrepancy_eq_eval f n i {cs with lambda := r}
    {p with intro := intro r} qs s shape hs oods rows

/-- Authentication fixes even adversarially supplied rows to immutable oracle
lookups. Therefore the query-error coefficients cannot depend on lambda through
the prover's row messages. Duplicated query indices are retained. -/
theorem authenticated_rows_eq (oracle : Oracle) (qs : Array Nat) (p : LevelProof)
    (rows : p.rows.size = qs.size)
    (auth : ∀ j, j < qs.size → (p.rows[j]! != oracle[qs[j]!]!) = false) :
    p.rows = qs.map (fun q => oracle[q]!) := by
  apply Array.ext
  · simpa using rows
  · intro j hj hk
    have hq : j < qs.size := by simpa using hk
    have he : p.rows[j]! = oracle[qs[j]!]! := by simpa using auth j hq
    simpa [getElem!_pos, hj, hq] using he

/-- The exact actual authentication loop supplies canonical rows. -/
theorem checked_rows_eq (oracle : Oracle) (qs : Array Nat) (p : LevelProof)
    (rows : p.rows.size = qs.size)
    (checked : runChecked (authenticateRow oracle qs p) qs.size 0 () = .ok ()) :
    p.rows = qs.map (fun q => oracle[q]!) :=
  authenticated_rows_eq oracle qs p rows
    ((OperationalRefinement.authentication_ok_iff oracle qs p).mp checked)

/-- Even lambda-dependent rows and query intros cannot alter the fixed polynomial
on authenticated executions. The only row premise is the actual Boolean lookup
check, not an algebraic batching-correctness assertion. -/
theorem authenticated_batch_vary_lambda (f : Array E) (n i : Nat)
    (cs : LevelChallenges) (p : LevelProof) (qs : Array Nat) (oracle : Oracle)
    (s : VerifierState E) (rowsAt : E → Oracle) (intro : E → Message E)
    (shape : f.size = 2^n) (hs : s.weight.size = f.size)
    (oods : ∀ j < p.oods.size, (eqTable cs.oodPoints[j]!).size = f.size)
    (r : E) (rows : (rowsAt r).size = qs.size)
    (auth : ∀ j, j < qs.size → ((rowsAt r)[j]! != oracle[qs[j]!]!) = false) :
    discrepancy f
      (queryBatch n i {cs with lambda := r} {p with rows := rowsAt r, intro := intro r} qs
        (oodBatch {cs with lambda := r} {p with rows := rowsAt r, intro := intro r} s)) =
      (errorPolynomial f n i cs {p with rows := qs.map (fun q => oracle[q]!)} qs s).eval r := by
  have hr : rowsAt r = qs.map (fun q => oracle[q]!) :=
    authenticated_rows_eq oracle qs {p with rows := rowsAt r} rows auth
  rw [hr]
  exact batch_discrepancy_vary_lambda f n i cs
    {p with rows := qs.map (fun q => oracle[q]!)} qs s intro shape hs oods (by simp) r

/-- Field-generic bridge: concrete operational equality above requires only the
proved ring laws. Root counting additionally requires an actual field instance. -/
theorem batchPolynomial_root_error {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (m k : Nat) (residual : F) (ood query : Nat → F)
    (bad : residual ≠ 0 ∨ (∃ j < m, ood j ≠ 0) ∨ (∃ j < k, query j ≠ 0)) :
    Soundness.uniformProb (Finset.univ.filter fun r =>
      (batchPolynomial m k residual ood query).eval r = 0) ≤
        ((m+k : Nat) : ℚ) / Fintype.card F :=
  Soundness.root_error _ (batchPolynomial_ne_zero m k residual ood query bad)
    (m+k) (batchPolynomial_degree m k residual ood query)

end Whir.BatchingRefinement
