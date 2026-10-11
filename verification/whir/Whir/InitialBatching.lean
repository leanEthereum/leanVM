import Whir.CausalGame
import Whir.ArrayAlgebra
import Whir.FieldEquivalence

/-! Initial batching of the actual public claims. The imperative accumulator is
refined to a single polynomial whose coefficient at `j` is the executable
dot-product error of claim `j`. Width and literal zero padding are preserved.

`escape_probability` counts actual false-claim cancellation over all `2^192`
extension elements, including zero. `candidate_escape_probability` takes the
commitment-fixed family before the public claims; no adaptive post-lambda choice
of coefficients is permitted. `lost_preserved` and `lost_escape_probability`
connect this event to the actual initial lost invariant. Empty claim arrays
have no false constituent and hence zero escape probability. -/
namespace Whir.InitialBatching
open Concrete Protocol CausalGame ArrayAlgebra ArrayLayout Polynomial
open scoped BigOperators

private def step (lambda : E) (s : Claim × E) (claim : Claim) : Claim × E :=
  (⟨weightGlue s.1.weight claim.weight s.2, s.1.value + s.2 * claim.value⟩,
    s.2 * lambda)

private def initial (width : Nat) : Claim × E :=
  (⟨tab width fun _ => 0, 0⟩, 1)

private theorem batchClaims_fold (width : Nat) (claims : Array Claim) (lambda : E) :
    batchClaims width claims lambda = (claims.foldl (step lambda) (initial width)).1 := by
  unfold batchClaims
  simp only [Array.forIn_pure_yield_eq_foldl, pure_bind]
  rfl

private theorem array_push_induction {α : Type*} {P : Array α → Prop}
    (empty : P #[]) (push : ∀ a x, P a → P (a.push x)) (a : Array α) : P a := by
  rcases a with ⟨xs⟩
  induction xs using List.reverseRecOn with
  | nil => exact empty
  | @append_singleton xs x ih => simpa using push xs.toArray x ih

/-- The actual imperative accumulator retains its width, without shape assumptions. -/
private theorem loop_size (width : Nat) (claims : Array Claim) (lambda : E) :
    (claims.foldl (step lambda) (initial width)).1.weight.size = width := by
  induction claims using array_push_induction with
  | empty => simp [initial]
  | @push claims claim ih => simp [step, ih]

@[simp] theorem batchClaims_size (width : Nat) (claims : Array Claim) (lambda : E) :
    (batchClaims width claims lambda).weight.size = width := by
  rw [batchClaims_fold]
  exact loop_size width claims lambda

/-- Discrepancy of a constituent, using the executable dense dot product. -/
def claimError (f : Array E) (claim : Claim) : E := dot f claim.weight - claim.value

private theorem loop_discrepancy (f : Array E) (claims : Array Claim) (lambda : E)
    (shape : ∀ j : Fin claims.size, claims[j].weight.size = f.size) :
    let out := claims.foldl (step lambda) (initial f.size)
    out.2 = lambda ^ claims.size ∧
      claimError f out.1 = ∑ j ∈ Finset.range claims.size,
        lambda ^ j * claimError f claims[j]! := by
  induction claims using array_push_induction with
  | empty =>
    simp [initial, claimError, dot_eq_sum]
    apply Finset.sum_eq_zero
    intro j hj
    rw [getElem!_tab _ _ _ (Finset.mem_range.mp hj), mul_zero]
  | @push claims claim ih =>
    have oldShape : ∀ j : Fin claims.size, claims[j].weight.size = f.size := by
      intro j
      have h := shape ⟨j.val, by simp⟩
      change (claims.push claim)[j.val].weight.size = f.size at h
      rw [Array.getElem_push_lt j.isLt] at h
      exact h
    have newShape : claim.weight.size = f.size := by
      simpa using shape ⟨claims.size, by simp⟩
    obtain ⟨power, err⟩ := ih oldShape
    dsimp only
    rw [Array.foldl_push]
    simp only [Array.size_push]
    refine ⟨?_, ?_⟩
    · simp only [step, power, pow_succ]
    · change dot f (weightGlue
          (claims.foldl (step lambda) (initial f.size)).1.weight claim.weight
          (claims.foldl (step lambda) (initial f.size)).2) -
          ((claims.foldl (step lambda) (initial f.size)).1.value +
            (claims.foldl (step lambda) (initial f.size)).2 * claim.value) = _
      rw [dot_weightGlue _ _ _ _ (loop_size _ _ _) newShape]
      rw [power, Finset.sum_range_succ]
      have oldSum : (∑ j ∈ Finset.range claims.size,
          lambda ^ j * claimError f (claims.push claim)[j]!) =
          ∑ j ∈ Finset.range claims.size, lambda ^ j * claimError f claims[j]! := by
        apply Finset.sum_congr rfl
        intro j hj
        have h := Finset.mem_range.mp hj
        rw [getElem!_pos (claims.push claim) j (by simp; omega),
          getElem!_pos claims j h, Array.getElem_push_lt h]
      rw [oldSum]
      rw [getElem!_pos (claims.push claim) claims.size (by simp), Array.getElem_push_eq]
      dsimp [claimError] at err ⊢
      rw [← err]
      ring

/-- One polynomial, with no hidden lambda dependence in any coefficient. -/
noncomputable def errorPolynomial (f : Array E) (claims : Array Claim) : E[X] :=
  ∑ j ∈ Finset.range claims.size, monomial j (claimError f claims[j]!)

theorem errorPolynomial_eval (f : Array E) (claims : Array Claim) (lambda : E) :
    (errorPolynomial f claims).eval lambda =
      ∑ j ∈ Finset.range claims.size, lambda ^ j * claimError f claims[j]! := by
  simp [errorPolynomial, eval_finsetSum, mul_comm]

/-- Exact actual-loop discrepancy, including lambda zero and empty claim arrays. -/
theorem batchClaims_discrepancy (f : Array E) (claims : Array Claim) (lambda : E)
    (shape : ∀ j : Fin claims.size, claims[j].weight.size = f.size) :
    dot f (batchClaims f.size claims lambda).weight -
        (batchClaims f.size claims lambda).value =
      (errorPolynomial f claims).eval lambda := by
  rw [batchClaims_fold, errorPolynomial_eval]
  exact (loop_discrepancy f claims lambda shape).2

theorem errorPolynomial_coeff (f : Array E) (claims : Array Claim) (j : Nat)
    (hj : j < claims.size) :
    (errorPolynomial f claims).coeff j = claimError f claims[j]! := by
  simp only [errorPolynomial, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hne
    simp [hne]
  · simp [hj]

theorem errorPolynomial_degree (f : Array E) (claims : Array Claim) :
    (errorPolynomial f claims).natDegree ≤ claims.size - 1 := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_monomial_le _).trans (by have := Finset.mem_range.mp hj; omega)

theorem errorPolynomial_ne_zero (f : Array E) (claims : Array Claim)
    (bad : ∃ j : Fin claims.size, dot f claims[j].weight ≠ claims[j].value) :
    errorPolynomial f claims ≠ 0 := by
  obtain ⟨j, hj⟩ := bad
  intro h
  have hc := errorPolynomial_coeff f claims j j.isLt
  rw [h] at hc
  exact hj (sub_eq_zero.mp (by simpa [claimError, getElem!_pos] using hc.symm))

/-- Padding remains literal zero, even for malformed weight lengths. -/
theorem batchClaims_zero_tail (width live : Nat) (claims : Array Claim) (lambda : E)
    (tail : ∀ j : Fin claims.size, ∀ i, live ≤ i → i < width →
      claims[j].weight[i]! = 0) :
    ∀ i, live ≤ i → i < width → (batchClaims width claims lambda).weight[i]! = 0 := by
  rw [batchClaims_fold]
  induction claims using array_push_induction with
  | empty =>
    intro i _ hi
    simp [initial, getElem!_tab _ _ _ hi]
  | @push claims claim ih =>
    have oldTail : ∀ j : Fin claims.size, ∀ i, live ≤ i → i < width →
        claims[j].weight[i]! = 0 := by
      intro j i hl hi
      have h := tail ⟨j.val, by simp⟩ i hl hi
      change (claims.push claim)[j.val].weight[i]! = 0 at h
      rwa [Array.getElem_push_lt j.isLt] at h
    intro i hl hi
    have last : claim.weight[i]! = 0 := by
      simpa using tail ⟨claims.size, by simp⟩ i hl hi
    rw [Array.foldl_push]
    change (weightGlue _ claim.weight _)[i]! = 0
    rw [weightGlue, getElem!_tab _ _ _ (by rw [loop_size]; exact hi)]
    rw [ih oldTail i hl hi, last, mul_zero, add_zero]

/-- A false public claim is a property of the fixed pre-lambda statement. -/
def Violated (f : Array E) (claims : Array Claim) : Prop :=
  ∃ j : Fin claims.size, dot f claims[j].weight ≠ claims[j].value

/-- Exactly the initial false-claim escape event, not an arbitrary polynomial root event. -/
noncomputable def escape (f : Array E) (claims : Array Claim) : Finset E := by
  classical
  exact Finset.univ.filter fun lambda => Violated f claims ∧
    dot f (batchClaims f.size claims lambda).weight =
      (batchClaims f.size claims lambda).value

theorem escape_probability (f : Array E) (claims : Array Claim)
    (shape : ∀ j : Fin claims.size, claims[j].weight.size = f.size) :
    Soundness.uniformProb (escape f claims) ≤ ((claims.size - 1 : Nat) : ℚ) / 2^192 := by
  classical
  by_cases bad : Violated f claims
  · have event : escape f claims = Finset.univ.filter fun lambda =>
        (errorPolynomial f claims).eval lambda = 0 := by
      ext lambda
      simp only [escape, Finset.mem_filter, Finset.mem_univ, true_and, bad]
      rw [← batchClaims_discrepancy f claims lambda shape, sub_eq_zero]
    rw [event]
    simpa only [FieldModel.card_E, Nat.cast_pow, Nat.cast_ofNat] using
      Soundness.root_error (errorPolynomial f claims)
        (errorPolynomial_ne_zero f claims bad) (claims.size - 1)
        (errorPolynomial_degree f claims)
  · have event : escape f claims = ∅ := by simp [escape, bad]
    rw [event]
    simp [Soundness.uniformProb]
    positivity

/-- The candidate set is fixed before the public claims, hence before lambda.
Claims need not be true for every candidate, and the empty array has zero risk. -/
noncomputable def candidateEscape (candidates : Finset (Array E)) (claims : Array Claim) :
    Finset E := by
  classical
  exact candidates.biUnion fun f => escape f claims

theorem candidate_escape_probability (candidates : Finset (Array E))
    (claims : Array Claim)
    (shape : ∀ f ∈ candidates, ∀ j : Fin claims.size, claims[j].weight.size = f.size) :
    Soundness.uniformProb (candidateEscape candidates claims) ≤
      (candidates.card : ℚ) * (claims.size - 1 : Nat) / 2^192 := by
  classical
  have events : candidateEscape candidates claims =
      Finset.univ.biUnion (fun f : candidates => escape f.val claims) := by
    ext lambda
    simp [candidateEscape]
  rw [events]
  calc
    _ ≤ ∑ f : candidates, Soundness.uniformProb (escape f.val claims) :=
      Soundness.union_bound _
    _ ≤ ∑ _f : candidates, ((claims.size - 1 : Nat) : ℚ) / 2^192 :=
      Finset.sum_le_sum fun f _ => escape_probability f.val claims (shape f.val f.property)
    _ = _ := by simp [mul_div_assoc]

/-- Lost means that no commitment-fixed candidate satisfies every public claim. -/
def Lost (candidates : Finset (Array E)) (claims : Array Claim) : Prop :=
  ∀ f ∈ candidates, Violated f claims

def BatchedLost (width : Nat) (candidates : Finset (Array E))
    (claims : Array Claim) (lambda : E) : Prop :=
  ∀ f ∈ candidates, dot f (batchClaims width claims lambda).weight ≠
    (batchClaims width claims lambda).value

/-- Outside the counted escape event, the actual initial batching preserves lostness. -/
theorem lost_preserved (width : Nat) (candidates : Finset (Array E))
    (claims : Array Claim) (lambda : E)
    (sizes : ∀ f ∈ candidates, f.size = width)
    (lost : Lost candidates claims)
    (outside : lambda ∉ candidateEscape candidates claims) :
    BatchedLost width candidates claims lambda := by
  classical
  intro f hf eq
  apply outside
  apply Finset.mem_biUnion.mpr
  refine ⟨f, hf, ?_⟩
  simp only [escape, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨lost f hf, by simpa only [sizes f hf] using eq⟩

noncomputable def lostEscape (width : Nat) (candidates : Finset (Array E))
    (claims : Array Claim) : Finset E := by
  classical
  exact Finset.univ.filter fun lambda =>
    Lost candidates claims ∧ ¬ BatchedLost width candidates claims lambda

/-- Exact finite probability of losing the actual initial lost invariant. -/
theorem lost_escape_probability (width : Nat) (candidates : Finset (Array E))
    (claims : Array Claim)
    (sizes : ∀ f ∈ candidates, f.size = width)
    (shape : ∀ j : Fin claims.size, claims[j].weight.size = width) :
    Soundness.uniformProb (lostEscape width candidates claims) ≤
      (candidates.card : ℚ) * (claims.size - 1 : Nat) / 2^192 := by
  classical
  have sub : lostEscape width candidates claims ⊆ candidateEscape candidates claims := by
    simp only [Finset.subset_iff, lostEscape, Finset.mem_filter,
      Finset.mem_univ, true_and]
    intro lambda h
    obtain ⟨lost, fails⟩ := h
    by_contra outside
    exact fails (lost_preserved width candidates claims lambda sizes lost outside)
  calc
    _ ≤ Soundness.uniformProb (candidateEscape candidates claims) := by
      unfold Soundness.uniformProb
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast Finset.card_le_card sub) (by positivity)
    _ ≤ _ := candidate_escape_probability candidates claims
      (by intro f hf j; rw [sizes f hf]; exact shape j)

end Whir.InitialBatching
