/-
The hypotheses of Theorem R can be met together.

* `PLsub_one_of_prod_le`: the hypothesis PL`(f, 1)` holds as soon as the elementary bound of
  note 37 Lemma 3.2 for the ordinary lists is at most `f`: then no list has more than `f` members.
* `concrete_K64`: Theorem R applied on a concrete field of characteristic two, with its
  hypothesis discharged. The field is Mathlib's `GaloisField 2 64`, the domain is the whole field
  (a subspace of dimension 64), `k = 2`, `T = 2^64 - 1`, `f = 2`, `j₀ = 1`. This is a consistency
  check of the statement, not a parameter set of leanVM, and its conclusion is weaker than
  `ordinary_bound`.
-/
import PeriodDescent.TheoremR

open Polynomial Finset
open scoped Classical

namespace PeriodDescent

/-- PL`(f, 1)` from the elementary bound: if `∏_{i < k} (n - i) ≤ f ∏_{i < k} (T - i)`, no ordinary
list has more than `f` members, so the hypothesis holds with nothing to check. -/
theorem PLsub_one_of_prod_le {F : Type*} [Field F] (D : Finset F) (k T f : ℕ) (hk : 1 ≤ k)
    (hkT : k ≤ T)
    (h : ∏ i ∈ Finset.range k, (D.card - i) ≤ f * ∏ i ∈ Finset.range k, (T - i)) :
    PLsub D k (T - k + 1) f 1 := by
  intro j hj U _ hU hUc κ _ hκ0 v S hS hcard
  have hj0 : j = 0 := by omega
  subst hj0
  exfalso
  have hκ' : κ = k - 1 := hκ0 rfl
  have hU0 : U = {0} := by
    rw [pow_zero] at hUc
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hUc
    have h0 := hU.1
    rw [hu] at h0
    rw [hu, Finset.mem_singleton.mp h0]
  have hsub : subPoly U = X := by
    rw [hU0]
    simp [subPoly]
  have hfib : ∀ y, (D.filter (fun x => (subPoly U).eval x = y)).card ≤ 1 := by
    intro y
    rw [hsub]
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    have h1 := (Finset.mem_filter.mp ha).2
    have h2 := (Finset.mem_filter.mp hb).2
    rw [eval_X] at h1 h2
    rw [h1, h2]
  have h1 := base_bound_nat D (subPoly U) v κ 1 (2 ^ 0 * κ + (T - k + 1)) hfib S
    (fun P hP => (hS P hP).1) (fun P hP => (hS P hP).2)
  have e1 : 2 ^ 0 * κ + (T - k + 1) = T := by
    rw [hκ', pow_zero, one_mul]
    omega
  have e2 : κ + 1 = k := by omega
  rw [e1, e2] at h1
  simp only [one_mul] at h1
  have hP : 0 < ∏ i ∈ Finset.range k, (T - i) := Finset.prod_pos fun i hi => by
    have := Finset.mem_range.mp hi
    omega
  have h3 := Nat.le_of_mul_le_mul_right (h1.trans h) hP
  omega

/-- `GF(2^64)`. -/
abbrev K64 : Type := GaloisField 2 64

/-- All the points of `GF(2^64)`. -/
noncomputable def allK64 : Finset K64 := (Set.finite_univ : (Set.univ : Set K64).Finite).toFinset

theorem allK64_isSubspace : IsSubspace allK64 :=
  ⟨by simp [allK64], fun _ _ _ _ => by simp [allK64]⟩

theorem allK64_card : allK64.card = 2 ^ 64 := by
  unfold allK64
  rw [← Set.ncard_eq_toFinset_card _ Set.finite_univ, Set.ncard_univ]
  exact GaloisField.card 2 64 (by norm_num)

/-- **Theorem R on a concrete field, with no hypothesis left.** On the domain of all the points of
`GF(2^64)`, with `k = 2`, `T = 2^64 - 1`, `f = 2`, `j₀ = 1`, the hypothesis PL`(2, 1)` holds, and
the conclusion of `theoremR` follows. -/
theorem concrete_K64 (w : K64 → K64) (S : Finset K64[X])
    (hdeg : ∀ P ∈ S, P.degree < ((2 : ℕ) : WithBot ℕ))
    (hagr : ∀ P ∈ S, 2 ^ 64 - 1 ≤ (allK64.filter (fun x => P.eval x = w x)).card) :
    (S.card : ℚ) ≤ (((2 + 1).choose 3 : ℕ) : ℚ) ^ 1 * 2 ^ (64 * 1 - 1 * (1 - 1) / 2)
      * (baseB (2 ^ 64) (2 ^ 64 - 1 - 2 + 1) (2 ^ 1) ((2 - 1) / 2 ^ 1) + 1) :=
  theoremR allK64 allK64_isSubspace 64 2 (2 ^ 64 - 1) 2 1 allK64_card (by norm_num)
    (by norm_num) (by norm_num) le_rfl (by norm_num)
    (PLsub_one_of_prod_le allK64 2 (2 ^ 64 - 1) 2 (by norm_num) (by norm_num)
      (by rw [allK64_card]; norm_num [Finset.prod_range_succ])) w S hdeg hagr

end PeriodDescent
