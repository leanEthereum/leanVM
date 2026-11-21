/-
The gap lemma: tops of locators multiply. The degree count in the proof of Proposition 3.4(c) of
the paper is the case of a fixed set and a free flat.

`HasGap p A n g` says that `p = A + B` with every coefficient of `B` at an exponent `m` with
`n < m + g` equal to zero, that is `deg B ≤ n - g` (and `B = 0` when `g > n`). If every piece
`p i` has top `A i` with gap `g` at size `n i`, the product has top `∏ A i` with gap `g` at size
`∑ n i` (`gap_lemma`, `HasGap.natDegree_le`). Over any field.
-/
import Constructions.Padded

open Polynomial
open scoped Classical

namespace Constructions

variable {K : Type*} [Field K]

/-- `p = A + (terms of degree at most n - g)`. -/
def HasGap (p A : K[X]) (n g : ℕ) : Prop := ∀ m, n < m + g → (p - A).coeff m = 0

theorem hasGap_of_natDegree_le {p A : K[X]} {n g : ℕ} (h : (p - A).natDegree + g ≤ n) :
    HasGap p A n g := fun m hm => coeff_eq_zero_of_natDegree_lt (by omega)

/-- A fixed piece: gap as large as wanted. -/
theorem hasGap_self (p : K[X]) (n g : ℕ) : HasGap p p n g := fun m _ => by
  rw [sub_self, coeff_zero]

theorem coeff_mul_eq_zero_of_gap {q r : K[X]} {n n' g : ℕ} (hq : ∀ m, n < m + g → q.coeff m = 0)
    (hr : r.natDegree ≤ n') : ∀ m, n + n' < m + g → (q * r).coeff m = 0 := by
  intro m hm
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  have hsum : ij.1 + ij.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  by_cases hj : ij.2 ≤ n'
  · rw [hq ij.1 (by omega), zero_mul]
  · rw [coeff_eq_zero_of_natDegree_lt (p := r) (by omega), mul_zero]

/-- The gap lemma for two pieces. -/
theorem HasGap.mul {p A p' A' : K[X]} {n n' g : ℕ} (h : HasGap p A n g) (h' : HasGap p' A' n' g)
    (hA : A.natDegree ≤ n) (hp' : p'.natDegree ≤ n') : HasGap (p * p') (A * A') (n + n') g := by
  intro m hm
  have e : p * p' - A * A' = (p - A) * p' + (p' - A') * A := by ring
  rw [e, coeff_add, coeff_mul_eq_zero_of_gap h hp' m hm,
    coeff_mul_eq_zero_of_gap h' hA m (by omega), add_zero]

/-- **The gap lemma.** If `p i = A i + B i` with `deg A i ≤ n i`,
`deg p i ≤ n i` and `deg B i ≤ n i - g` for every `i`, then `∏ p i = ∏ A i + C` with
`deg C ≤ ∑ n i - g`. -/
theorem gap_lemma {ι : Type*} (s : Finset ι) (p A : ι → K[X]) (n : ι → ℕ) (g : ℕ)
    (hA : ∀ i ∈ s, (A i).natDegree ≤ n i) (hp : ∀ i ∈ s, (p i).natDegree ≤ n i)
    (h : ∀ i ∈ s, HasGap (p i) (A i) (n i) g) :
    HasGap (∏ i ∈ s, p i) (∏ i ∈ s, A i) (∑ i ∈ s, n i) g := by
  induction s using Finset.induction_on with
  | empty =>
    intro m _
    simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    refine (h a (Finset.mem_insert_self a s)).mul
      (ih (fun i hi => hA i (Finset.mem_insert_of_mem hi))
        (fun i hi => hp i (Finset.mem_insert_of_mem hi))
        (fun i hi => h i (Finset.mem_insert_of_mem hi)))
      (hA a (Finset.mem_insert_self a s)) ?_
    exact (natDegree_prod_le _ _).trans
      (Finset.sum_le_sum fun i hi => hp i (Finset.mem_insert_of_mem hi))

theorem HasGap.natDegree_le {p A : K[X]} {n g : ℕ} (h : HasGap p A n g) :
    (p - A).natDegree ≤ n - g := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  exact h N (by omega)

/-- The gap lemma for locators of a disjoint union: if `L_{S i} = A i + B i` with
`deg A i ≤ |S i|` and `deg B i ≤ |S i| - g`, then `L_S = ∏ A i + C` with `deg C ≤ |S| - g` for
`S` the disjoint union of the `S i`. -/
theorem gap_lemma_locator {ι : Type*} (s : Finset ι) (S : ι → Finset K) (A : ι → K[X]) (g : ℕ)
    (hdisj : (s : Set ι).PairwiseDisjoint S) (hA : ∀ i ∈ s, (A i).natDegree ≤ (S i).card)
    (h : ∀ i ∈ s, HasGap (locator (S i)) (A i) (S i).card g) :
    (locator (s.biUnion S) - ∏ i ∈ s, A i).natDegree ≤ (s.biUnion S).card - g := by
  rw [Finset.card_biUnion hdisj, locator, Finset.prod_biUnion hdisj]
  exact (gap_lemma s (fun i => locator (S i)) A (fun i => (S i).card) g hA
    (fun i _ => (locator_natDegree (S i)).le) h).natDegree_le

/-- The pieces on a subspace domain (characteristic two): a free flat `a + V` has top `X ^ |V|`
with gap `|V| / 2`. -/
theorem hasGap_flat [CharP K 2] (V : AddSubgroup K) [Finite V] (a : K) :
    HasGap (locator (flat V a)) (X ^ Nat.card V) (Nat.card V) (Nat.card V - Nat.card V / 2) := by
  refine hasGap_of_natDegree_le ?_
  have h := natDegree_locator_flat_sub_le V a
  rw [← natDegree_neg, neg_sub] at h
  omega

/-- A coset of a fixed subspace `W` has top `L_W` with gap `|W|`. -/
theorem hasGap_coset (W : AddSubgroup K) [Finite W] (a : K) :
    HasGap (locator (flat W a)) (subPoly W) (Nat.card W) (Nat.card W) := by
  refine hasGap_of_natDegree_le ?_
  rw [flat, locator_coset, sub_sub_cancel_left, natDegree_neg, natDegree_C]
  omega

end Constructions
