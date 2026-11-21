/-
The extractor step of Theorem 5.6 of the paper (Section 5.5): the descent through one fold
round.

A tuple `P` of degree at most `d` agrees with the fold `O_c` on the set `S` of at least `A` columns.
A near tuple of the unfolded word `O` on `S` (the pair `(F, G)` that Lemma 4.10's clause (b) speaks
of) is unique when `A ≥ d + 3`, lies in `List(O; A - 1, d)`, and folds to `P`. So the descent step
"replace `P` by the near tuple of the unfolded word on the agreement set of `P`" is well defined, is
unique decoding with at most one error on a known set, and inverts the fold.
-/
import Rounds.Basic

open Polynomial Finset
open scoped Classical

namespace Rounds

open DeepFold

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

/-- **Uniqueness of the near tuple** (Lemma 5.5 of the paper): two tuples of degree at most `d`
that each agree with `O` on all but at most one column of a set `S` of at least `d + 3` columns
are equal. -/
theorem nearT_unique {D : Finset K} {O : K → ι → K} {d : ℕ} {S : Finset K}
    (hS : d + 3 ≤ S.card) {U U' : ι → K[X]} (hU : NearT D O d S U) (hU' : NearT D O d S U') :
    U = U' := by
  funext u
  have hcard : d + 1 ≤ (S \ ((S \ agr D O U) ∪ (S \ agr D O U'))).card := by
    have h1 := le_card_sdiff ((S \ agr D O U) ∪ (S \ agr D O U')) S
    have h2 := card_union_le (S \ agr D O U) (S \ agr D O U')
    have h3 := hU.2
    have h4 := hU'.2
    omega
  refine eq_of_degrees_lt_of_eval_finset_eq (S \ ((S \ agr D O U) ∪ (S \ agr D O U'))) ?_ ?_ ?_
  · exact degree_le_natDegree.trans_lt (by exact_mod_cast lt_of_le_of_lt (hU.1 u) hcard)
  · exact degree_le_natDegree.trans_lt (by exact_mod_cast lt_of_le_of_lt (hU'.1 u) hcard)
  · intro x hx
    obtain ⟨hxS, hxn⟩ := mem_sdiff.mp hx
    have hxU : x ∈ agr D O U := by
      by_contra hcon
      exact hxn (mem_union_left _ (mem_sdiff.mpr ⟨hxS, hcon⟩))
    have hxU' : x ∈ agr D O U' := by
      by_contra hcon
      exact hxn (mem_union_right _ (mem_sdiff.mpr ⟨hxS, hcon⟩))
    rw [(mem_filter.mp hxU).2 u, (mem_filter.mp hxU').2 u]

/-- A near tuple on a set of at least `A` columns is a member of `List(O; A - 1, d)`
(`A - 1 = A^{(i,j-1)}` when `A = A^{(i,j)}`). -/
theorem NearT.inList {D : Finset K} {O : K → ι → K} {d A : ℕ} {S : Finset K} (hS : A ≤ S.card)
    {U : ι → K[X]} (hU : NearT D O d S U) : InList D O d (A - 1) U := by
  refine ⟨hU.1, ?_⟩
  have h1 : S.card ≤ (S \ agr D O U).card + (agr D O U).card := card_le_card_sdiff_add_card
  have h2 := hU.2
  omega

/-- **The descent inverts the fold**: if `P` has degree at most `d` and agrees with the fold `O_c`
on at least `d + 3` columns, a near tuple `U = (F, G)` of `O` on the agreement set of `P` has
`P = G + (α + β X) F`. -/
theorem NearT.fold_eq {D : Finset K} {O : K → ι ⊕ ι → K} {d : ℕ} {c : K × K} {P : ι → K[X]}
    (hP : ∀ u, (P u).natDegree ≤ d) (hS : d + 3 ≤ (agr D (foldWord c O) P).card)
    {U : ι ⊕ ι → K[X]} (hU : NearT D O d (agr D (foldWord c O) P) U) : P = foldTuple c U := by
  funext u
  have hcard : d + 2 ≤ (agr D (foldWord c O) P \ (agr D (foldWord c O) P \ agr D O U)).card := by
    have h1 := le_card_sdiff (agr D (foldWord c O) P \ agr D O U) (agr D (foldWord c O) P)
    have h2 := hU.2
    omega
  have hfd : (foldTuple c U u).natDegree ≤ d + 1 := by
    unfold foldTuple
    refine natDegree_add_le_of_degree_le ((hU.1 _).trans (Nat.le_succ d)) ?_
    have h := natDegree_mul_le_of_le (aff_natDegree_le c) (hU.1 (Sum.inl u))
    omega
  refine eq_of_degrees_lt_of_eval_finset_eq
    (agr D (foldWord c O) P \ (agr D (foldWord c O) P \ agr D O U)) ?_ ?_ ?_
  · exact degree_le_natDegree.trans_lt (by exact_mod_cast lt_of_le_of_lt (hP u) (by omega))
  · exact degree_le_natDegree.trans_lt (by exact_mod_cast lt_of_le_of_lt hfd (by omega))
  · intro x hx
    obtain ⟨hxS, hxn⟩ := mem_sdiff.mp hx
    have hxU : x ∈ agr D O U := by
      by_contra hcon
      exact hxn (mem_sdiff.mpr ⟨hxS, hcon⟩)
    rw [(mem_filter.mp hxS).2 u, (mem_filter.mp (agr_subset_agr_foldTuple D O c U hxU)).2 u]

/-- The degree bounds `(d - 1, d)` of the unfolded pair: when `β ≠ 0`, the first half `F` of the
near tuple has degree less than `d` (for `β = 0` the fold does not see the top coefficient of
`F`; this is the line `β = const` of Lemma 4.7(b) of the paper). -/
theorem NearT.degree_lt {D : Finset K} {O : K → ι ⊕ ι → K} {d : ℕ} {c : K × K} {P : ι → K[X]}
    (hP : ∀ u, (P u).natDegree ≤ d) (hS : d + 3 ≤ (agr D (foldWord c O) P).card)
    {U : ι ⊕ ι → K[X]} (hU : NearT D O d (agr D (foldWord c O) P) U) (hβ : c.2 ≠ 0) (u : ι) :
    (U (Sum.inl u)).degree < (d : WithBot ℕ) := by
  have hfold := congrFun (hU.fold_eq hP hS) u
  unfold foldTuple at hfold
  by_cases hF : U (Sum.inl u) = 0
  · rw [hF, degree_zero]
    exact WithBot.bot_lt_coe d
  have haff : (aff c).natDegree = 1 := by
    unfold aff
    rw [add_comm]
    exact natDegree_linear hβ
  have haff0 : aff c ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at haff
    exact zero_ne_one haff
  have hmul : aff c * U (Sum.inl u) = P u - U (Sum.inr u) := by
    rw [hfold]
    ring
  have hdeg : (aff c * U (Sum.inl u)).natDegree ≤ d := by
    rw [hmul]
    exact (natDegree_sub_le_of_le (hP u) (hU.1 _)).trans_eq (max_self d)
  rw [natDegree_mul haff0 hF, haff] at hdeg
  exact degree_le_natDegree.trans_lt
    (by exact_mod_cast (by omega : (U (Sum.inl u)).natDegree < d))

/-- **The descent step of Theorem 5.6 of the paper** (the paragraph *Descent* of its proof, and
the step of the extractor of Section 5.5). Let `A = A^{(i,j)} ≥ d + 3` (which is (S2)) and let `P`
have degree at most `d`. If `P` does not satisfy the pull-back `pull B` of a predicate `B`, then
`P` is in `List(O_c; A, d)`, and there is a tuple `T` such that:

- `T` is a near tuple of the unfolded word `O` on the agreement set of `P` with `O_c`, and the
  only one, so it is determined by `P`, `c` and the columns of `O` (unique decoding with at most
  one error on a known set);
- `T ∈ List(O; A - 1, d)`, the list of the previous round;
- `¬ B(T)`;
- `P` is the fold of `T`. -/
theorem descent_step (D : Finset K) (O : K → ι ⊕ ι → K) (d A : ℕ) (c : K × K)
    (B : (ι ⊕ ι → K[X]) → Prop) (hdA : d + 3 ≤ A) {P : ι → K[X]}
    (hP : ∀ u, (P u).natDegree ≤ d) (hnb : ¬ pull D O d A c B P) :
    InList D (foldWord c O) d A P ∧
      ∃ T : ι ⊕ ι → K[X], NearT D O d (agr D (foldWord c O) P) T ∧ InList D O d (A - 1) T ∧
        ¬ B T ∧ P = foldTuple c T ∧
        ∀ T' : ι ⊕ ι → K[X], NearT D O d (agr D (foldWord c O) P) T' → T' = T := by
  unfold pull at hnb
  push Not at hnb
  obtain ⟨hA, T, hT, hBT⟩ := hnb
  exact ⟨⟨hP, hA⟩, T, hT, hT.inList hA, hBT, hT.fold_eq hP (hdA.trans hA),
    fun T' hT' => nearT_unique (hdA.trans hA) hT' hT⟩

/-- The extractor step as existence and uniqueness: for `P` of degree at most `d` agreeing with
the fold `O_c` on at least `A ≥ d + 3` columns, if the unfolded word has a near tuple on the
agreement set of `P` at all (which is what Lemma 4.10's clause (b) provides on a run that preserved
the relativised invariant), then it has exactly one. -/
theorem existsUnique_nearT (D : Finset K) (O : K → ι ⊕ ι → K) (d A : ℕ) (c : K × K)
    (hdA : d + 3 ≤ A) {P : ι → K[X]} (hA : A ≤ (agr D (foldWord c O) P).card)
    (hex : ∃ T : ι ⊕ ι → K[X], NearT D O d (agr D (foldWord c O) P) T) :
    ∃! T : ι ⊕ ι → K[X], NearT D O d (agr D (foldWord c O) P) T := by
  obtain ⟨T, hT⟩ := hex
  exact ⟨T, hT, fun T' hT' => nearT_unique (hdA.trans hA) hT' hT⟩

end Rounds
