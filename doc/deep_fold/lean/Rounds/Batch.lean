/-
The batching challenge: transition M1 of Theorem 5.2 of the paper (Section 5.4) and of
Theorem 5.6 (Section 5.5), and the root count used again inside M3.

One pinned candidate, several claims carrying distinct powers of `λ`: if the candidate violates
one claim, the batch stays violated for all but `J - 1` values of `λ`. There is no union over the
list, because every other list member violates a point claim, which is not batched.
-/
import Rounds.Basic

open Polynomial Finset
open scoped Classical

namespace Rounds

open DeepFold

variable {K : Type*} [Field K] [Fintype K]

/-- The root count of a batch: `∑_k λ^(e k) δ_k` with pairwise distinct exponents `e k ≤ N` and
some `δ_k ≠ 0` vanishes for at most `N` values of `λ`. -/
theorem card_powsum_zero_le {κ : Type*} [Fintype κ] (e : κ → ℕ) (he : Function.Injective e)
    {N : ℕ} (hN : ∀ k, e k ≤ N) (δ : κ → K) (hδ : ∃ k, δ k ≠ 0) :
    (univ.filter (fun l : K => ∑ k, l ^ e k * δ k = 0)).card ≤ N := by
  obtain ⟨k₀, hk₀⟩ := hδ
  let p : K[X] := ∑ k, C (δ k) * X ^ e k
  have hpe : ∀ l : K, p.eval l = ∑ k, l ^ e k * δ k := by
    intro l
    simp only [p, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    exact sum_congr rfl (fun k _ => mul_comm _ _)
  have hcoeff : p.coeff (e k₀) = δ k₀ := by
    simp only [p, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    rw [sum_eq_single k₀]
    · simp
    · intro k _ hk
      have hne : e k₀ ≠ e k := fun h => hk (he h).symm
      simp [hne]
    · intro h
      exact absurd (mem_univ _) h
  have hp : p ≠ 0 := by
    intro h
    rw [h, coeff_zero] at hcoeff
    exact hk₀ hcoeff.symm
  have hdeg : p.natDegree ≤ N := by
    refine natDegree_sum_le_of_forall_le _ _ (fun k _ => ?_)
    exact (natDegree_C_mul_X_pow_le _ _).trans (hN k)
  calc (univ.filter (fun l : K => ∑ k, l ^ e k * δ k = 0)).card
      = (univ.filter (fun l : K => p.eval l = 0)).card := by simp only [hpe]
    _ ≤ p.natDegree := card_roots_le hp
    _ ≤ N := hdeg

/-- The root count for claims indexed by `Fin J` with the powers `λ^0, ..., λ^(J-1)`: at most
`J - 1` values of `λ`. -/
theorem card_batch_zero_le {J : ℕ} (δ : Fin J → K) (hδ : ∃ k, δ k ≠ 0) :
    (univ.filter (fun l : K => ∑ k : Fin J, l ^ (k : ℕ) * δ k = 0)).card ≤ J - 1 :=
  card_powsum_zero_le (fun k : Fin J => (k : ℕ)) Fin.val_injective (fun k => by omega) δ hδ

variable {ι : Type*} [Fintype ι]

/-- The batched weight `∑_k λ^(k-1) W_k` of Protocol 4.2 of the paper, Open (claims indexed from
`0`). -/
noncomputable def batchW {J : ℕ} (Wk : Fin J → (ι → K[X]) →ₗ[K] K) (l : K) :
    (ι → K[X]) →ₗ[K] K :=
  ∑ k : Fin J, l ^ (k : ℕ) • Wk k

/-- The batched value `∑_k λ^(k-1) c_k`. -/
noncomputable def batchC {J : ℕ} (ck : Fin J → K) (l : K) : K :=
  ∑ k : Fin J, l ^ (k : ℕ) * ck k

/-- **Transition M1 of Theorem 5.2 and of Theorem 5.6 of the paper** (Sections 5.4 and 5.5),
counting form.

Setting: the committed word `O = O^{(0)}` with its list at `(A, d) = (A^{(0,0)}, d^{(0)})`, the
points `z` and the commit-phase answers `y`, the `J` input claims `(W_k, c_k)`.

Hypotheses: the points are separating for the answers (`hsep`: at most one list member matches all
answers, the conclusion of Lemma 4.11), and the input claims are false relative to `B` (`hfalse`:
every list member with `B` that matches all answers violates some input claim; with `B` true this
is the definition of false input claims in Section 5.2, and with `B = Bad` the hypothesis of
Theorem 5.6).

Conclusion: for all but at most `J - 1` values of `λ` the state after batching is doomed:
`(I^B_{0,0})` holds for the running claim `(∑ λ^k W_k, ∑ λ^k c_k)` and the carried values `y`. -/
theorem batch_transition (D : Finset K) (O : K → ι → K) (d A : ℕ) (ex : ι → ℕ) {s : ℕ}
    (z : Fin s → K × K) (y : Fin s → K) {J : ℕ} (Wk : Fin J → (ι → K[X]) →ₗ[K] K)
    (ck : Fin J → K) (B : (ι → K[X]) → Prop)
    (hsep : ∀ U U' : ι → K[X], InList D O d A U → InList D O d A U' →
      (∀ m, evL ex (z m) U = y m) → (∀ m, evL ex (z m) U' = y m) → U = U')
    (hfalse : ∀ U : ι → K[X], InList D O d A U → B U → (∀ m, evL ex (z m) U = y m) →
      ∃ k, Wk k U ≠ ck k) :
    (univ.filter (fun l : K =>
      ¬ Doomed D O d A ex z y (batchW Wk l) (batchC ck l) B)).card ≤ J - 1 := by
  by_cases hex : ∃ U : ι → K[X], InList D O d A U ∧ B U ∧ ∀ m, evL ex (z m) U = y m
  · obtain ⟨Us, hUs, hBs, hpts⟩ := hex
    obtain ⟨k₀, hk₀⟩ := hfalse Us hUs hBs hpts
    refine (card_le_card ?_).trans
      (card_batch_zero_le (fun k => Wk k Us - ck k) ⟨k₀, sub_ne_zero.mpr hk₀⟩)
    intro l hl
    have hnd := (mem_filter.mp hl).2
    unfold Doomed at hnd
    push Not at hnd
    obtain ⟨U, hU, _, hpt, hW⟩ := hnd
    have hUU : U = Us := hsep U Us hU hUs hpt hpts
    rw [hUU] at hW
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    simp only [batchW, batchC, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
      smul_eq_mul] at hW
    simp only [mul_sub, sum_sub_distrib, hW, sub_self]
  · have hempty : univ.filter (fun l : K =>
        ¬ Doomed D O d A ex z y (batchW Wk l) (batchC ck l) B) = ∅ := by
      refine filter_eq_empty_iff.mpr (fun l _ hnd => hnd ?_)
      intro U hU hB hpt _
      exact hex ⟨U, hU, hB, hpt⟩
    rw [hempty, card_empty]
    exact Nat.zero_le _

omit [Fintype K] in
/-- **The hypothesis of Theorem 5.6 of the paper for the predicate of Corollary 5.7.**
Let `U^*` be the list member consistent with the commit-phase answers, and
`Bad(U) :⟺ U ≠ U^* or U violates an input claim`. By separation a bad list member that matches
the answers is `U^*`, so it violates an input claim: `hfalse` of `batch_transition` holds for
`Bad`, with no assumption on the claims. (If no list member matches the answers, `hfalse` holds
vacuously for every predicate.) -/
theorem k2_hfalse (D : Finset K) (O : K → ι → K) (d A : ℕ) (ex : ι → ℕ) {s : ℕ}
    (z : Fin s → K × K) (y : Fin s → K) {J : ℕ} (Wk : Fin J → (ι → K[X]) →ₗ[K] K)
    (ck : Fin J → K)
    (hsep : ∀ U U' : ι → K[X], InList D O d A U → InList D O d A U' →
      (∀ m, evL ex (z m) U = y m) → (∀ m, evL ex (z m) U' = y m) → U = U')
    {Us : ι → K[X]} (hUs : InList D O d A Us) (hpts : ∀ m, evL ex (z m) Us = y m) :
    ∀ U : ι → K[X], InList D O d A U → (U ≠ Us ∨ ∃ k, Wk k U ≠ ck k) →
      (∀ m, evL ex (z m) U = y m) → ∃ k, Wk k U ≠ ck k := by
  intro U hU hB hpt
  rcases hB with hne | hk
  · exact absurd (hsep U Us hU hUs hpt hpts) hne
  · exact hk

/-- Transition M1 as a density: at most `(J - 1) / q`, row M1 of Theorem 5.2 of the paper
(the ring-switching scalars of the outer protocol are not part of this statement). -/
theorem batch_transition_density (D : Finset K) (O : K → ι → K) (d A : ℕ) (ex : ι → ℕ) {s : ℕ}
    (z : Fin s → K × K) (y : Fin s → K) {J : ℕ} (Wk : Fin J → (ι → K[X]) →ₗ[K] K)
    (ck : Fin J → K) (B : (ι → K[X]) → Prop)
    (hsep : ∀ U U' : ι → K[X], InList D O d A U → InList D O d A U' →
      (∀ m, evL ex (z m) U = y m) → (∀ m, evL ex (z m) U' = y m) → U = U')
    (hfalse : ∀ U : ι → K[X], InList D O d A U → B U → (∀ m, evL ex (z m) U = y m) →
      ∃ k, Wk k U ≠ ck k) :
    ((univ.filter (fun l : K =>
      ¬ Doomed D O d A ex z y (batchW Wk l) (batchC ck l) B)).card : ℚ) /
        (Fintype.card K : ℚ) ≤ ((J - 1 : ℕ) : ℚ) / (Fintype.card K : ℚ) := by
  have h := batch_transition D O d A ex z y Wk ck B hsep hfalse
  have hq : (0 : ℚ) < (Fintype.card K : ℚ) := by exact_mod_cast Fintype.card_pos
  refine div_le_div_of_nonneg_right ?_ hq.le
  exact_mod_cast h

end Rounds
