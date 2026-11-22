/-
Note 37 Theorem 3.5 (the dimension induction, conditional on DP), with Corollary 3.4, for
polynomials over a field of characteristic two on a subspace domain.

* `DPsub`: the hypothesis DP`(B)`: at every level `j < j₀`, every list of a level problem has a
  pair `(P₀, P₁)` for which at most `B` members `P` have a function `(P - P₀) / (P₁ - P₀)` that is
  neither constant nor periodic for a nonzero direction of the quotient. In the notation of the
  note: `B^diff_{N,j}(κ, Δ) ≤ B`.
* `theorem35`: under DP`(B)`, for `k ≤ 2^{j₀}` and `j₀ ≤ N`, every word has at most
  `2^(N j₀ - j₀ (j₀ - 1) / 2) (j₀ (B + 2) + ⌊n / Δ⌋)` polynomials of degree `< k` agreeing with it
  on at least `T` points. With `j₀ = J = ⌈log₂ k⌉` this is the bound of the note.
-/
import PeriodDescent.TheoremR

open Polynomial Finset
open scoped Classical

namespace PeriodDescent

variable {F : Type*} [Field F]

/-- **The hypothesis DP`(B)` of note 37 Theorem 3.5**, for the levels `j < j₀`: every list of at
least two members of a level problem (subspace `U ⊆ D` with `2^j` elements, degree bound
`κ ≤ ⌊(k - 1) / 2^j⌋`, word with blanks, slack `Δ`) has two members `P₀ ≠ P₁` such that at most
`B` members do not form a bad triple with them. -/
def DPsub (D : Finset F) (k Δ B j0 : ℕ) : Prop :=
  ∀ j < j0, ∀ U : Finset F, U ⊆ D → IsSubspace U → U.card = 2 ^ j →
    ∀ κ : ℕ, κ ≤ (k - 1) / 2 ^ j → (j = 0 → κ = k - 1) → ∀ v : F → Option F,
      ∀ S : Finset F[X],
        (∀ P ∈ S, P.natDegree ≤ κ ∧ 2 ^ j * κ + Δ ≤ polyAgr D (subPoly U) v P) → 2 ≤ S.card →
        ∃ P0 ∈ S, ∃ P1 ∈ S, P0 ≠ P1 ∧
          ∀ T ⊆ S, (∀ P ∈ T, ¬ BadTriple D (subPoly U) P0 P1 P) → T.card ≤ B

/-- **Note 37 Theorem 3.5.** Let `F` be a field of characteristic two, `D ⊆ F` a subspace with
`2^N` elements, `1 ≤ k ≤ T`, `Δ = T - k + 1`, `j₀ ≤ N` with `k ≤ 2^{j₀}`. Under DP`(B)`, for every
word `w : D → F` the number of polynomials of degree `< k` that agree with `w` on at least `T`
points of `D` is at most `2^(N j₀ - j₀ (j₀ - 1) / 2) (j₀ (B + 2) + ⌊2^N / Δ⌋)`. -/
theorem theorem35 [CharP F 2] (D : Finset F) (hD : IsSubspace D) (N k T B j0 : ℕ)
    (hN : D.card = 2 ^ N) (hk : 1 ≤ k) (hkT : k ≤ T) (hj0 : j0 ≤ N) (hkj : k ≤ 2 ^ j0)
    (hDP : DPsub D k (T - k + 1) B j0)
    (w : F → F) (S : Finset F[X]) (hdeg : ∀ P ∈ S, P.degree < k)
    (hagr : ∀ P ∈ S, T ≤ (D.filter (fun x => P.eval x = w x)).card) :
    S.card ≤ 2 ^ (N * j0 - j0 * (j0 - 1) / 2) * (j0 * (B + 2) + 2 ^ N / (T - k + 1)) := by
  refine abstract_descent_DP (Pb := LevelPb D k) (C := F[X]) (A := F) (fun p => p.j)
    (fun p => p.Mem (T - k + 1)) (fun p => (D.image (fun x => p.ℓ.eval x)).erase 0)
    (fun _ a c0 c1 c => Periodic a (c1 - c0) (c - c0)) N j0 B (2 ^ N / (T - k + 1)) hj0
    (fun p _ => p.hℓ.dirs_card_le hD hN) ?_ ?_ ?_ (LevelPb.ofWord D k w) rfl S
    (fun P hP => LevelPb.ofWord_mem D hk hkT (hdeg P hP) (hagr P hP))
  · -- the descent step
    intro p _ c0 c1 h0 h1 h01 a ha
    exact p.descent_step hD _ h0 h1 h01 ha
  · -- the hypothesis
    intro p hp S' hS' hcard
    obtain ⟨U, hUD, hU, hUc, hℓ⟩ := p.hℓ.exists_subspace hD
    obtain ⟨P0, hP0, P1, hP1, h01, hB⟩ :=
      hDP p.j hp U hUD hU hUc p.κ p.hκ p.hκ0 p.v S' (by rw [← hℓ]; exact hS') hcard
    refine ⟨P0, hP0, P1, hP1, h01, fun T hT hTper => hB T hT fun P hP hbad => ?_⟩
    rw [← hℓ] at hbad
    exact hTper P hP (hbad.exists_dir hD hN p.hℓ (by omega))
  · -- the base case: degree `0`, at most `n / Δ` members
    intro p hp S' hS'
    have hκ0 : p.κ = 0 := by
      have h1 := p.hκ
      rw [hp, Nat.div_eq_of_lt (by omega)] at h1
      omega
    have h := base_bound_nat D p.ℓ p.v p.κ (2 ^ p.j) (2 ^ p.j * p.κ + (T - k + 1))
      (p.hℓ.fiber_card_le hD) S' (fun P hP => (hS' P hP).1) (fun P hP => (hS' P hP).2)
    rw [hκ0] at h
    simp only [zero_add, Finset.prod_range_one, mul_zero, Nat.sub_zero] at h
    rw [hN] at h
    exact (Nat.le_div_iff_mul_le (by omega)).mpr h

end PeriodDescent
