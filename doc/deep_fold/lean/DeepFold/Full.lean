/-
The set `𝒯` of Definition 4.5 of the paper exists as a finite set: all candidates `(c, P)` with
`P` in the list of the fold `O_c`. With it, the theorems of `Lanes.lean` and `Claim.lean`, stated
for any finite set `T` of candidates with degree at most `d` and agreement at least `A`, apply to
`𝒯` itself.
-/
import DeepFold.Lanes

open Polynomial Finset
open scoped Classical

namespace DeepFold

variable {K : Type*} [Field K] [Fintype K] {ι : Type*} [Fintype ι]

omit [Fintype K] in
/-- Over a finite field there are finitely many polynomials of degree at most `d`. -/
theorem finite_natDegree_le [Finite K] (d : ℕ) : {P : K[X] | P.natDegree ≤ d}.Finite := by
  have hsub : {P : K[X] | P.natDegree ≤ d} ⊆
      Set.range (fun v : Fin (d + 1) → K => ∑ i : Fin (d + 1), C (v i) * X ^ (i : ℕ)) := by
    intro P hP
    refine ⟨fun i => P.coeff i, ?_⟩
    have h1 := P.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hP)
    rw [← Fin.sum_univ_eq_sum_range (fun i => C (P.coeff i) * X ^ i) (d + 1)] at h1
    exact h1.symm
  exact (Set.finite_range _).subset hsub

/-- The set of candidates with lanes of degree at most `d` is finite. -/
theorem finite_candL (d : ℕ) :
    {e : CandL ι K | ∀ u, (e.2 u).natDegree ≤ d}.Finite := by
  have h1 : (Set.univ.pi (fun _ : ι => {P : K[X] | P.natDegree ≤ d})).Finite :=
    Set.Finite.pi (fun _ => finite_natDegree_le d)
  have h2 : ((Set.univ : Set (K × K)) ×ˢ
      (Set.univ.pi (fun _ : ι => {P : K[X] | P.natDegree ≤ d}))).Finite :=
    Set.finite_univ.prod h1
  refine h2.subset ?_
  intro e he
  exact ⟨Set.mem_univ _, fun u _ => he u⟩

/-- `𝒯`: all `(c, P)` with `P` a tuple of degree at most `d` agreeing with the fold
`O₁ + a_c O₀` on at least `A` columns of `D`. -/
noncomputable def fullT (D : Finset K) (O₀ O₁ : K → ι → K) (d A : ℕ) : Finset (CandL ι K) :=
  (finite_candL (K := K) (ι := ι) d).toFinset.filter (fun e => A ≤ (agrL D O₀ O₁ e).card)

theorem mem_fullT {D : Finset K} {O₀ O₁ : K → ι → K} {d A : ℕ} {e : CandL ι K} :
    e ∈ fullT D O₀ O₁ d A ↔ (∀ u, (e.2 u).natDegree ≤ d) ∧ A ≤ (agrL D O₀ O₁ e).card := by
  simp [fullT]

theorem fullT_natDegree_le (D : Finset K) (O₀ O₁ : K → ι → K) (d A : ℕ) :
    ∀ e ∈ fullT D O₀ O₁ d A, ∀ u, (e.2 u).natDegree ≤ d := fun _ he => (mem_fullT.mp he).1

theorem fullT_agr (D : Finset K) (O₀ O₁ : K → ι → K) (d A : ℕ) :
    ∀ e ∈ fullT D O₀ O₁ d A, A ≤ (agrL D O₀ O₁ e).card := fun _ he => (mem_fullT.mp he).2

end DeepFold
