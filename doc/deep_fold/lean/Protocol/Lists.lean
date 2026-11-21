/-
The list `List(O; A, d)` of an interleaved word (Definition 2.1 of the paper), and its link with
the candidate set `𝒯 = {(c, P) : P ∈ List(O_c; A, d)}` of `DeepFold` (Definition 4.5).

`listW D O d A` is `List(O; A, d)`: the tuples of polynomials of degree at most `d` that agree
with the interleaved word `O` on at least `A` columns of `D`. The fibre of `𝒯` over a challenge
`c` is the list of the fold `O₁ + a_c O₀`, so a bound on the lists of the folds is the `Λ` of
`DeepFold.lemmaF_exc` (the `L` of Lemma 4.10).
-/
import DeepFold.Full

open Polynomial Finset
open scoped Classical

namespace Protocol

open DeepFold

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

/-- The agreement set of a tuple with an interleaved word: the columns of `D` where all lanes
agree. -/
noncomputable def agrW (D : Finset K) (O : K → ι → K) (U : ι → K[X]) : Finset K :=
  D.filter (fun x => ∀ u, (U u).eval x = O x u)

/-- The fold `O_c = O₁ + a_c O₀` of two interleaved words, `a_c(x) = α + β x`. -/
def foldPair (O₀ O₁ : K → ι → K) (c : K × K) : K → ι → K :=
  fun x u => O₁ x u + (c.1 + c.2 * x) * O₀ x u

/-- The agreement set of a candidate `(c, P)` in `DeepFold` is the agreement set of `P` with the
fold `O_c`. -/
theorem agrL_eq_agrW (D : Finset K) (O₀ O₁ : K → ι → K) (e : CandL ι K) :
    agrL D O₀ O₁ e = agrW D (foldPair O₀ O₁ e.1) e.2 := rfl

/-- The set `𝒜_{F,G}` of `DeepFold` (`agrPairL`) for a pair of tuples is the agreement set of the
joined tuple with the joined word, the lanes being two copies of `ι`. -/
theorem agrPairL_eq_agrW (D : Finset K) (O₀ O₁ : K → ι → K) (F₀ G₀ : ι → K[X]) :
    agrPairL D O₀ O₁ F₀ G₀ =
      agrW D (fun x => Sum.elim (O₀ x) (O₁ x)) (Sum.elim F₀ G₀) := by
  unfold agrPairL agrW
  refine filter_congr (fun x _ => ?_)
  constructor
  · rintro h (u | u)
    · exact (h u).1
    · exact (h u).2
  · intro h u
    exact ⟨h (Sum.inl u), h (Sum.inr u)⟩

variable [Fintype K]

/-- Over a finite field there are finitely many tuples of degree at most `d`. -/
theorem finite_tuples (d : ℕ) : {U : ι → K[X] | ∀ u, (U u).natDegree ≤ d}.Finite := by
  have h : (Set.univ.pi (fun _ : ι => {P : K[X] | P.natDegree ≤ d})).Finite :=
    Set.Finite.pi (fun _ => finite_natDegree_le d)
  exact h.subset (fun U hU u _ => hU u)

/-- `List(O; A, d)`: the tuples of degree at most `d` agreeing with `O` on at least `A` columns
of `D`. -/
noncomputable def listW (D : Finset K) (O : K → ι → K) (d A : ℕ) : Finset (ι → K[X]) :=
  (finite_tuples (K := K) (ι := ι) d).toFinset.filter (fun U => A ≤ (agrW D O U).card)

theorem mem_listW {D : Finset K} {O : K → ι → K} {d A : ℕ} {U : ι → K[X]} :
    U ∈ listW D O d A ↔ (∀ u, (U u).natDegree ≤ d) ∧ A ≤ (agrW D O U).card := by
  simp [listW]

theorem listW_natDegree_le (D : Finset K) (O : K → ι → K) (d A : ℕ) :
    ∀ U ∈ listW D O d A, ∀ u, (U u).natDegree ≤ d := fun _ hU => (mem_listW.mp hU).1

/-- Lists at a larger agreement are subsets (Section 5.1 of the paper, after Hypothesis 5.1). -/
theorem listW_anti (D : Finset K) (O : K → ι → K) (d : ℕ) {A A' : ℕ} (h : A ≤ A') :
    listW D O d A' ⊆ listW D O d A := fun _ hU =>
  mem_listW.mpr ⟨(mem_listW.mp hU).1, h.trans (mem_listW.mp hU).2⟩

/-- The list at a larger agreement is no larger. -/
theorem card_listW_le (D : Finset K) (O : K → ι → K) (d : ℕ) {A A' : ℕ} (h : A ≤ A') :
    (listW D O d A').card ≤ (listW D O d A).card :=
  card_le_card (listW_anti D O d h)

/-- `(c, P) ∈ 𝒯` exactly when `P` is in the list of the fold `O_c`. -/
theorem mem_fullT_iff_mem_listW {D : Finset K} {O₀ O₁ : K → ι → K} {d A : ℕ} {e : CandL ι K} :
    e ∈ fullT D O₀ O₁ d A ↔ e.2 ∈ listW D (foldPair O₀ O₁ e.1) d A := by
  rw [mem_fullT, mem_listW, agrL_eq_agrW]

/-- The fibre of `𝒯` over a challenge is the list of the fold by that challenge. -/
theorem card_fullT_fiber (D : Finset K) (O₀ O₁ : K → ι → K) (d A : ℕ) (c : K × K) :
    ((fullT D O₀ O₁ d A).filter (fun e => e.1 = c)).card =
      (listW D (foldPair O₀ O₁ c) d A).card := by
  refine card_bij (fun e _ => e.2) ?_ ?_ ?_
  · intro e he
    obtain ⟨h1, h2⟩ := mem_filter.mp he
    rw [← h2]
    exact mem_fullT_iff_mem_listW.mp h1
  · intro e he e' he' h
    exact Prod.ext ((mem_filter.mp he).2.trans (mem_filter.mp he').2.symm) h
  · intro P hP
    exact ⟨(c, P), mem_filter.mpr ⟨mem_fullT_iff_mem_listW.mpr hP, rfl⟩, rfl⟩

/-- A bound on the lists of all folds is a bound `Λ` as `DeepFold.lemmaF_exc` takes it. -/
theorem fullT_fiber_le (D : Finset K) (O₀ O₁ : K → ι → K) (d A : ℕ) {L : ℕ}
    (hL : ∀ c : K × K, (listW D (foldPair O₀ O₁ c) d A).card ≤ L) (c : K × K) :
    ((fullT D O₀ O₁ d A).filter (fun e => e.1 = c)).card ≤ L :=
  (card_fullT_fiber D O₀ O₁ d A c).trans_le (hL c)

end Protocol
