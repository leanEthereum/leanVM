/-
The fold challenge: transition M2 of Theorem 5.2 of the paper (Section 5.4), and its relativised
form in Theorem 5.6 (Section 5.5), derived from Lemma 4.10(2) (`DeepFold.lemmaF_round`).

Before the challenge of round `j` the word is `O = O^{(i,j-1)}` with lanes `ι ⊕ ι` (halves `O₀`,
`O₁`), the running claim is `(W, σ)`, the carried point values are `v`, and the invariant
`(I_{i,j-1})` holds at agreement `A - 1 = A^{(i,j-1)}`. After the challenge `c = (α, β)` the word
is the fold `O_c`, the claim is `(W̃(α, ·), σ')` and the carried values are
`v + (θ^w + α + β ζ) φ`. For points outside the exceptional set, fewer than `K₀` challenges leave
a state that is not doomed.
-/
import Rounds.Basic

open Polynomial Finset
open scoped Classical

namespace Rounds

open DeepFold

variable {K : Type*} [Field K] [Fintype K] {ι : Type*} [Fintype ι]

omit [Fintype K] in
/-- (E2) of Lemma 4.4 of the paper for a tuple with lanes `ι ⊕ ι` and the exponents `exHalves`. -/
theorem evL_exHalves (ex : ι → ℕ) (w : ℕ) (z : K × K) (F₀ G₀ : ι → K[X]) :
    evL (exHalves w ex) z (Sum.elim F₀ G₀) = z.1 ^ w * evL ex z F₀ + evL ex z G₀ :=
  evL_halves ex w z (Sum.elim F₀ G₀)

/-- **Transition M2 of Theorem 5.2 and of Theorem 5.6 of the paper** (Sections 5.4 and 5.5),
counting form, in characteristic two.

Setting: domain `D` of size `n`, word `O = O^{(i,j-1)}` with lanes `ι ⊕ ι`, degree bound `d`,
agreement `A = A^{(i,j)}`, exponents `ex = e_j` of the folded tuple and `w = 2^(j-1)`,
`M ≥ max(2 q, C(n, 2))`, points `z ∉ Exc_j(O)` (threshold `K₀ (K₀ - 1) (K₀ - M)`).

If the state before the challenge is doomed, that is `(I^B_{i,j-1})`: no
`U ∈ List(O; A - 1, d)` with `B(U)` satisfies `(W, σ)` and the point claims `(z_m, v_m)` at round
`j - 1`, then for every prover message `(v_G, v_F, σ₀, σ₁, φ)` fewer than `K₀` challenges `c`
give a state that is not doomed, that is, for which `(I^{pull B}_{i,j})` fails: some
`P ∈ List(O_c; A, d)` with `(pull B)(P)` satisfies the new claim `(W̃(α, ·), σ')` and the new
point claims `(z_m, v_m + (θ_m^w + α + β ζ_m) φ_m)`. -/
theorem fold_transition [CharP K 2] (D : Finset K) (O : K → ι ⊕ ι → K) (d A : ℕ) (ex : ι → ℕ)
    (w : ℕ) {s K₀ M : ℕ} (hMq : 2 * Fintype.card K ≤ M) (hMn : D.card.choose 2 ≤ M)
    {z : Fin s → K × K}
    (hz : z ∉ ExcL (fullT D (half₀ O) (half₁ O) d A) ex s (K₀ * (K₀ - 1) * (K₀ - M)))
    (W : (ι ⊕ ι → K[X]) →ₗ[K] K) (σ : K) (v : Fin s → K) (B : (ι ⊕ ι → K[X]) → Prop)
    (hI : Doomed D O d (A - 1) (exHalves w ex) z v W σ B)
    (vG vF σ₀ σ₁ : K) (φm : Fin s → K) :
    (univ.filter (fun c : K × K =>
      ¬ Doomed D (foldWord c O) d A ex z (foldVal w z v φm c) (foldWeight W c)
        (foldClaim σ vG vF σ₀ σ₁ c) (pull D O d A c B))).card < K₀ := by
  have key := lemmaF_round D (half₀ O) (half₁ O) d A ex w hMq hMn hz (W ∘ₗ inlL) (W ∘ₗ inrL) σ v
    (fun F₀ G₀ => B (Sum.elim F₀ G₀)) ?_ vG vF σ₀ σ₁ φm
  · refine lt_of_le_of_lt (card_le_card ?_) key
    intro c hc
    have hnd := (mem_filter.mp hc).2
    unfold Doomed at hnd
    push Not at hnd
    obtain ⟨P, ⟨hPd, hPA⟩, hPB, hPpt, hPw⟩ := hnd
    refine mem_filter.mpr ⟨mem_univ _, P, hPd, ?_, ?_, ?_, ?_⟩
    · rw [← agr_foldWord]
      exact hPA
    · exact hPpt
    · exact hPw
    · intro F₀ G₀ hF hG hnear
      refine hPB hPA (Sum.elim F₀ G₀) ⟨?_, ?_⟩
      · rintro (u | u)
        · exact hF u
        · exact hG u
      · rw [agr_elim, agr_foldWord]
        exact hnear
  · intro F₀ G₀ hF hG hZ hB hpt
    rw [← weight_elim]
    refine hI (Sum.elim F₀ G₀) ⟨?_, ?_⟩ hB ?_
    · rintro (u | u)
      · exact natDegree_le_of_degree_le (le_of_lt (hF u))
      · exact hG u
    · rw [agr_elim]
      omega
    · intro m
      rw [evL_exHalves]
      exact hpt m

/-- Transition M2 as a density: the challenges after which the state is not doomed are at most
`(K₀ - 1) / q^2` of the `q^2` challenges. This is the term `(K₀ - 1)/q^2` of row M2 of Theorem 5.2
of the paper. -/
theorem fold_transition_density [CharP K 2] (D : Finset K) (O : K → ι ⊕ ι → K) (d A : ℕ)
    (ex : ι → ℕ) (w : ℕ) {s K₀ M : ℕ} (hMq : 2 * Fintype.card K ≤ M)
    (hMn : D.card.choose 2 ≤ M) {z : Fin s → K × K}
    (hz : z ∉ ExcL (fullT D (half₀ O) (half₁ O) d A) ex s (K₀ * (K₀ - 1) * (K₀ - M)))
    (W : (ι ⊕ ι → K[X]) →ₗ[K] K) (σ : K) (v : Fin s → K) (B : (ι ⊕ ι → K[X]) → Prop)
    (hI : Doomed D O d (A - 1) (exHalves w ex) z v W σ B)
    (vG vF σ₀ σ₁ : K) (φm : Fin s → K) :
    ((univ.filter (fun c : K × K =>
      ¬ Doomed D (foldWord c O) d A ex z (foldVal w z v φm c) (foldWeight W c)
        (foldClaim σ vG vF σ₀ σ₁ c) (pull D O d A c B))).card : ℚ) /
        (Fintype.card (K × K) : ℚ) ≤ ((K₀ : ℚ) - 1) / (Fintype.card K : ℚ) ^ 2 := by
  have h := fold_transition D O d A ex w hMq hMn hz W σ v B hI vG vF σ₀ σ₁ φm
  have hq : (0 : ℚ) < (Fintype.card K : ℚ) ^ 2 := by
    have : (0 : ℚ) < (Fintype.card K : ℚ) := by exact_mod_cast Fintype.card_pos
    positivity
  rw [Fintype.card_prod]
  push_cast
  rw [← sq]
  refine div_le_div_of_nonneg_right ?_ hq.le
  have h' : ((univ.filter (fun c : K × K =>
      ¬ Doomed D (foldWord c O) d A ex z (foldVal w z v φm c) (foldWeight W c)
        (foldClaim σ vG vF σ₀ σ₁ c) (pull D O d A c B))).card : ℚ) + 1 ≤ (K₀ : ℚ) := by
    exact_mod_cast h
  linarith

omit [Fintype K] in
/-- With the trivial predicate the pull-back is trivial: plain soundness needs no clause (b). -/
theorem pull_true (D : Finset K) (O : K → ι ⊕ ι → K) (d A : ℕ) (c : K × K) (P : ι → K[X]) :
    pull D O d A c (fun _ => True) P :=
  fun _ _ _ => trivial

/-- **Transition M2 of Theorem 5.2 of the paper** (plain soundness, `B` true): if no
`U ∈ List(O^{(i,j-1)}; A^{(i,j-1)}, d)` satisfies the running claim and all point claims at round
`j - 1`, then for fewer than `K₀` challenges some `P ∈ List(O^{(i,j)}; A^{(i,j)}, d)` satisfies
the running claim and all point claims at round `j`. -/
theorem fold_transition_plain [CharP K 2] (D : Finset K) (O : K → ι ⊕ ι → K) (d A : ℕ)
    (ex : ι → ℕ) (w : ℕ) {s K₀ M : ℕ} (hMq : 2 * Fintype.card K ≤ M)
    (hMn : D.card.choose 2 ≤ M) {z : Fin s → K × K}
    (hz : z ∉ ExcL (fullT D (half₀ O) (half₁ O) d A) ex s (K₀ * (K₀ - 1) * (K₀ - M)))
    (W : (ι ⊕ ι → K[X]) →ₗ[K] K) (σ : K) (v : Fin s → K)
    (hI : Doomed D O d (A - 1) (exHalves w ex) z v W σ (fun _ => True))
    (vG vF σ₀ σ₁ : K) (φm : Fin s → K) :
    (univ.filter (fun c : K × K =>
      ¬ Doomed D (foldWord c O) d A ex z (foldVal w z v φm c) (foldWeight W c)
        (foldClaim σ vG vF σ₀ σ₁ c) (fun _ => True))).card < K₀ := by
  refine lt_of_le_of_lt (card_le_card ?_)
    (fold_transition D O d A ex w hMq hMn hz W σ v (fun _ => True) hI vG vF σ₀ σ₁ φm)
  intro c hc
  refine mem_filter.mpr ⟨mem_univ _, fun hd => (mem_filter.mp hc).2 ?_⟩
  exact hd.mono (fun P _ => pull_true D O d A c P)

end Rounds
