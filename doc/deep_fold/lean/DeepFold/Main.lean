/-
The end statements, for the set `𝒯` of all candidates, in the form of the paper.

`lemmaF_exc` is Lemma 4.10(1) of the paper and `lemmaF_round` is Lemma 4.10(2); `lemmaD4_exc` and
`lemmaD4_round` are the same with the threshold `⌈K₀^3 / 4⌉` in place of `K₀ (K₀ - 1) (K₀ - M)`.
-/
import DeepFold.Theorem
import DeepFold.Claim
import DeepFold.Full

open Polynomial Finset
open scoped Classical

namespace DeepFold

variable {K : Type*} [Field K] [Fintype K] {ι : Type*} [Fintype ι]

/-- Lemma 4.10(1) of the paper. `Λ` bounds the list of every fold, `ex` is injective with values
at most `E`, and `ε = (d + 1 + E) / q`. The exceptional set of `𝒯` with threshold `B` has density
at most `Λ^3 q^6 ε^s / B` among the vectors of `s` points of `K^2`. In the paper `Λ` is `L`,
`B = Θ = K₀ (K₀ - 1) (K₀ - M)` and `E = 2^ℓ - 2^j`. -/
theorem lemmaF_exc (D : Finset K) (O₀ O₁ : K → ι → K) (d A : ℕ) {ex : ι → ℕ}
    (hex : Function.Injective ex) {E : ℕ} (hE : ∀ u, ex u ≤ E) (Λ : ℕ)
    (hΛ : ∀ c : K × K, ((fullT D O₀ O₁ d A).filter (fun e => e.1 = c)).card ≤ Λ)
    (s : ℕ) {B : ℕ} (hB : 0 < B) :
    ((ExcL (fullT D O₀ O₁ d A) ex s B).card : ℚ) / (Fintype.card (Fin s → K × K) : ℚ) ≤
      (Λ : ℚ) ^ 3 * (Fintype.card K : ℚ) ^ 6 *
        (((d + 1 + E : ℕ) : ℚ) / Fintype.card K) ^ s / B := by
  have h1 := density_ExcL_le hex hE (fullT_natDegree_le D O₀ O₁ d A) s hB
  have h2 : ((fullT D O₀ O₁ d A).card : ℚ) ≤ (Λ : ℚ) * (Fintype.card K : ℚ) ^ 2 := by
    exact_mod_cast card_T_le (fullT D O₀ O₁ d A) (fun e => e.1) Λ hΛ
  have h3 : ((fullT D O₀ O₁ d A).card : ℚ) ^ 3 ≤ (Λ : ℚ) ^ 3 * (Fintype.card K : ℚ) ^ 6 := by
    calc ((fullT D O₀ O₁ d A).card : ℚ) ^ 3 ≤ ((Λ : ℚ) * (Fintype.card K : ℚ) ^ 2) ^ 3 :=
          pow_le_pow_left₀ (by positivity) h2 3
      _ = (Λ : ℚ) ^ 3 * (Fintype.card K : ℚ) ^ 6 := by ring
  refine h1.trans ?_
  gcongr

/-- Lemma 4.10(2) of the paper, for the set `𝒯` of all candidates, in characteristic two.

Setting: domain `D` of size `n`, halves `O₀, O₁` of an interleaved word, lanes `ι`, degree bound
`d`, agreement `A`, lane exponents `ex`, `w` the exponent `2^(j-1)` of the folded lane variable,
`M ≥ max(2 q, C(n, 2))`, and `z` outside `Exc` with threshold `K₀ (K₀ - 1) (K₀ - M)`.

Hypothesis: every pair of polynomial tuples `U = (F₀, G₀)` with `deg F₀ < d`, `deg G₀ ≤ d`,
agreeing with `(O₀, O₁)` on at least `A - 1` columns, with `B(U)` and
`θ_i^w ev_{z_i}(F₀) + ev_{z_i}(G₀) = v_i` for all `i`, has `⟨W₀, F₀⟩ + ⟨W₁, G₀⟩ ≠ σ`.

Conclusion: for every prover message `(v_G, v_F, σ₀, σ₁, φ)`, fewer than `K₀` challenges
`c = (α, β)` admit a tuple `P` of degree at most `d`, agreeing with `O₁ + a_c O₀` on at least `A`
columns, with (p), (w) and (b). -/
theorem lemmaF_round [CharP K 2] (D : Finset K) (O₀ O₁ : K → ι → K) (d A : ℕ) (ex : ι → ℕ)
    (w : ℕ) {s K₀ M : ℕ} (hMq : 2 * Fintype.card K ≤ M) (hMn : D.card.choose 2 ≤ M)
    {z : Fin s → K × K}
    (hz : z ∉ ExcL (fullT D O₀ O₁ d A) ex s (K₀ * (K₀ - 1) * (K₀ - M)))
    (W₀ W₁ : (ι → K[X]) →ₗ[K] K) (σ : K) (v : Fin s → K)
    (B : (ι → K[X]) → (ι → K[X]) → Prop)
    (hyp : ∀ F₀ G₀ : ι → K[X], (∀ u, (F₀ u).degree < (d : WithBot ℕ)) →
      (∀ u, (G₀ u).natDegree ≤ d) → A ≤ (agrPairL D O₀ O₁ F₀ G₀).card + 1 → B F₀ G₀ →
      (∀ i, (z i).1 ^ w * evL ex (z i) F₀ + evL ex (z i) G₀ = v i) → W₀ F₀ + W₁ G₀ ≠ σ)
    (vG vF σ₀ σ₁ : K) (φm : Fin s → K) :
    (univ.filter (fun c : K × K => ∃ P : ι → K[X],
      (∀ u, (P u).natDegree ≤ d) ∧ A ≤ (agrL D O₀ O₁ (c, P)).card ∧
      (∀ i, evL ex (z i) P = v i + ((z i).1 ^ w + c.1 + c.2 * (z i).2) * φm i) ∧
      ((1 + c.1) • W₀ + c.1 • W₁) P =
        vG + c.1 * (vG + σ) + c.1 ^ 2 * vF + c.2 * σ₀ + c.1 * c.2 * (σ₀ + σ₁) ∧
      (∀ F₀ G₀ : ι → K[X], (∀ u, (F₀ u).natDegree ≤ d) → (∀ u, (G₀ u).natDegree ≤ d) →
        (agrL D O₀ O₁ (c, P) \ agrPairL D O₀ O₁ F₀ G₀).card ≤ 1 → B F₀ G₀))).card < K₀ := by
  have key := deepFold_lemmaF D O₀ O₁ ex w (fullT_natDegree_le D O₀ O₁ d A)
    (fullT_agr D O₀ O₁ d A) hMq hMn hz W₀ W₁ σ v B hyp vG vF σ₀ σ₁ φm
  refine lt_of_le_of_lt (card_le_card ?_) key
  intro c hc
  obtain ⟨P, h1, h2, h3⟩ := (mem_filter.mp hc).2
  exact mem_filter.mpr ⟨mem_univ _, P, mem_fullT.mpr ⟨h1, h2⟩, h3⟩

/-- Lemma 4.10(1) of the paper with the threshold `⌈K₀^3 / 4⌉`: the exceptional set has density at
most `4 Λ^3 q^6 ε^s / K₀^3`. -/
theorem lemmaD4_exc (D : Finset K) (O₀ O₁ : K → ι → K) (d A : ℕ) {ex : ι → ℕ}
    (hex : Function.Injective ex) {E : ℕ} (hE : ∀ u, ex u ≤ E) (Λ : ℕ)
    (hΛ : ∀ c : K × K, ((fullT D O₀ O₁ d A).filter (fun e => e.1 = c)).card ≤ Λ)
    (s : ℕ) {K₀ : ℕ} (hK : 0 < K₀) :
    ((ExcL (fullT D O₀ O₁ d A) ex s ((K₀ ^ 3 + 3) / 4)).card : ℚ) /
        (Fintype.card (Fin s → K × K) : ℚ) ≤
      4 * (Λ : ℚ) ^ 3 * (Fintype.card K : ℚ) ^ 6 *
        (((d + 1 + E : ℕ) : ℚ) / Fintype.card K) ^ s / (K₀ : ℚ) ^ 3 := by
  have hpos : 0 < K₀ ^ 3 := pow_pos hK 3
  have hB : 0 < (K₀ ^ 3 + 3) / 4 := by omega
  have h1 := lemmaF_exc D O₀ O₁ d A hex hE Λ hΛ s hB
  have h2 : (K₀ : ℚ) ^ 3 ≤ 4 * (((K₀ ^ 3 + 3) / 4 : ℕ) : ℚ) := by
    have h3 : K₀ ^ 3 ≤ 4 * ((K₀ ^ 3 + 3) / 4) := by omega
    exact_mod_cast h3
  have hB' : (0 : ℚ) < (((K₀ ^ 3 + 3) / 4 : ℕ) : ℚ) := by exact_mod_cast hB
  have hK' : (0 : ℚ) < (K₀ : ℚ) ^ 3 := by positivity
  refine h1.trans ?_
  rw [div_le_div_iff₀ hB' hK']
  have hnn : (0 : ℚ) ≤ (Λ : ℚ) ^ 3 * (Fintype.card K : ℚ) ^ 6 *
      (((d + 1 + E : ℕ) : ℚ) / Fintype.card K) ^ s := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 hnn]

/-- Lemma 4.10(2) of the paper with the threshold `⌈K₀^3 / 4⌉`: the conclusion of `lemmaF_round` for
`z` outside the exceptional set with threshold `⌈K₀^3 / 4⌉`, when `K₀ ≥ 26` and
`0.74 K₀ ≥ M ≥ max(2 q, C(n, 2))`. -/
theorem lemmaD4_round [CharP K 2] (D : Finset K) (O₀ O₁ : K → ι → K) (d A : ℕ) (ex : ι → ℕ)
    (w : ℕ) {s K₀ M : ℕ} (hK : 26 ≤ K₀) (hMK : 100 * M ≤ 74 * K₀)
    (hMq : 2 * Fintype.card K ≤ M) (hMn : D.card.choose 2 ≤ M)
    {z : Fin s → K × K} (hz : z ∉ ExcL (fullT D O₀ O₁ d A) ex s ((K₀ ^ 3 + 3) / 4))
    (W₀ W₁ : (ι → K[X]) →ₗ[K] K) (σ : K) (v : Fin s → K)
    (B : (ι → K[X]) → (ι → K[X]) → Prop)
    (hyp : ∀ F₀ G₀ : ι → K[X], (∀ u, (F₀ u).degree < (d : WithBot ℕ)) →
      (∀ u, (G₀ u).natDegree ≤ d) → A ≤ (agrPairL D O₀ O₁ F₀ G₀).card + 1 → B F₀ G₀ →
      (∀ i, (z i).1 ^ w * evL ex (z i) F₀ + evL ex (z i) G₀ = v i) → W₀ F₀ + W₁ G₀ ≠ σ)
    (vG vF σ₀ σ₁ : K) (φm : Fin s → K) :
    (univ.filter (fun c : K × K => ∃ P : ι → K[X],
      (∀ u, (P u).natDegree ≤ d) ∧ A ≤ (agrL D O₀ O₁ (c, P)).card ∧
      (∀ i, evL ex (z i) P = v i + ((z i).1 ^ w + c.1 + c.2 * (z i).2) * φm i) ∧
      ((1 + c.1) • W₀ + c.1 • W₁) P =
        vG + c.1 * (vG + σ) + c.1 ^ 2 * vF + c.2 * σ₀ + c.1 * c.2 * (σ₀ + σ₁) ∧
      (∀ F₀ G₀ : ι → K[X], (∀ u, (F₀ u).natDegree ≤ d) → (∀ u, (G₀ u).natDegree ≤ d) →
        (agrL D O₀ O₁ (c, P) \ agrPairL D O₀ O₁ F₀ G₀).card ≤ 1 → B F₀ G₀))).card < K₀ := by
  have h1 := quarter_cube_le hK hMK
  have h2 : (K₀ ^ 3 + 3) / 4 ≤ K₀ * (K₀ - 1) * (K₀ - M) := by
    generalize K₀ * (K₀ - 1) * (K₀ - M) = x at h1
    generalize K₀ ^ 3 = y at h1
    omega
  exact lemmaF_round D O₀ O₁ d A ex w hMq hMn (not_mem_Exc_of_le _ _ _ h2 hz) W₀ W₁ σ v B hyp
    vG vF σ₀ σ₁ φm

end DeepFold
