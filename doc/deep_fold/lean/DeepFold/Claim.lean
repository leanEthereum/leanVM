/-
The DEEP fold round with its claims: Lemma 4.10(2) of the paper, for any finite set of candidates.

The weighted claim enters only through two `K`-linear functionals `W₀`, `W₁` on tuples, as the
paper remarks after Lemma 4.10. Characteristic two is used in one place, to turn the point
condition (p) into consistency with an answer vector.
-/
import DeepFold.Lanes

open Polynomial Finset
open scoped Classical

namespace DeepFold

variable {K : Type*} [Field K] [Fintype K]

/-- The zeros of the residual in the proof of Lemma 4.10(2) of the paper: a polynomial
`a + b α + c α^2 + β (d + e α)` in the challenge `(α, β)` whose constant term and coefficient of
`α` do not both vanish has at most `2 q` zeros in `K^2`. -/
theorem card_quadric_zeros_le (a b c d e : K) (hab : ¬ (a = 0 ∧ b = 0)) :
    (univ.filter (fun p : K × K =>
      a + b * p.1 + c * p.1 ^ 2 + p.2 * (d + e * p.1) = 0)).card ≤ 2 * Fintype.card K := by
  have hsum : (univ.filter (fun p : K × K =>
      a + b * p.1 + c * p.1 ^ 2 + p.2 * (d + e * p.1) = 0)).card =
      ∑ x : K, (univ.filter (fun y : K => a + b * x + c * x ^ 2 + y * (d + e * x) = 0)).card := by
    simp only [card_filter]
    rw [Fintype.sum_prod_type]
  rw [hsum]
  by_cases hde : d = 0 ∧ e = 0
  · obtain ⟨rfl, rfl⟩ := hde
    set P : K[X] := C a + C b * X + C c * X ^ 2 with hP
    have hPne : P ≠ 0 := by
      intro h0
      apply hab
      have h1 := congrArg (fun p : K[X] => p.coeff 0) h0
      have h2 := congrArg (fun p : K[X] => p.coeff 1) h0
      simp [hP] at h1 h2
      exact ⟨h1, h2⟩
    have hPdeg : P.natDegree ≤ 2 := by
      rw [hP]
      compute_degree
    have hroots := (card_roots_le hPne).trans hPdeg
    have hPeval : ∀ x : K, P.eval x = a + b * x + c * x ^ 2 := by
      intro x
      simp [hP]
    simp only [hPeval] at hroots
    calc ∑ x : K, (univ.filter (fun y : K =>
            a + b * x + c * x ^ 2 + y * (0 + 0 * x) = 0)).card
        ≤ ∑ x : K, (if a + b * x + c * x ^ 2 = 0 then Fintype.card K else 0) := by
          apply sum_le_sum
          intro x _
          by_cases hx : a + b * x + c * x ^ 2 = 0
          · simp only [hx, ite_true]
            exact card_le_univ _
          · simp [hx]
      _ = (univ.filter (fun x : K => a + b * x + c * x ^ 2 = 0)).card * Fintype.card K := by
          rw [← sum_filter, sum_const, smul_eq_mul]
      _ ≤ 2 * Fintype.card K := Nat.mul_le_mul_right _ hroots
  · have hone : (univ.filter (fun x : K => d + e * x = 0)).card ≤ 1 := by
      apply card_le_one.mpr
      intro x hx y hy
      have hx := (mem_filter.mp hx).2
      have hy := (mem_filter.mp hy).2
      have he : e ≠ 0 := by
        intro he
        apply hde
        rw [he, zero_mul, add_zero] at hx
        exact ⟨hx, he⟩
      have h1 : e * (x - y) = 0 := by linear_combination hx - hy
      exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left he)
    calc ∑ x : K, (univ.filter (fun y : K =>
            a + b * x + c * x ^ 2 + y * (d + e * x) = 0)).card
        ≤ ∑ x : K, (1 + (if d + e * x = 0 then Fintype.card K else 0)) := by
          apply sum_le_sum
          intro x _
          by_cases hx : d + e * x = 0
          · simp only [hx, ite_true]
            exact (card_le_univ _).trans (Nat.le_add_left _ _)
          · simp only [hx, ite_false, add_zero]
            apply card_le_one.mpr
            intro y hy y' hy'
            have hy := (mem_filter.mp hy).2
            have hy' := (mem_filter.mp hy').2
            have h1 : (y - y') * (d + e * x) = 0 := by linear_combination hy - hy'
            exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hx)
      _ = Fintype.card K +
            (univ.filter (fun x : K => d + e * x = 0)).card * Fintype.card K := by
          rw [sum_add_distrib, sum_const, card_univ, smul_eq_mul, mul_one, ← sum_filter,
            sum_const, smul_eq_mul]
      _ ≤ Fintype.card K + 1 * Fintype.card K :=
          Nat.add_le_add_left (Nat.mul_le_mul_right _ hone) _
      _ = 2 * Fintype.card K := by ring

variable {ι : Type*} [Fintype ι]

/-- The tuple `X F`. -/
noncomputable def mulX (F : ι → K[X]) : ι → K[X] := fun u => X * F u

/-- Lemma 4.10(2) of the paper for a finite set `T` of candidates and an answer vector, with lanes,
monomial lane weights and the predicate `B`.

Let `M ≥ max(2 q, C(n, 2))` and `z` outside the exceptional set of `T`. Fix an answer vector
`m = (y^F_i, y^G_i)`, a weighted claim given by two linear functionals `W₀`, `W₁` and a target
`σ`, and a predicate `B` on pairs of tuples. Suppose no pair `(F₀, G₀)` of polynomial tuples with
`deg F₀ < d`, `deg G₀ ≤ d`, agreement at least `A - 1` with `(O₀, O₁)`, satisfying `B` and
consistent with the answers satisfies the claim `⟨W₀, F₀⟩ + ⟨W₁, G₀⟩ = σ`. Then for every round
message `(v_G, v_F, σ₀, σ₁)` fewer than `K₀` challenges `c = (α, β)` admit a `P` with
`(c, P) ∈ T` that is consistent with the answers, satisfies the folded claim (w), and all of
whose near tuples satisfy `B`. -/
theorem deepFoldL_fold_round (D : Finset K) (O₀ O₁ : K → ι → K) {d A : ℕ} (ex : ι → ℕ)
    {T : Finset (CandL ι K)} (hTd : ∀ e ∈ T, ∀ u, (e.2 u).natDegree ≤ d)
    (hTA : ∀ e ∈ T, A ≤ (agrL D O₀ O₁ e).card)
    {s K₀ M : ℕ} (hMq : 2 * Fintype.card K ≤ M) (hMn : D.card.choose 2 ≤ M)
    {z : Fin s → K × K} (hz : z ∉ ExcL T ex s (K₀ * (K₀ - 1) * (K₀ - M)))
    (m : Fin s → K × K)
    (W₀ W₁ : (ι → K[X]) →ₗ[K] K) (σ : K) (B : (ι → K[X]) → (ι → K[X]) → Prop)
    (hyp : ∀ F₀ G₀ : ι → K[X], (∀ u, (F₀ u).degree < (d : WithBot ℕ)) →
      (∀ u, (G₀ u).natDegree ≤ d) → A ≤ (agrPairL D O₀ O₁ F₀ G₀).card + 1 → B F₀ G₀ →
      (∀ i, evL ex (z i) F₀ = (m i).1 ∧ evL ex (z i) G₀ = (m i).2) → W₀ F₀ + W₁ G₀ ≠ σ)
    (vG vF σ₀ σ₁ : K) :
    (univ.filter (fun c : K × K => ∃ P : ι → K[X], (c, P) ∈ T ∧
      (∀ i, ConsL ex (c, P) (z i) (m i).1 (m i).2) ∧
      ((1 + c.1) • W₀ + c.1 • W₁) P =
        vG + c.1 * (vG + σ) + c.1 ^ 2 * vF + c.2 * σ₀ + c.1 * c.2 * (σ₀ + σ₁) ∧
      (∀ F₀ G₀ : ι → K[X], (∀ u, (F₀ u).natDegree ≤ d) → (∀ u, (G₀ u).natDegree ≤ d) →
        (agrL D O₀ O₁ (c, P) \ agrPairL D O₀ O₁ F₀ G₀).card ≤ 1 → B F₀ G₀))).card < K₀ := by
  by_contra hlt
  set S := univ.filter (fun c : K × K => ∃ P : ι → K[X], (c, P) ∈ T ∧
      (∀ i, ConsL ex (c, P) (z i) (m i).1 (m i).2) ∧
      ((1 + c.1) • W₀ + c.1 • W₁) P =
        vG + c.1 * (vG + σ) + c.1 ^ 2 * vF + c.2 * σ₀ + c.1 * c.2 * (σ₀ + σ₁) ∧
      (∀ F₀ G₀ : ι → K[X], (∀ u, (F₀ u).natDegree ≤ d) → (∀ u, (G₀ u).natDegree ≤ d) →
        (agrL D O₀ O₁ (c, P) \ agrPairL D O₀ O₁ F₀ G₀).card ≤ 1 → B F₀ G₀)) with hSdef
  have hK : K₀ ≤ S.card := not_lt.mp hlt
  have hS : ∀ c ∈ S, ∃ P : ι → K[X], (c, P) ∈ T ∧
      (∀ i, ConsL ex (c, P) (z i) (m i).1 (m i).2) ∧
      ((1 + c.1) • W₀ + c.1 • W₁) P =
        vG + c.1 * (vG + σ) + c.1 ^ 2 * vF + c.2 * σ₀ + c.1 * c.2 * (σ₀ + σ₁) ∧
      (∀ F₀ G₀ : ι → K[X], (∀ u, (F₀ u).natDegree ≤ d) → (∀ u, (G₀ u).natDegree ≤ d) →
        (agrL D O₀ O₁ (c, P) \ agrPairL D O₀ O₁ F₀ G₀).card ≤ 1 → B F₀ G₀) :=
    fun c hc => (mem_filter.mp hc).2
  choose! Pc hPc using hS
  set W : Finset (CandL ι K) := S.image (fun c => (c, Pc c)) with hWdef
  have hWcard : W.card = S.card :=
    card_image_of_injective _ (fun c c' h => congrArg Prod.fst h)
  have hWmem : ∀ e ∈ W, e.1 ∈ S ∧ e = (e.1, Pc e.1) := by
    intro e he
    obtain ⟨c, hc, rfl⟩ := mem_image.mp he
    exact ⟨hc, rfl⟩
  have hWT : W ⊆ T := by
    intro e he
    obtain ⟨hc, heq⟩ := hWmem e he
    rw [heq]
    exact (hPc e.1 hc).1
  have hWc : ∀ e ∈ W, ∀ e' ∈ W, e.1 = e'.1 → e = e' := by
    intro e he e' he' h
    rw [(hWmem e he).2, (hWmem e' he').2, h]
  have hWcons : ∀ e ∈ W, ∀ i, ConsL ex e (z i) (m i).1 (m i).2 := by
    intro e he i
    obtain ⟨hc, heq⟩ := hWmem e he
    rw [heq]
    exact (hPc e.1 hc).2.1 i
  obtain ⟨F₀, G₀, hFd, hGd, hZ, hbig, ⟨e₀, he₀W, -, he₀near⟩, hans⟩ :=
    deepFoldL_theorem3 D O₀ O₁ ex hTd hTA (by omega : Fintype.card K ≤ M) hMn hz m hWT hWc
      hWcons (hWcard ▸ hK)
  have hFd' : ∀ u, (F₀ u).natDegree ≤ d := fun u =>
    natDegree_le_of_degree_le (le_of_lt (hFd u))
  have hB : B F₀ G₀ := by
    obtain ⟨hc, heq⟩ := hWmem e₀ he₀W
    rw [heq] at he₀near
    exact (hPc e₀.1 hc).2.2.2 F₀ G₀ hFd' hGd he₀near
  have hσ := hyp F₀ G₀ hFd hGd hZ hB hans
  set Cl := W.filter (fun e => ∀ u, e.2 u = G₀ u + aff e.1 * F₀ u) with hCl
  have hquad : ∀ e ∈ Cl,
      (W₀ G₀ - vG) + (W₀ G₀ + W₀ F₀ + W₁ G₀ - (vG + σ)) * e.1.1 +
        (W₀ F₀ + W₁ F₀ - vF) * e.1.1 ^ 2 +
        e.1.2 * ((W₀ (mulX F₀) - σ₀) +
          (W₀ (mulX F₀) + W₁ (mulX F₀) - (σ₀ + σ₁)) * e.1.1) = 0 := by
    intro e he
    obtain ⟨heW, heq⟩ := mem_filter.mp he
    obtain ⟨hc, hee⟩ := hWmem e heW
    have hw := (hPc e.1 hc).2.2.1
    have hP : Pc e.1 = G₀ + e.1.1 • F₀ + e.1.2 • mulX F₀ := by
      funext u
      have h1 : Pc e.1 u = e.2 u := by
        rw [hee]
      rw [h1, heq u]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_C_mul, aff, mulX]
      ring
    rw [hP] at hw
    simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, smul_eq_mul] at hw
    linear_combination hw
  have hClinj : ∀ e ∈ Cl, ∀ e' ∈ Cl, e.1 = e'.1 → e = e' := fun e he e' he' h =>
    hWc e (mem_filter.mp he).1 e' (mem_filter.mp he').1 h
  have hle : Cl.card ≤ 2 * Fintype.card K := by
    refine le_trans (card_le_card_of_injOn (fun e : CandL ι K => e.1) ?_ ?_)
      (card_quadric_zeros_le (W₀ G₀ - vG) (W₀ G₀ + W₀ F₀ + W₁ G₀ - (vG + σ))
        (W₀ F₀ + W₁ F₀ - vF) (W₀ (mulX F₀) - σ₀)
        (W₀ (mulX F₀) + W₁ (mulX F₀) - (σ₀ + σ₁)) (by
          rintro ⟨h1, h2⟩
          apply hσ
          linear_combination h2 - h1))
    · intro e he
      exact mem_coe.mpr (mem_filter.mpr ⟨mem_univ _, hquad e (mem_coe.mp he)⟩)
    · intro e he e' he' h
      exact hClinj e (mem_coe.mp he) e' (mem_coe.mp he') h
  omega

/-- Lemma 4.10(2) of the paper for a finite set `T` of candidates, in characteristic two.

`w` is the exponent `2^(j-1)` of the folded lane variable, so that
`ev^(j-1)_z(F₀, G₀) = θ^w ev_z(F₀) + ev_z(G₀)` by (E2). Let `M ≥ max(2 q, C(n, 2))` and `z`
outside the exceptional set of `T`. Suppose every pair of polynomial tuples `U = (F₀, G₀)` with
`deg F₀ < d`, `deg G₀ ≤ d`, agreement at least `A - 1` with `(O₀, O₁)`, satisfying `B` and the
carried point claims `ev^(j-1)_{z_i}(U) = v_i` has `⟨W₀, F₀⟩ + ⟨W₁, G₀⟩ ≠ σ`. Then for every
prover message `(v_G, v_F, σ₀, σ₁, φ_1, …, φ_s)` fewer than `K₀` challenges `c = (α, β)` admit a
`P` with `(c, P) ∈ T` and (p), (w), (b). -/
theorem deepFold_lemmaF [CharP K 2] (D : Finset K) (O₀ O₁ : K → ι → K) {d A : ℕ} (ex : ι → ℕ)
    (w : ℕ) {T : Finset (CandL ι K)} (hTd : ∀ e ∈ T, ∀ u, (e.2 u).natDegree ≤ d)
    (hTA : ∀ e ∈ T, A ≤ (agrL D O₀ O₁ e).card)
    {s K₀ M : ℕ} (hMq : 2 * Fintype.card K ≤ M) (hMn : D.card.choose 2 ≤ M)
    {z : Fin s → K × K} (hz : z ∉ ExcL T ex s (K₀ * (K₀ - 1) * (K₀ - M)))
    (W₀ W₁ : (ι → K[X]) →ₗ[K] K) (σ : K) (v : Fin s → K)
    (B : (ι → K[X]) → (ι → K[X]) → Prop)
    (hyp : ∀ F₀ G₀ : ι → K[X], (∀ u, (F₀ u).degree < (d : WithBot ℕ)) →
      (∀ u, (G₀ u).natDegree ≤ d) → A ≤ (agrPairL D O₀ O₁ F₀ G₀).card + 1 → B F₀ G₀ →
      (∀ i, (z i).1 ^ w * evL ex (z i) F₀ + evL ex (z i) G₀ = v i) → W₀ F₀ + W₁ G₀ ≠ σ)
    (vG vF σ₀ σ₁ : K) (φm : Fin s → K) :
    (univ.filter (fun c : K × K => ∃ P : ι → K[X], (c, P) ∈ T ∧
      (∀ i, evL ex (z i) P = v i + ((z i).1 ^ w + c.1 + c.2 * (z i).2) * φm i) ∧
      ((1 + c.1) • W₀ + c.1 • W₁) P =
        vG + c.1 * (vG + σ) + c.1 ^ 2 * vF + c.2 * σ₀ + c.1 * c.2 * (σ₀ + σ₁) ∧
      (∀ F₀ G₀ : ι → K[X], (∀ u, (F₀ u).natDegree ≤ d) → (∀ u, (G₀ u).natDegree ≤ d) →
        (agrL D O₀ O₁ (c, P) \ agrPairL D O₀ O₁ F₀ G₀).card ≤ 1 → B F₀ G₀))).card < K₀ := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have key := deepFoldL_fold_round D O₀ O₁ ex hTd hTA hMq hMn hz
    (fun i => (φm i, v i + (z i).1 ^ w * φm i)) W₀ W₁ σ B (by
      intro F₀ G₀ h1 h3 h4 h5 h6
      refine hyp F₀ G₀ h1 h3 h4 h5 (fun i => ?_)
      have hF : evL ex (z i) F₀ = φm i := (h6 i).1
      have hG : evL ex (z i) G₀ = v i + (z i).1 ^ w * φm i := (h6 i).2
      rw [hF, hG]
      linear_combination ((z i).1 ^ w * φm i) * h2) vG vF σ₀ σ₁
  refine lt_of_le_of_lt (card_le_card ?_) key
  intro c hc
  obtain ⟨P, hP, hp, hw, hb⟩ := (mem_filter.mp hc).2
  refine mem_filter.mpr ⟨mem_univ _, P, hP, fun i => ?_, hw, hb⟩
  show evL ex (z i) P = (v i + (z i).1 ^ w * φm i) + (c.1 + c.2 * (z i).2) * φm i
  rw [hp i]
  ring

end DeepFold
