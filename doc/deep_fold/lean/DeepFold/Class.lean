/-
Classes: the candidates that are folds of one rational pair (Definition 4.5 of the paper), with
Lemma 4.6(a), (b) and the trichotomy of Lemma 4.7 in the form the fold round uses, for one lane.
-/
import DeepFold.Basic

open Polynomial

namespace DeepFold

variable {K : Type*} [Field K]

local notation "φ" => algebraMap K[X] (RatFunc K)

/-- `(c, P)` is the fold of the rational pair `(F, G)`: `P = G + a_c F` in `K(X)`. -/
def IsFold (F G : RatFunc K) (e : Cand K) : Prop := φ e.2 = G + φ (aff e.1) * F

/-- The rational `F = (P₂ - P₁) / (a₂ - a₁)` of two candidates. -/
noncomputable def pairF (e₁ e₂ : Cand K) : RatFunc K :=
  φ (e₂.2 - e₁.2) / φ (aff e₂.1 - aff e₁.1)

/-- The rational `G = P₁ - a₁ F` of two candidates. -/
noncomputable def pairG (e₁ e₂ : Cand K) : RatFunc K := φ e₁.2 - φ (aff e₁.1) * pairF e₁ e₂

theorem phi_injective : Function.Injective φ := IsFractionRing.injective K[X] (RatFunc K)

theorem phi_aff_sub_ne_zero {e₁ e₂ : Cand K} (h : e₁.1 ≠ e₂.1) :
    φ (aff e₂.1 - aff e₁.1) ≠ 0 := by
  intro h0
  have h1 := phi_injective (h0.trans (map_zero φ).symm)
  exact h (aff_injective (sub_eq_zero.mp h1)).symm

theorem pairF_spec {e₁ e₂ : Cand K} (h : e₁.1 ≠ e₂.1) :
    φ (aff e₂.1 - aff e₁.1) * pairF e₁ e₂ = φ (e₂.2 - e₁.2) := by
  have hL := phi_aff_sub_ne_zero h
  unfold pairF
  field_simp

theorem isFold_pair_left (e₁ e₂ : Cand K) : IsFold (pairF e₁ e₂) (pairG e₁ e₂) e₁ := by
  simp [IsFold, pairG]

theorem isFold_pair_right {e₁ e₂ : Cand K} (h : e₁.1 ≠ e₂.1) :
    IsFold (pairF e₁ e₂) (pairG e₁ e₂) e₂ := by
  have hF := pairF_spec h
  simp only [IsFold, pairG, map_sub] at hF ⊢
  linear_combination -hF

/-- Lemma 4.6(a) of the paper, uniqueness: two candidates with different challenges are folds of
at most one rational pair. -/
theorem isFold_unique {F G : RatFunc K} {e₁ e₂ : Cand K} (h : e₁.1 ≠ e₂.1)
    (h₁ : IsFold F G e₁) (h₂ : IsFold F G e₂) : F = pairF e₁ e₂ ∧ G = pairG e₁ e₂ := by
  have hL := phi_aff_sub_ne_zero h
  have hF : F = pairF e₁ e₂ := by
    unfold pairF
    rw [eq_div_iff hL]
    unfold IsFold at h₁ h₂
    simp only [map_sub]
    linear_combination h₁ - h₂
  subst hF
  refine ⟨rfl, ?_⟩
  unfold pairG
  unfold IsFold at h₁
  linear_combination -h₁

/-- The identity behind Lemma 4.6(b) of the paper: `Delta = (a₂ - a₁) (P₃ - (G + a₃ F))` for the
pair of the first two candidates. -/
theorem map_Delta {e₁ e₂ : Cand K} (h : e₁.1 ≠ e₂.1) (e₃ : Cand K) :
    φ (Delta e₁ e₂ e₃) =
      φ (aff e₂.1 - aff e₁.1) * (φ e₃.2 - (pairG e₁ e₂ + φ (aff e₃.1) * pairF e₁ e₂)) := by
  have hF := pairF_spec h
  simp only [Delta, pairG, map_add, map_mul, map_sub] at hF ⊢
  linear_combination (φ (aff e₃.1) - φ (aff e₁.1)) * hF

/-- Lemma 4.6(b) of the paper: for `c₁ ≠ c₂`, `Delta = 0` exactly when the third candidate is a
fold of the rational pair of the first two. No hypothesis on `c₃`. -/
theorem Delta_eq_zero_iff {e₁ e₂ : Cand K} (h : e₁.1 ≠ e₂.1) (e₃ : Cand K) :
    Delta e₁ e₂ e₃ = 0 ↔ IsFold (pairF e₁ e₂) (pairG e₁ e₂) e₃ := by
  rw [← (phi_injective (K := K)).eq_iff, map_zero, map_Delta h, mul_eq_zero,
    or_iff_right (phi_aff_sub_ne_zero h), sub_eq_zero]
  rfl

/-- `Delta = 0` exactly when the three candidates are folds of one common rational pair. -/
theorem Delta_eq_zero_iff_exists {e₁ e₂ : Cand K} (h : e₁.1 ≠ e₂.1) (e₃ : Cand K) :
    Delta e₁ e₂ e₃ = 0 ↔ ∃ F G : RatFunc K, IsFold F G e₁ ∧ IsFold F G e₂ ∧ IsFold F G e₃ := by
  constructor
  · intro h0
    exact ⟨_, _, isFold_pair_left e₁ e₂, isFold_pair_right h, (Delta_eq_zero_iff h e₃).mp h0⟩
  · rintro ⟨F, G, h₁, h₂, h₃⟩
    obtain ⟨rfl, rfl⟩ := isFold_unique h h₁ h₂
    exact (Delta_eq_zero_iff h e₃).mpr h₃

/-- A class has at most one element per challenge. -/
theorem isFold_ext {F G : RatFunc K} {e e' : Cand K} (he : IsFold F G e) (he' : IsFold F G e')
    (h : e.1 = e'.1) : e = e' := by
  refine Prod.ext h (phi_injective ?_)
  unfold IsFold at he he'
  rw [he, he', h]

/-- The pole of the rational pair of two candidates with different `β`: the root of
`a_c - a_c'`. -/
noncomputable def pole (c c' : K × K) : K := (c'.1 - c.1) / (c.2 - c'.2)

/-- The core of Lemma 4.7 of the paper, for two anchors with different `β` in the class of `(F, G)`:
either `F`, `G` are polynomials of degrees below `d` and at most `d`, or every element of the class
has its challenge on the line `α + x₀ β = α_e + x₀ β_e` through the pole `x₀`. -/
theorem fold_anchor_dichotomy {F G : RatFunc K} {e e' : Cand K} {d : ℕ}
    (hβ : e.1.2 ≠ e'.1.2) (he : IsFold F G e) (he' : IsFold F G e')
    (hd : e.2.natDegree ≤ d) (hd' : e'.2.natDegree ≤ d) :
    (∃ F₀ G₀ : K[X], F = φ F₀ ∧ G = φ G₀ ∧ F₀.degree < (d : WithBot ℕ) ∧ G₀.natDegree ≤ d) ∨
    (∀ e'' : Cand K, IsFold F G e'' →
      e''.1.1 + pole e.1 e'.1 * e''.1.2 = e.1.1 + pole e.1 e'.1 * e.1.2) := by
  set x₀ := pole e.1 e'.1 with hx₀
  set b := e.1.2 - e'.1.2 with hb
  have hb0 : b ≠ 0 := sub_ne_zero.mpr hβ
  set L := aff e.1 - aff e'.1 with hL
  set N := e.2 - e'.2 with hN
  have hbx : b * x₀ = e'.1.1 - e.1.1 := by
    rw [hx₀, pole, ← hb]
    field_simp
  have hLx : L = C b * (X - C x₀) := by
    rw [hL, aff_sub, mul_sub, ← C_mul, hbx, hb]
    simp only [C_sub]
    ring
  have hLne : L ≠ 0 := by
    rw [hLx]
    exact mul_ne_zero (C_ne_zero.mpr hb0) (X_sub_C_ne_zero x₀)
  have hLdeg : L.natDegree = 1 := by
    rw [hLx, natDegree_C_mul hb0, natDegree_X_sub_C]
  have hLx0 : L.eval x₀ = 0 := by
    rw [hLx]
    simp
  have hFN : φ L * F = φ N := by
    unfold IsFold at he he'
    rw [hL, hN]
    simp only [map_sub]
    linear_combination he' - he
  by_cases hroot : N.eval x₀ = 0
  · left
    obtain ⟨F₁, hF₁⟩ := dvd_iff_isRoot.mpr hroot
    have hLF : L * (C b⁻¹ * F₁) = N := by
      calc L * (C b⁻¹ * F₁) = (C b * C b⁻¹) * ((X - C x₀) * F₁) := by
            rw [hLx]
            ring
        _ = N := by rw [← C_mul, mul_inv_cancel₀ hb0, C_1, one_mul, hF₁]
    set F₀ := C b⁻¹ * F₁ with hF₀
    have hφL : φ L ≠ 0 := fun h0 => hLne (phi_injective (h0.trans (map_zero φ).symm))
    have hF : F = φ F₀ := by
      have h1 : φ L * F = φ L * φ F₀ := by rw [hFN, ← map_mul, hLF]
      exact mul_left_cancel₀ hφL h1
    have hG : G = φ (e.2 - aff e.1 * F₀) := by
      unfold IsFold at he
      rw [map_sub, map_mul, ← hF]
      linear_combination -he
    have hNd : N.natDegree ≤ d := (natDegree_sub_le_of_le hd hd').trans (le_of_eq (max_self d))
    have hF₀deg : F₀ ≠ 0 → F₀.natDegree + 1 ≤ d := by
      intro h0
      have h1 : (L * F₀).natDegree = L.natDegree + F₀.natDegree := natDegree_mul hLne h0
      rw [hLF, hLdeg] at h1
      omega
    refine ⟨F₀, e.2 - aff e.1 * F₀, hF, hG, ?_, ?_⟩
    · by_cases h0 : F₀ = 0
      · rw [h0, degree_zero]
        exact WithBot.bot_lt_coe d
      · rw [degree_eq_natDegree h0]
        have h1 := hF₀deg h0
        exact_mod_cast (by omega : F₀.natDegree < d)
    · by_cases h0 : F₀ = 0
      · simpa [h0] using hd
      · have h1 := hF₀deg h0
        have h2 : (aff e.1 * F₀).natDegree ≤ d := by
          calc (aff e.1 * F₀).natDegree ≤ 1 + F₀.natDegree :=
                natDegree_mul_le_of_le (aff_natDegree_le _) le_rfl
            _ ≤ d := by omega
        exact (natDegree_sub_le_of_le hd h2).trans (le_of_eq (max_self d))
  · right
    intro e'' he''
    have h1 : φ ((e''.2 - e.2) * L) = φ ((aff e''.1 - aff e.1) * N) := by
      unfold IsFold at he he''
      simp only [map_mul, map_sub]
      rw [← hFN]
      linear_combination (φ L) * (he'' - he)
    have h2 := phi_injective h1
    have h3 := congrArg (eval x₀) h2
    simp only [eval_mul, eval_sub, hLx0, mul_zero, aff_eval] at h3
    have h4 := (mul_eq_zero.mp h3.symm).resolve_right hroot
    linear_combination h4

/-- Lemma 4.7 of the paper as a trichotomy for any set of folds of one rational pair
with polynomials of degree at most `d`: a polynomial pair of degrees `(< d, ≤ d)`, or all
challenges on one line `α + x₀ β = γ`, or all challenges with the same `β`. -/
theorem class_trichotomy {F G : RatFunc K} {S : Set (Cand K)} {d : ℕ}
    (hS : ∀ e ∈ S, IsFold F G e ∧ e.2.natDegree ≤ d) :
    (∃ F₀ G₀ : K[X], F = φ F₀ ∧ G = φ G₀ ∧ F₀.degree < (d : WithBot ℕ) ∧ G₀.natDegree ≤ d) ∨
    (∃ x₀ γ : K, ∀ e ∈ S, e.1.1 + x₀ * e.1.2 = γ) ∨ (∃ β₀ : K, ∀ e ∈ S, e.1.2 = β₀) := by
  by_cases h : ∃ e ∈ S, ∃ e' ∈ S, e.1.2 ≠ e'.1.2
  · obtain ⟨e, he, e', he', hβ⟩ := h
    rcases fold_anchor_dichotomy hβ (hS e he).1 (hS e' he').1 (hS e he).2 (hS e' he').2 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨_, _, fun e'' he'' => h e'' (hS e'' he'').1⟩)
  · push Not at h
    right
    right
    rcases S.eq_empty_or_nonempty with h0 | ⟨e, he⟩
    · exact ⟨0, fun e he => by simp [h0] at he⟩
    · exact ⟨e.1.2, fun e' he' => (h e he e' he').symm⟩

section Finite

variable [Fintype K]

/-- A set of elements with distinct challenges `ch e = (α, β)` on one line `α + x₀ β = γ` has at
most `q` elements. -/
theorem card_le_of_line {α : Type*} {W : Finset α} {ch : α → K × K}
    (hinj : ∀ e ∈ W, ∀ e' ∈ W, ch e = ch e' → e = e') {x₀ γ : K}
    (h : ∀ e ∈ W, (ch e).1 + x₀ * (ch e).2 = γ) : W.card ≤ Fintype.card K := by
  classical
  rw [← Finset.card_univ]
  refine Finset.card_le_card_of_injOn (fun e => (ch e).2) (by intro e _; simp) ?_
  intro e he e' he' hee
  have he := Finset.mem_coe.mp he
  have he' := Finset.mem_coe.mp he'
  have hee : (ch e).2 = (ch e').2 := hee
  have h1 := (h e he).trans (h e' he').symm
  refine hinj e he e' he' (Prod.ext ?_ hee)
  linear_combination h1 - x₀ * hee

omit [Field K] in
/-- A set of elements with distinct challenges that share `β` has at most `q` elements. -/
theorem card_le_of_snd_const {α : Type*} {W : Finset α} {ch : α → K × K}
    (hinj : ∀ e ∈ W, ∀ e' ∈ W, ch e = ch e' → e = e') {β₀ : K}
    (h : ∀ e ∈ W, (ch e).2 = β₀) : W.card ≤ Fintype.card K := by
  classical
  rw [← Finset.card_univ]
  refine Finset.card_le_card_of_injOn (fun e => (ch e).1) (by intro e _; simp) ?_
  intro e he e' he' hee
  have he := Finset.mem_coe.mp he
  have he' := Finset.mem_coe.mp he'
  have hee : (ch e).1 = (ch e').1 := hee
  exact hinj e he e' he' (Prod.ext hee ((h e he).trans (h e' he').symm))

/-- The consequence of Lemma 4.7(a), (b) of the paper that the fold round uses: a class with more
than `q` elements is the class of a polynomial pair with `deg F < d` and `deg G ≤ d`. -/
theorem class_poly_of_card_gt {F G : RatFunc K} {W : Finset (Cand K)} {d : ℕ}
    (hW : ∀ e ∈ W, IsFold F G e ∧ e.2.natDegree ≤ d) (hq : Fintype.card K < W.card) :
    ∃ F₀ G₀ : K[X], F = φ F₀ ∧ G = φ G₀ ∧ F₀.degree < (d : WithBot ℕ) ∧ G₀.natDegree ≤ d := by
  have hinj : ∀ e ∈ W, ∀ e' ∈ W, e.1 = e'.1 → e = e' := fun e he e' he' h =>
    isFold_ext (hW e he).1 (hW e' he').1 h
  rcases class_trichotomy (S := (W : Set (Cand K)))
    (fun e he => hW e (Finset.mem_coe.mp he)) with h | ⟨x₀, γ, h⟩ | ⟨β₀, h⟩
  · exact h
  · exact absurd (card_le_of_line (ch := fun e : Cand K => e.1) hinj
      (fun e he => h e (Finset.mem_coe.mpr he))) (not_le.mpr hq)
  · exact absurd (card_le_of_snd_const (ch := fun e : Cand K => e.1) hinj
      (fun e he => h e (Finset.mem_coe.mpr he))) (not_le.mpr hq)

end Finite

end DeepFold
