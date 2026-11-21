/-
A class of a polynomial pair that does not agree with the committed pair of words is small:
Lemma 4.7(c) of the paper, for one lane.
-/
import DeepFold.Basic

open Polynomial Finset
open scoped Classical

namespace DeepFold

variable {K : Type*} [Field K]

/-- The counting step of Lemma 4.7(c) of the paper, with no polynomials. `S` is a set of elements
with pairwise different challenges `ch e = (α, β)`, `Agr e` is the agreement set of `e`, and on a
column `x` of `R` (the columns outside `𝒜_{F,G}`) all elements that agree there have the same
scalar `α + β x`. Then at most `C(|R|, 2)` elements have two agreement columns in `R`: two columns
determine the challenge. -/
theorem card_two_points_le {α : Type*} (S : Finset α) (ch : α → K × K)
    (hch : ∀ e ∈ S, ∀ e' ∈ S, ch e = ch e' → e = e')
    (R : Finset K) (Agr : α → Finset K)
    (hg : ∀ e ∈ S, ∀ e' ∈ S, ∀ x ∈ R, x ∈ Agr e → x ∈ Agr e' →
      (ch e).1 + (ch e).2 * x = (ch e').1 + (ch e').2 * x) :
    (S.filter (fun e => 2 ≤ (Agr e ∩ R).card)).card ≤ R.card.choose 2 := by
  have hex : ∀ e, 2 ≤ (Agr e ∩ R).card → ∃ t ⊆ Agr e ∩ R, t.card = 2 := fun e h =>
    exists_subset_card_eq h
  let τ : α → Finset K := fun e =>
    if h : 2 ≤ (Agr e ∩ R).card then (hex e h).choose else ∅
  have hτ : ∀ e, 2 ≤ (Agr e ∩ R).card → τ e ⊆ Agr e ∩ R ∧ (τ e).card = 2 := by
    intro e h
    simp only [τ, h, ↓reduceDIte]
    exact (hex e h).choose_spec
  rw [← card_powersetCard]
  refine card_le_card_of_injOn τ ?_ ?_
  · intro e he
    have h2 := (mem_filter.mp (mem_coe.mp he)).2
    exact mem_coe.mpr (mem_powersetCard.mpr
      ⟨(hτ e h2).1.trans inter_subset_right, (hτ e h2).2⟩)
  · intro e he e' he' hee
    obtain ⟨heS, h2⟩ := mem_filter.mp (mem_coe.mp he)
    obtain ⟨heS', h2'⟩ := mem_filter.mp (mem_coe.mp he')
    obtain ⟨x, y, hxy, hxyeq⟩ := card_eq_two.mp (hτ e h2).2
    have hx : x ∈ τ e := by rw [hxyeq]; simp
    have hy : y ∈ τ e := by rw [hxyeq]; simp
    have hx' : x ∈ τ e' := hee ▸ hx
    have hy' : y ∈ τ e' := hee ▸ hy
    have mx := mem_inter.mp ((hτ e h2).1 hx)
    have my := mem_inter.mp ((hτ e h2).1 hy)
    have mx' := mem_inter.mp ((hτ e' h2').1 hx')
    have my' := mem_inter.mp ((hτ e' h2').1 hy')
    have e1 := hg e heS e' heS' x mx.2 mx.1 mx'.1
    have e2 := hg e heS e' heS' y my.2 my.1 my'.1
    apply hch e heS e' heS'
    have hsub : ((ch e).2 - (ch e').2) * (x - y) = 0 := by
      linear_combination e1 - e2
    have hβ : (ch e).2 = (ch e').2 :=
      sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_right (sub_ne_zero.mpr hxy))
    refine Prod.ext ?_ hβ
    linear_combination e1 - x * hβ

/-- The agreement set of a candidate `(c, P)` with the fold `f₁ + a_c f₀` of the words. -/
noncomputable def agr (D : Finset K) (f₀ f₁ : K → K) (e : Cand K) : Finset K :=
  D.filter (fun x => e.2.eval x = f₁ x + (e.1.1 + e.1.2 * x) * f₀ x)

/-- `𝒜_{F,G}` of Lemma 4.7(c) of the paper: the columns where the polynomial pair `(F₀, G₀)`
agrees with the pair of words. -/
noncomputable def agrPair (D : Finset K) (f₀ f₁ : K → K) (F₀ G₀ : K[X]) : Finset K :=
  D.filter (fun x => F₀.eval x = f₀ x ∧ G₀.eval x = f₁ x)

/-- Lemma 4.7(c) of the paper, the count: in the class of a polynomial pair, at most
`C(n - |𝒜_{F,G}|, 2)` elements have two or more agreement columns outside `𝒜_{F,G}`. -/
theorem card_agr_outside_le (D : Finset K) (f₀ f₁ : K → K) (F₀ G₀ : K[X]) (W : Finset (Cand K))
    (hW : ∀ e ∈ W, e.2 = G₀ + aff e.1 * F₀) :
    (W.filter (fun e => 2 ≤ (agr D f₀ f₁ e \ agrPair D f₀ f₁ F₀ G₀).card)).card ≤
      (D.card - (agrPair D f₀ f₁ F₀ G₀).card).choose 2 := by
  have hZD : agrPair D f₀ f₁ F₀ G₀ ⊆ D := filter_subset _ _
  have hcard : (D \ agrPair D f₀ f₁ F₀ G₀).card = D.card - (agrPair D f₀ f₁ F₀ G₀).card :=
    card_sdiff_of_subset hZD
  have hinter : ∀ e, agr D f₀ f₁ e ∩ (D \ agrPair D f₀ f₁ F₀ G₀) =
      agr D f₀ f₁ e \ agrPair D f₀ f₁ F₀ G₀ := by
    intro e
    ext x
    simp only [agr, mem_inter, mem_sdiff, mem_filter]
    tauto
  have hch : ∀ e ∈ W, ∀ e' ∈ W, e.1 = e'.1 → e = e' := by
    intro e he e' he' h
    exact Prod.ext h (by rw [hW e he, hW e' he', h])
  have hscal : ∀ e ∈ W, ∀ x ∈ D \ agrPair D f₀ f₁ F₀ G₀, x ∈ agr D f₀ f₁ e →
      f₀ x - F₀.eval x ≠ 0 ∧ (e.1.1 + e.1.2 * x) * (f₀ x - F₀.eval x) = G₀.eval x - f₁ x := by
    intro e he x hxR hx
    have hxa := (mem_filter.mp hx).2
    rw [hW e he] at hxa
    simp only [eval_add, eval_mul, aff_eval] at hxa
    have hxD := (mem_sdiff.mp hxR).1
    have hxZ := (mem_sdiff.mp hxR).2
    refine ⟨?_, by linear_combination -hxa⟩
    intro h0
    apply hxZ
    have hF : F₀.eval x = f₀ x := (sub_eq_zero.mp h0).symm
    refine mem_filter.mpr ⟨hxD, hF, ?_⟩
    rw [hF] at hxa
    exact add_right_cancel hxa
  have key := card_two_points_le W (fun e => e.1) hch (D \ agrPair D f₀ f₁ F₀ G₀)
    (agr D f₀ f₁) (by
      intro e he e' he' x hxR hx hx'
      obtain ⟨hδ, h1⟩ := hscal e he x hxR hx
      obtain ⟨-, h2⟩ := hscal e' he' x hxR hx'
      exact mul_right_cancel₀ hδ (h1.trans h2.symm))
  simp only [hinter] at key
  rw [hcard] at key
  exact key

/-- Lemma 4.7(c) of the paper, its consequence: if the class of a polynomial pair has more than
`C(n, 2)` elements, each agreeing with its fold of the words on at least `A` columns, the pair
agrees with the pair of words on at least `A - 1` columns. -/
theorem agrPair_card_ge (D : Finset K) (f₀ f₁ : K → K) (F₀ G₀ : K[X]) (W : Finset (Cand K))
    (hW : ∀ e ∈ W, e.2 = G₀ + aff e.1 * F₀) {A : ℕ}
    (hA : ∀ e ∈ W, A ≤ (agr D f₀ f₁ e).card) (hcard : D.card.choose 2 < W.card) :
    A ≤ (agrPair D f₀ f₁ F₀ G₀).card + 1 := by
  have h1 := card_agr_outside_le D f₀ f₁ F₀ G₀ W hW
  have h2 : (D.card - (agrPair D f₀ f₁ F₀ G₀).card).choose 2 ≤ D.card.choose 2 :=
    Nat.choose_le_choose 2 (Nat.sub_le _ _)
  have h3 : ∃ e ∈ W, ¬ 2 ≤ (agr D f₀ f₁ e \ agrPair D f₀ f₁ F₀ G₀).card := by
    by_contra hcon
    push Not at hcon
    rw [filter_true_of_mem hcon] at h1
    omega
  obtain ⟨e, he, hlt⟩ := h3
  have h4 : (agr D f₀ f₁ e).card ≤
      (agr D f₀ f₁ e \ agrPair D f₀ f₁ F₀ G₀).card + (agrPair D f₀ f₁ F₀ G₀).card :=
    card_le_card_sdiff_add_card
  have h5 := hA e he
  omega

end DeepFold
