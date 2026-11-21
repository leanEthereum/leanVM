/-
The link with the DEEP fold lemma (`DeepFold`): the hypothesis `hΛ` of `DeepFold.lemmaF_exc`,
"every fold has at most `Λ` candidates", follows from the list bound `RSListBound` of this
library, hence from the single-lane hypothesis `H_K` over the small field (Hypothesis 6.4 of the
paper).

In `DeepFold` the field `K` is the large field (here `E`), the points `D` are a finite set of
`E`, and the words `O₀, O₁` are functions `E → ι → E`. Here the points are the images in `E` of
a finite set `D₀` of points of a subfield `K`: in leanVM the domain is in `GF(2^64)`.
-/
import DeepFold.Main
import Interleave.ReedSolomon

open Polynomial Finset
open scoped Classical

namespace Interleave

variable {K : Type*} [Field K] {E : Type*} [Field E] [Fintype E] [Algebra K E] {ι : Type*}
  [Fintype ι]

/-- A list bound for words with values in `E^ι` on points of `K` bounds, for every challenge
`c`, the candidates `(c, P)` of the fold `O₁ + a_c O₀`: the hypothesis `hΛ` of
`DeepFold.lemmaF_exc`. -/
theorem card_fullT_filter_le {D₀ : Finset K} {d A Λ : ℕ} (hΛ : RSListBound D₀ E ι d A Λ)
    (O₀ O₁ : E → ι → E) (c : E × E) :
    ((DeepFold.fullT (D₀.image (algebraMap K E)) O₀ O₁ d A).filter (fun e => e.1 = c)).card ≤
      Λ := by
  have hinj : Set.InjOn (fun e : DeepFold.CandL ι E => e.2)
      ((DeepFold.fullT (D₀.image (algebraMap K E)) O₀ O₁ d A).filter (fun e => e.1 = c)) := by
    intro e he e' he' h
    exact Prod.ext
      ((mem_filter.mp (mem_coe.mp he)).2.trans (mem_filter.mp (mem_coe.mp he')).2.symm) h
  rw [← card_image_of_injOn hinj]
  refine hΛ.image (fun x u => O₁ x u + (c.1 + c.2 * x) * O₀ x u) _ fun P hP => ?_
  obtain ⟨e, he, rfl⟩ := mem_image.mp hP
  obtain ⟨heT, rfl⟩ := mem_filter.mp he
  obtain ⟨hdeg, hagr⟩ := DeepFold.mem_fullT.mp heT
  refine ⟨hdeg, hagr.trans (card_le_card fun x hx => ?_)⟩
  rw [DeepFold.agrL, mem_filter] at hx
  exact mem_agr.mpr ⟨hx.1, funext fun u => (hx.2 u).symm⟩

/-- **Lemma 4.10(1) of the paper from a list bound on points of the small field.** The bound of
`DeepFold.lemmaF_exc` on the exceptional set, with its hypothesis `hΛ` replaced by
`RSListBound D₀ E ι d A Λ`. -/
theorem lemmaF_exc_of_rsListBound (D₀ : Finset K) (O₀ O₁ : E → ι → E) (d A : ℕ) {ex : ι → ℕ}
    (hex : Function.Injective ex) {Eb : ℕ} (hE : ∀ u, ex u ≤ Eb) (Λ : ℕ)
    (hΛ : RSListBound D₀ E ι d A Λ) (s : ℕ) {B : ℕ} (hB : 0 < B) :
    ((DeepFold.ExcL (DeepFold.fullT (D₀.image (algebraMap K E)) O₀ O₁ d A) ex s B).card : ℚ) /
        (Fintype.card (Fin s → E × E) : ℚ) ≤
      (Λ : ℚ) ^ 3 * (Fintype.card E : ℚ) ^ 6 *
        (((d + 1 + Eb : ℕ) : ℚ) / Fintype.card E) ^ s / B :=
  DeepFold.lemmaF_exc _ O₀ O₁ d A hex hE Λ (card_fullT_filter_le hΛ O₀ O₁) s hB

/-- The same from `H_K`, the hypothesis on single words with values in the small field, for
`A > (n + 3d)/4`: the list factor is `2L - 1`. -/
theorem lemmaF_exc_of_HK (D₀ : Finset K) (O₀ O₁ : E → ι → E) (d A : ℕ) {ex : ι → ℕ}
    (hex : Function.Injective ex) {Eb : ℕ} (hE : ∀ u, ex u ≤ Eb) (L : ℕ)
    (hL : RSListBound₁ D₀ d A L) (hda : d < A) (h4 : D₀.card + 3 * d < 4 * A) (s : ℕ) {B : ℕ}
    (hB : 0 < B) :
    ((DeepFold.ExcL (DeepFold.fullT (D₀.image (algebraMap K E)) O₀ O₁ d A) ex s B).card : ℚ) /
        (Fintype.card (Fin s → E × E) : ℚ) ≤
      ((2 * L - 1 : ℕ) : ℚ) ^ 3 * (Fintype.card E : ℚ) ^ 6 *
        (((d + 1 + Eb : ℕ) : ℚ) / Fintype.card E) ^ s / B := by
  have : Module.Finite K E := Module.Finite.of_finite
  exact lemmaF_exc_of_rsListBound D₀ O₀ O₁ d A hex hE _
    (rs_interleave_two_mul E ι hL hda h4) s hB

/-- info: 'Interleave.card_fullT_filter_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms card_fullT_filter_le

/-- info: 'Interleave.lemmaF_exc_of_rsListBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lemmaF_exc_of_rsListBound

/-- info: 'Interleave.lemmaF_exc_of_HK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lemmaF_exc_of_HK

end Interleave
