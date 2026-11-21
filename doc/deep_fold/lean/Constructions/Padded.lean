/-
A fixed set and a free flat: lists at agreement `5n/8` for rate 1/2 (Proposition 3.4(c) of the
paper).

For a finite set `P` and a flat `F = a + V` disjoint from it,
`L_P L_F = L_P X ^ |V| + (degree at most |P| + |V| / 2)`. So the word `L_P(x) x ^ |V|` agrees on
`P ∪ F` with a polynomial of degree at most `|P| + |V| / 2`, one for each flat `F` of that size
(`padPoly_mem_RSList`). With `P` inside a hyperplane `H` of the domain `D`, `|D| = n`, and the
flats of size `n / 4` in the other coset of `H`, this gives at least `n - 2` list members at
agreement `|P| + n / 4` and degree at most `|P| + n / 8` (`padded_flats_list`): for
`|P| = 3n/8`, degree at most `n / 2` at agreement `5n/8` (`five_eighths_slack`), and for
`|P| = 3n/8 - 1`, degree below `n / 2` at agreement `5n/8 - 1` (`five_eighths_genuine`).
-/
import Constructions.Flats

open Polynomial
open scoped Classical

namespace Constructions

variable {K : Type*} [Field K]

/-- The flat `a + V` as a finset. -/
noncomputable def flat (V : AddSubgroup K) (a : K) : Finset K := (pts V).image (· + a)

theorem mem_flat {V : AddSubgroup K} [Finite V] {a x : K} : x ∈ flat V a ↔ x - a ∈ V := by
  rw [flat, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [add_sub_cancel_right]
    exact mem_pts.mp hy
  · intro h
    exact ⟨x - a, mem_pts.mpr h, sub_add_cancel x a⟩

theorem card_flat (V : AddSubgroup K) [Finite V] (a : K) : (flat V a).card = Nat.card V := by
  rw [flat, Finset.card_image_of_injective _ fun x y h => add_right_cancel h, card_pts]

/-- A flat determines its direction. -/
theorem flat_direction {V W : AddSubgroup K} [Finite V] [Finite W] {a b : K}
    (h : flat V a = flat W b) : V = W := by
  have key : ∀ (V W : AddSubgroup K) [Finite V] [Finite W] (a b : K), flat V a = flat W b →
      V ≤ W := by
    intro V W _ _ a b h x hx
    have ha : a ∈ flat W b := by
      rw [← h, mem_flat, sub_self]
      exact V.zero_mem
    have hxa : x + a ∈ flat W b := by
      rw [← h, mem_flat, add_sub_cancel_right]
      exact hx
    have := W.sub_mem (mem_flat.mp hxa) (mem_flat.mp ha)
    rwa [show x + a - b - (a - b) = x by ring] at this
  exact le_antisymm (key V W a b h) (key W V b a h.symm)

/-- The polynomial of the padded flat: `L_P (X ^ |V| - L_F)` for `F = a + V`. -/
noncomputable def padPoly (P : Finset K) (V : AddSubgroup K) (a : K) : K[X] :=
  locator P * (X ^ Nat.card V - locator (flat V a))

/-- The word of the padded flats: `x ↦ L_P(x) x ^ m`. -/
noncomputable def padWord (P : Finset K) (m : ℕ) : K → K := fun x => (locator P).eval x * x ^ m

theorem padPoly_eval (P : Finset K) (V : AddSubgroup K) (a x : K) :
    (padPoly P V a).eval x =
      padWord P (Nat.card V) x - (locator P).eval x * (locator (flat V a)).eval x := by
  simp only [padPoly, padWord, eval_mul, eval_sub, eval_pow, eval_X]
  ring

/-- `padPoly` agrees with the word on `P ∪ F`. -/
theorem subset_agree_padPoly (D P : Finset K) (V : AddSubgroup K) (a : K) (hP : P ⊆ D)
    (hF : flat V a ⊆ D) : P ∪ flat V a ⊆ agree D (padWord P (Nat.card V)) (padPoly P V a) := by
  intro x hx
  rw [agree, Finset.mem_filter, padPoly_eval]
  rcases Finset.mem_union.mp hx with h | h
  · exact ⟨hP h, by rw [locator_eval_eq_zero.mpr h, zero_mul, sub_zero]⟩
  · exact ⟨hF h, by rw [locator_eval_eq_zero.mpr h, mul_zero, sub_zero]⟩

/-- The agreement is exactly `P ∪ F`. -/
theorem agree_padPoly (D P : Finset K) (V : AddSubgroup K) (a : K) (hP : P ⊆ D)
    (hF : flat V a ⊆ D) : agree D (padWord P (Nat.card V)) (padPoly P V a) = P ∪ flat V a := by
  refine Finset.Subset.antisymm (fun x hx => ?_) (subset_agree_padPoly D P V a hP hF)
  obtain ⟨-, hx⟩ := Finset.mem_filter.mp hx
  rw [padPoly_eval, sub_eq_self, mul_eq_zero, locator_eval_eq_zero, locator_eval_eq_zero] at hx
  exact Finset.mem_union.mpr hx

/-- Distinct flats of one size give distinct polynomials. -/
theorem padPoly_injective (P : Finset K) {V W : AddSubgroup K} {a b : K}
    (hc : Nat.card V = Nat.card W) (h : padPoly P V a = padPoly P W b) : flat V a = flat W b := by
  rw [padPoly, padPoly, hc] at h
  exact locator_injective (sub_right_injective (mul_left_cancel₀ (locator_ne_zero P) h))

section CharTwo

variable [CharP K 2]

/-- A flat has gap half its size: `L_{a + V} = X ^ |V| + (degree at most |V| / 2)`. -/
theorem natDegree_locator_flat_sub_le (V : AddSubgroup K) [Finite V] (a : K) :
    (X ^ Nat.card V - locator (flat V a)).natDegree ≤ Nat.card V / 2 := by
  rw [flat, locator_coset, ← natDegree_neg]
  have e : -(X ^ Nat.card V - (subPoly V - C ((subPoly V).eval a))) =
      (subPoly V - X ^ Nat.card V) - C ((subPoly V).eval a) := by ring
  rw [e]
  exact (natDegree_sub_le _ _).trans (max_le (natDegree_subPoly_sub_le V) (by simp))

theorem padPoly_natDegree_le (P : Finset K) (V : AddSubgroup K) [Finite V] (a : K) :
    (padPoly P V a).natDegree ≤ P.card + Nat.card V / 2 := by
  refine natDegree_mul_le.trans ?_
  rw [locator_natDegree]
  exact Nat.add_le_add_left (natDegree_locator_flat_sub_le V a) _

/-- A fixed set and a free flat (the proof of Proposition 3.4(c) of the paper): for `P` and
`F = a + V` disjoint inside `D`, the word `L_P(x) x ^ |V|` agrees on at least `|P| + |V|` points
with the polynomial `L_P (X ^ |V| - L_F)` of degree at most `|P| + |V| / 2`. -/
theorem padPoly_mem_RSList (D P : Finset K) (V : AddSubgroup K) [Finite V] (a : K) (hP : P ⊆ D)
    (hF : flat V a ⊆ D) (hdisj : Disjoint P (flat V a)) :
    padPoly P V a ∈
      RSList D (padWord P (Nat.card V)) (P.card + Nat.card V / 2 + 1) (P.card + Nat.card V) := by
  constructor
  · refine lt_of_le_of_lt degree_le_natDegree ?_
    exact_mod_cast Nat.lt_succ_of_le (padPoly_natDegree_le P V a)
  · have h := Finset.card_le_card (subset_agree_padPoly D P V a hP hF)
    rwa [Finset.card_union_of_disjoint hdisj, card_flat] at h

/-- **Padded flats.** Let `H` be a hyperplane of the subspace domain `D`, `|D| = n`, and `P` any
set of points of `H`. The word `L_P(x) x ^ (n / 4)` has at least `n - 2` polynomials of degree at
most `|P| + n / 8` agreeing with it on at least `|P| + n / 4` points of `D`: one for each of the
two cosets, outside `H`, of each hyperplane of `H`. -/
theorem padded_flats_list (D H : AddSubgroup K) [Finite D] (hHD : H ≤ D)
    (hH : 2 * Nat.card H = Nat.card D) (P : Finset K) (hP : ∀ x ∈ P, x ∈ H) {q : ℕ}
    (hq : Nat.card D = 4 * q) :
    ((Nat.card D - 2 : ℕ) : ℕ∞) ≤
      (RSList (pts D) (padWord P q) (P.card + q / 2 + 1) (P.card + q)).encard := by
  have : Finite H := Set.finite_coe_iff.mpr ((Set.toFinite (D : Set K)).subset hHD)
  -- a point of `D` outside `H`
  obtain ⟨b, hbD, hbH⟩ : ∃ b ∈ D, b ∉ H := by
    by_contra hcon
    have hle : D ≤ H := fun x hx => by
      by_contra hx'
      exact hcon ⟨x, hx, hx'⟩
    have hc : Nat.card D ≠ 0 := by
      rw [← card_pts]
      exact (card_pts_pos D).ne'
    rw [le_antisymm hle hHD] at hH hc
    omega
  set T : Set (AddSubgroup K) := {V | V ≤ H ∧ 2 * Nat.card V = Nat.card H} with hT
  have hfin : ∀ V ∈ T, Finite V := fun V hV =>
    Set.finite_coe_iff.mpr ((Set.toFinite (H : Set K)).subset hV.1)
  -- for each hyperplane of `H`, a point of `H` outside it
  have hex : ∀ V : AddSubgroup K, ∃ h : K, V ∈ T → h ∈ H ∧ h ∉ V := by
    intro V
    by_cases hV : V ∈ T
    · have := hfin V hV
      have hne : ∃ h ∈ H, h ∉ V := by
        by_contra hcon
        have hle : H ≤ V := fun x hx => by
          by_contra hx'
          exact hcon ⟨x, hx, hx'⟩
        have hc : Nat.card H ≠ 0 := by
          rw [← card_pts]
          exact (card_pts_pos H).ne'
        have h2 := hV.2
        rw [le_antisymm hV.1 hle] at h2
        omega
      obtain ⟨h, hh⟩ := hne
      exact ⟨h, fun _ => hh⟩
    · exact ⟨0, fun h => absurd h hV⟩
  choose hsel hsel_spec using hex
  have hcardV : ∀ V ∈ T, Nat.card V = q := by
    intro V hV
    have := hV.2
    omega
  -- the two families
  let f₁ : AddSubgroup K → K[X] := fun V => padPoly P V b
  let f₂ : AddSubgroup K → K[X] := fun V => padPoly P V (b + hsel V)
  have hflat_sub : ∀ V ∈ T, ∀ a ∈ D, a ∉ H → flat V a ⊆ pts D ∧ Disjoint P (flat V a) := by
    intro V hV a haD haH
    have := hfin V hV
    constructor
    · intro x hx
      have hx' := hHD (hV.1 (mem_flat.mp hx))
      have := D.add_mem hx' haD
      rw [sub_add_cancel] at this
      exact mem_pts.mpr this
    · rw [Finset.disjoint_left]
      intro x hxP hxF
      apply haH
      have h1 := H.sub_mem (hP x hxP) (hV.1 (mem_flat.mp hxF))
      rwa [sub_sub_cancel] at h1
  have hbh : ∀ V ∈ T, b + hsel V ∈ D ∧ b + hsel V ∉ H := by
    intro V hV
    obtain ⟨h1, -⟩ := hsel_spec V hV
    refine ⟨D.add_mem hbD (hHD h1), fun h => hbH ?_⟩
    have := H.sub_mem h h1
    rwa [add_sub_cancel_right] at this
  have hPD : P ⊆ pts D := fun x hx => mem_pts.mpr (hHD (hP x hx))
  have hmem₁ : ∀ V ∈ T, f₁ V ∈ RSList (pts D) (padWord P q) (P.card + q / 2 + 1) (P.card + q) := by
    intro V hV
    have := hfin V hV
    obtain ⟨h1, h2⟩ := hflat_sub V hV b hbD hbH
    have := padPoly_mem_RSList (pts D) P V b hPD h1 h2
    rwa [hcardV V hV] at this
  have hmem₂ : ∀ V ∈ T, f₂ V ∈ RSList (pts D) (padWord P q) (P.card + q / 2 + 1) (P.card + q) := by
    intro V hV
    have := hfin V hV
    obtain ⟨h1, h2⟩ := hflat_sub V hV _ (hbh V hV).1 (hbh V hV).2
    have := padPoly_mem_RSList (pts D) P V (b + hsel V) hPD h1 h2
    rwa [hcardV V hV] at this
  have hinj₁ : Set.InjOn f₁ T := by
    intro V hV W hW h
    have := hfin V hV
    have := hfin W hW
    exact flat_direction (padPoly_injective P ((hcardV V hV).trans (hcardV W hW).symm) h)
  have hinj₂ : Set.InjOn f₂ T := by
    intro V hV W hW h
    have := hfin V hV
    have := hfin W hW
    exact flat_direction (padPoly_injective P ((hcardV V hV).trans (hcardV W hW).symm) h)
  have hdisj : Disjoint (f₁ '' T) (f₂ '' T) := by
    rw [Set.disjoint_left]
    rintro _ ⟨V, hV, rfl⟩ ⟨W, hW, h⟩
    have := hfin V hV
    have := hfin W hW
    have hfl := padPoly_injective P ((hcardV W hW).trans (hcardV V hV).symm) h
    have hVW : W = V := flat_direction hfl
    subst hVW
    have hb : b ∈ flat W (b + hsel W) := by
      rw [hfl, mem_flat, sub_self]
      exact W.zero_mem
    have h3 := W.neg_mem (mem_flat.mp hb)
    rw [show -(b - (b + hsel W)) = hsel W by ring] at h3
    exact (hsel_spec W hW).2 h3
  have hT : ((Nat.card H - 1 : ℕ) : ℕ∞) ≤ T.encard := card_hyperplanes_ge H
  have hsub : f₁ '' T ∪ f₂ '' T ⊆
      RSList (pts D) (padWord P q) (P.card + q / 2 + 1) (P.card + q) := by
    rintro _ (⟨V, hV, rfl⟩ | ⟨V, hV, rfl⟩)
    · exact hmem₁ V hV
    · exact hmem₂ V hV
  refine le_trans ?_ (Set.encard_le_encard hsub)
  rw [Set.encard_union_eq hdisj, hinj₁.encard_image, hinj₂.encard_image]
  have h2 : ((Nat.card D - 2 : ℕ) : ℕ∞) = ((Nat.card H - 1 : ℕ) : ℕ∞) + ((Nat.card H - 1 : ℕ) : ℕ∞) := by
    have hc : Nat.card H ≠ 0 := by
      rw [← card_pts]
      exact (card_pts_pos H).ne'
    rw [← Nat.cast_add]
    congr 1
    omega
  rw [h2]
  exact add_le_add hT hT

/-- **Rate 1/2, agreement `5n/8`, degree at most `n / 2`.** On a subspace domain of size
`n = 8m`, for any `3m` points `P` of a hyperplane, the word `L_P(x) x ^ (2m)` has at least `n - 2`
polynomials of degree at most `4m = n / 2` agreeing with it on at least `5m = 5n/8` points. -/
theorem five_eighths_slack (D H : AddSubgroup K) [Finite D] (hHD : H ≤ D)
    (hH : 2 * Nat.card H = Nat.card D) {m : ℕ} (hD : Nat.card D = 8 * m) (P : Finset K)
    (hP : ∀ x ∈ P, x ∈ H) (hPc : P.card = 3 * m) :
    ((Nat.card D - 2 : ℕ) : ℕ∞) ≤
      (RSList (pts D) (padWord P (2 * m)) (4 * m + 1) (5 * m)).encard := by
  have h := padded_flats_list D H hHD hH P hP (q := 2 * m) (by omega)
  rw [hPc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)] at h
  rwa [show 3 * m + m + 1 = 4 * m + 1 by ring, show 3 * m + 2 * m = 5 * m by ring] at h

/-- **Rate 1/2, genuine codewords.** On a subspace domain of size `n = 8m`, for any `3m - 1`
points `P` of a hyperplane, the word `L_P(x) x ^ (2m)` has at least `n - 2` polynomials of degree
below `4m = n / 2` agreeing with it on at least `5m - 1 = 5n/8 - 1` points. -/
theorem five_eighths_genuine (D H : AddSubgroup K) [Finite D] (hHD : H ≤ D)
    (hH : 2 * Nat.card H = Nat.card D) {m : ℕ} (hm : 1 ≤ m) (hD : Nat.card D = 8 * m)
    (P : Finset K) (hP : ∀ x ∈ P, x ∈ H) (hPc : P.card = 3 * m - 1) :
    ((Nat.card D - 2 : ℕ) : ℕ∞) ≤
      (RSList (pts D) (padWord P (2 * m)) (4 * m) (5 * m - 1)).encard := by
  have h := padded_flats_list D H hHD hH P hP (q := 2 * m) (by omega)
  rw [hPc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)] at h
  rwa [show 3 * m - 1 + m + 1 = 4 * m by omega, show 3 * m - 1 + 2 * m = 5 * m - 1 by omega] at h

end CharTwo

end Constructions
