module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.ENNReal.BigOperators

@[expose] public section

/-!
# Presampling an adaptive computation on a random function

A procedure reads a function `H : X → Y` at the points `pt h k`, `k : K`, where the point of `k`
depends only on the answers `h k'` at the earlier positions `k' < k`, and different positions read
different points. Then a uniform `H` is the same as uniform answers `h : K → Y` together with an
independent uniform `G : X → Y` used off the points read (`Qrom.sum_eq_sum_override`): every `H`
is `override G h` for exactly one `h`, the answers of the procedure on `H`, and for `|Y|^|K|`
functions `G`, those that agree with `H` off the points read.
-/

open scoped ENNReal

set_option linter.unusedSectionVars false

namespace Qrom

variable {X Y K : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype K]
  [DecidableEq K] [LinearOrder K]

/-- An adaptive procedure: the point read at each position, from the answers at the earlier
positions. -/
structure Procedure (X Y K : Type) [LinearOrder K] where
  /-- The point read at position `k`, given the answers. -/
  pt : (K → Y) → K → X
  /-- It depends only on the answers at earlier positions. -/
  causal : ∀ h h' k, (∀ k' < k, h k' = h' k') → pt h k = pt h' k
  /-- Different positions read different points. -/
  distinct : ∀ h, Function.Injective (pt h)

variable (C : Procedure X Y K)

/-- The function answering the points read with the answers, and the rest with `G`. -/
noncomputable def override (G : X → Y) (h : K → Y) (x : X) : Y :=
  if hx : ∃ k, C.pt h k = x then h (Classical.choose hx) else G x

theorem override_pt (G : X → Y) (h : K → Y) (k : K) : override C G h (C.pt h k) = h k := by
  have hx : ∃ k', C.pt h k' = C.pt h k := ⟨k, rfl⟩
  rw [override, dite_eq_left hx]
  congr 1
  exact C.distinct h (Classical.choose_spec hx)

theorem override_of_not_mem (G : X → Y) (h : K → Y) (x : X) (hx : ∀ k, C.pt h k ≠ x) :
    override C G h x = G x := by
  rw [override, dite_eq_right (fun ⟨k, hk⟩ ↦ hx k hk)]

/-- The answers determine themselves: if `H` answers the points read with `h` and with `h'`, the two
agree. -/
theorem answers_unique {H : X → Y} {h h' : K → Y} (hh : ∀ k, H (C.pt h k) = h k)
    (hh' : ∀ k, H (C.pt h' k) = h' k) : h = h' := by
  funext k
  induction k using WellFoundedLT.induction with
  | ind k ih =>
    have hpt : C.pt h k = C.pt h' k := C.causal h h' k fun k' hk' ↦ ih k' hk'
    rw [← hh k, ← hh' k, hpt]

/-- `override G h = H` exactly when `h` answers the points read as `H` does and `G` agrees with
`H` off them. -/
theorem override_eq_iff (G : X → Y) (h : K → Y) (H : X → Y) :
    override C G h = H ↔ (∀ k, H (C.pt h k) = h k) ∧ ∀ x, (∀ k, C.pt h k ≠ x) → G x = H x := by
  constructor
  · rintro rfl
    exact ⟨fun k ↦ override_pt C G h k, fun x hx ↦ (override_of_not_mem C G h x hx).symm⟩
  · rintro ⟨hh, hG⟩
    funext x
    by_cases hx : ∃ k, C.pt h k = x
    · obtain ⟨k, rfl⟩ := hx
      rw [override_pt, hh]
    · push Not at hx
      rw [override_of_not_mem C G h x hx, hG x hx]

/-- The functions agreeing with `H` off the points read by `h`. -/
theorem card_agree (h : K → Y) (H : X → Y) :
    (Finset.univ.filter fun G : X → Y ↦ ∀ x, (∀ k, C.pt h k ≠ x) → G x = H x).card =
      Fintype.card Y ^ Fintype.card K := by
  classical
  set img := Finset.univ.image (C.pt h)
  have himg : img.card = Fintype.card K := by
    rw [Finset.card_image_of_injective _ (C.distinct h), Finset.card_univ]
  have e : {G : X → Y // ∀ x, (∀ k, C.pt h k ≠ x) → G x = H x} ≃ ({x // x ∈ img} → Y) :=
    { toFun := fun G x ↦ G.1 x.1
      invFun := fun g ↦ ⟨fun x ↦ if hx : x ∈ img then g ⟨x, hx⟩ else H x, fun x hx ↦ by
        have : x ∉ img := by simpa [img] using hx
        simp [this]⟩
      left_inv := fun G ↦ by
        apply Subtype.ext
        funext x
        by_cases hx : x ∈ img
        · simp [hx]
        · have hx' : ∀ k, C.pt h k ≠ x := by simpa [img] using hx
          simp [hx, G.2 x hx']
      right_inv := fun g ↦ by
        funext x
        simp [x.2] }
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fun, Fintype.card_coe, himg]

/-- **Presampling.** Uniform `H` is uniform answers with an independent `G` off the points read. -/
theorem sum_eq_sum_override (Φ : (X → Y) → ℝ≥0∞) :
    (Fintype.card Y : ℝ≥0∞) ^ Fintype.card K * ∑ H, Φ H = ∑ h, ∑ G, Φ (override C G h) := by
  classical
  -- `N H`: the pairs `(h, G)` overriding to `H`
  set N : (X → Y) → ℕ := fun H ↦
    (Finset.univ.filter fun hG : (K → Y) × (X → Y) ↦ override C hG.2 hG.1 = H).card
  have hN_le : ∀ H, N H ≤ Fintype.card Y ^ Fintype.card K := by
    intro H
    by_cases hex : ∃ h₀ : K → Y, ∀ k, H (C.pt h₀ k) = h₀ k
    · obtain ⟨h₀, hh₀⟩ := hex
      have hsub : (Finset.univ.filter fun hG : (K → Y) × (X → Y) ↦ override C hG.2 hG.1 = H) =
          ({h₀} : Finset (K → Y)) ×ˢ
            (Finset.univ.filter fun G : X → Y ↦ ∀ x, (∀ k, C.pt h₀ k ≠ x) → G x = H x) := by
        ext ⟨h, G⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
          Finset.mem_singleton, override_eq_iff]
        constructor
        · rintro ⟨hh, hG⟩
          have : h = h₀ := answers_unique C hh hh₀
          subst this
          exact ⟨rfl, hG⟩
        · rintro ⟨rfl, hG⟩
          exact ⟨hh₀, hG⟩
      simp only [N]
      rw [hsub, Finset.card_product, Finset.card_singleton, one_mul, card_agree]
    · have : (Finset.univ.filter fun hG : (K → Y) × (X → Y) ↦ override C hG.2 hG.1 = H) = ∅ := by
        ext ⟨h, G⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro hov
        exact hex ⟨h, ((override_eq_iff C G h H).mp hov).1⟩
      simp [N, this]
  have hN_sum : ∑ H, N H = Fintype.card (K → Y) * Fintype.card (X → Y) := by
    simp only [N]
    rw [← Fintype.card_prod, ← Finset.card_univ]
    exact (Finset.card_eq_sum_card_fiberwise (f := fun hG : (K → Y) × (X → Y) ↦
      override C hG.2 hG.1) (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _)).symm
  have hN_eq : ∀ H, N H = Fintype.card Y ^ Fintype.card K := by
    have hsum_le : ∑ H, N H ≤ ∑ _H : X → Y, Fintype.card Y ^ Fintype.card K :=
      Finset.sum_le_sum fun H _ ↦ hN_le H
    have heq : ∑ H, N H = ∑ _H : X → Y, Fintype.card Y ^ Fintype.card K := by
      rw [hN_sum, Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fun, mul_comm]
    intro H
    exact (Finset.sum_eq_sum_iff_of_le fun H _ ↦ hN_le H).mp heq H (Finset.mem_univ _)
  rw [← Fintype.sum_prod_type', ← Finset.sum_fiberwise Finset.univ (fun hG : (K → Y) × (X → Y) ↦
    override C hG.2 hG.1), Finset.mul_sum]
  refine Finset.sum_congr rfl fun H _ ↦ ?_
  rw [Finset.sum_congr rfl (g := fun _ ↦ Φ H) (fun hG hhG ↦ by
    rw [(Finset.mem_filter.mp hhG).2]), Finset.sum_const, nsmul_eq_mul]
  rw [show ((Finset.univ.filter fun hG : (K → Y) × (X → Y) ↦ override C hG.2 hG.1 = H).card :
    ℝ≥0∞) = (N H : ℝ≥0∞) from rfl, hN_eq]
  push_cast
  rfl

end Qrom
