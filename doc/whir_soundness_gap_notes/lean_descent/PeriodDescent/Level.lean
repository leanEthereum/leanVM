/-
The levels of the descent on a subspace domain, in characteristic two.

`D` is a finite set of points of the field `F` that contains `0` and is closed under addition
(`IsSubspace`): in characteristic two this is an `𝔽₂`-subspace, and `D.card = 2 ^ N` says that its
dimension is `N`.

* `IsLevel D j ℓ`: `ℓ` is a level polynomial of level `j`: `X` at level `0`, and
  `ℓ² + a ℓ = q_a ∘ ℓ` at level `j + 1` for a level polynomial `ℓ` of level `j` and a nonzero value
  `a` of `ℓ` on `D`. These are the polynomials reached by the descent.
* `IsLevel.exists_subspace`: a level polynomial of level `j` is the subspace polynomial
  `L_U = ∏_{u ∈ U} (X - u)` of a subspace `U ⊆ D` with `2 ^ j` elements.
* `IsLevel.additive`, `IsLevel.kernel_card`, `IsLevel.fiber_card_le`, `IsLevel.image_card`,
  `IsLevel.dirs_card_le`: `ℓ` is additive, its kernel in `D` has `2 ^ j` elements, its fibres in `D`
  have at most `2 ^ j` elements, it takes `2 ^ (N - j)` values on `D`, of which at most
  `2 ^ (N - j)` are nonzero directions.
-/
import PeriodDescent.Core

open Polynomial Finset
open scoped Classical

namespace PeriodDescent

variable {F : Type*} [Field F]

/-- `D` contains `0` and is closed under addition. In characteristic two: an `𝔽₂`-subspace. -/
def IsSubspace (D : Finset F) : Prop := (0 : F) ∈ D ∧ ∀ x ∈ D, ∀ y ∈ D, x + y ∈ D

/-- The level polynomials of `D`. -/
inductive IsLevel (D : Finset F) : ℕ → F[X] → Prop
  | zero : IsLevel D 0 X
  | succ {j : ℕ} {ℓ : F[X]} {a : F} (h : IsLevel D j ℓ)
      (ha : a ∈ D.image (fun x => ℓ.eval x)) (ha0 : a ≠ 0) : IsLevel D (j + 1) ((qPoly a).comp ℓ)

/-- The subspace polynomial `L_U = ∏_{u ∈ U} (X - u)`. -/
noncomputable def subPoly (U : Finset F) : F[X] := ∏ u ∈ U, (X - C u)

theorem subPoly_eval_eq_zero {U : Finset F} {u : F} (hu : u ∈ U) : (subPoly U).eval u = 0 := by
  unfold subPoly
  rw [eval_prod]
  exact Finset.prod_eq_zero hu (by simp)

section CharTwo

variable [CharP F 2]

/-! ### Additive maps on a subspace -/

/-- The fibres of an additive map on a subspace are translates of the kernel. -/
theorem fiber_card_eq_kernel {D : Finset F} (hD : IsSubspace D) (g : F → F)
    (hg : ∀ x y, g (x + y) = g x + g y) {x0 : F} (hx0 : x0 ∈ D) :
    (D.filter (fun x => g x = g x0)).card = (D.filter (fun x => g x = 0)).card := by
  have h : D.filter (fun x => g x = g x0)
      = (D.filter (fun x => g x = 0)).image (fun x => x + x0) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hx, hgx⟩
      refine ⟨x + x0, ⟨hD.2 x hx x0 hx0, ?_⟩, ?_⟩
      · rw [hg, hgx, CharTwo.add_self_eq_zero]
      · rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    · rintro ⟨k, ⟨hk, hgk⟩, rfl⟩
      exact ⟨hD.2 k hk x0 hx0, by rw [hg, hgk, zero_add]⟩
  rw [h, Finset.card_image_of_injective _ (add_left_injective x0)]

theorem fiber_card_le_kernel {D : Finset F} (hD : IsSubspace D) (g : F → F)
    (hg : ∀ x y, g (x + y) = g x + g y) (y : F) :
    (D.filter (fun x => g x = y)).card ≤ (D.filter (fun x => g x = 0)).card := by
  rcases (D.filter (fun x => g x = y)).eq_empty_or_nonempty with h | ⟨x0, hx0⟩
  · rw [h]
    simp
  · obtain ⟨hx0D, rfl⟩ := Finset.mem_filter.mp hx0
    exact (fiber_card_eq_kernel hD g hg hx0D).le

theorem image_card_mul_kernel {D : Finset F} (hD : IsSubspace D) (g : F → F)
    (hg : ∀ x y, g (x + y) = g x + g y) :
    (D.image g).card * (D.filter (fun x => g x = 0)).card = D.card := by
  have h1 : ∀ y ∈ D.image g,
      (D.filter (fun x => g x = y)).card = (D.filter (fun x => g x = 0)).card := by
    intro y hy
    obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.mp hy
    exact fiber_card_eq_kernel hD g hg hx0
  rw [Finset.card_eq_sum_card_image g D, Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul]

/-! ### Level polynomials -/

/-- A level polynomial is additive. -/
theorem IsLevel.additive {D : Finset F} {j : ℕ} {ℓ : F[X]} (h : IsLevel D j ℓ) (x y : F) :
    ℓ.eval (x + y) = ℓ.eval x + ℓ.eval y := by
  induction h with
  | zero => simp
  | succ h ha ha0 ih =>
    rw [eval_comp, eval_comp, eval_comp, ih, eval_qPoly, eval_qPoly, eval_qPoly, CharTwo.add_sq]
    ring

/-- Additivity as an identity of polynomials: `ℓ(X + b) = ℓ(X) + ℓ(b)`. -/
theorem IsLevel.comp_translate {D : Finset F} {j : ℕ} {ℓ : F[X]} (h : IsLevel D j ℓ) (b : F) :
    ℓ.comp (X + C b) = ℓ + C (ℓ.eval b) := by
  induction h with
  | zero => simp
  | @succ j ℓ a h ha ha0 ih =>
    rw [comp_assoc, ih, eval_comp]
    generalize ℓ.eval b = c
    unfold qPoly
    simp only [add_comp, pow_comp, mul_comp, X_comp, C_comp, eval_add, eval_pow, eval_mul, eval_X,
      eval_C, C_add, C_pow, C_mul]
    linear_combination (ℓ * C c) * (CharTwo.two_eq_zero : (2 : F[X]) = 0)

/-- The kernel in `D` of a level polynomial of level `j` has `2 ^ j` elements. -/
theorem IsLevel.kernel_card {D : Finset F} (hD : IsSubspace D) {j : ℕ} {ℓ : F[X]}
    (h : IsLevel D j ℓ) : (D.filter (fun x => ℓ.eval x = 0)).card = 2 ^ j := by
  induction h with
  | zero =>
    have h1 : D.filter (fun x => (X : F[X]).eval x = 0) = {0} := by
      ext x
      simp only [eval_X, Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨_, rfl⟩
        rfl
      · rintro rfl
        exact ⟨hD.1, rfl⟩
    rw [h1]
    simp
  | @succ j ℓ a h ha ha0 ih =>
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp ha
    have key : ∀ x : F, (ℓ.eval x) ^ 2 + a * ℓ.eval x = 0 ↔ ℓ.eval x = 0 ∨ ℓ.eval x = ℓ.eval b := by
      intro x
      rw [hba]
      have h1 : (ℓ.eval x) ^ 2 + a * ℓ.eval x = ℓ.eval x * (ℓ.eval x + a) := by ring
      rw [h1, mul_eq_zero]
      constructor
      · rintro (h2 | h2)
        · exact Or.inl h2
        · right
          calc ℓ.eval x = ℓ.eval x + a + a := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
            _ = a := by rw [h2, zero_add]
      · rintro (h2 | h2)
        · exact Or.inl h2
        · right
          rw [h2, CharTwo.add_self_eq_zero]
    have hsplit : D.filter (fun x => ((qPoly a).comp ℓ).eval x = 0)
        = D.filter (fun x => ℓ.eval x = 0) ∪ D.filter (fun x => ℓ.eval x = ℓ.eval b) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_union, eval_comp, eval_qPoly]
      constructor
      · rintro ⟨hx, h1⟩
        rcases (key x).mp h1 with h2 | h2
        · exact Or.inl ⟨hx, h2⟩
        · exact Or.inr ⟨hx, h2⟩
      · rintro (⟨hx, h2⟩ | ⟨hx, h2⟩)
        · exact ⟨hx, (key x).mpr (Or.inl h2)⟩
        · exact ⟨hx, (key x).mpr (Or.inr h2)⟩
    have hdisj : Disjoint (D.filter (fun x => ℓ.eval x = 0))
        (D.filter (fun x => ℓ.eval x = ℓ.eval b)) := by
      rw [Finset.disjoint_left]
      intro x h1 h2
      have e1 := (Finset.mem_filter.mp h1).2
      have e2 := (Finset.mem_filter.mp h2).2
      exact ha0 (by rw [← hba, ← e2, e1])
    rw [hsplit, Finset.card_union_of_disjoint hdisj,
      fiber_card_eq_kernel hD (fun x => ℓ.eval x) h.additive hb, ih, pow_succ]
    ring

/-- The fibres in `D` of a level polynomial of level `j` have at most `2 ^ j` elements. -/
theorem IsLevel.fiber_card_le {D : Finset F} (hD : IsSubspace D) {j : ℕ} {ℓ : F[X]}
    (h : IsLevel D j ℓ) (y : F) : (D.filter (fun x => ℓ.eval x = y)).card ≤ 2 ^ j := by
  rw [← h.kernel_card hD]
  exact fiber_card_le_kernel hD (fun x => ℓ.eval x) h.additive y

/-- A level polynomial of level `j` takes `|D| / 2 ^ j` values on `D`. -/
theorem IsLevel.image_card {D : Finset F} (hD : IsSubspace D) {j : ℕ} {ℓ : F[X]}
    (h : IsLevel D j ℓ) : (D.image (fun x => ℓ.eval x)).card * 2 ^ j = D.card := by
  rw [← h.kernel_card hD]
  exact image_card_mul_kernel hD (fun x => ℓ.eval x) h.additive

theorem IsLevel.level_le {D : Finset F} (hD : IsSubspace D) {N j : ℕ} {ℓ : F[X]}
    (h : IsLevel D j ℓ) (hN : D.card = 2 ^ N) : j ≤ N := by
  have h1 := h.kernel_card hD
  have h2 : (D.filter (fun x => ℓ.eval x = 0)).card ≤ D.card := Finset.card_filter_le _ _
  rw [h1, hN] at h2
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2

/-- On a subspace of dimension `N`, a level polynomial of level `j` takes `2 ^ (N - j)` values. -/
theorem IsLevel.image_card_eq {D : Finset F} (hD : IsSubspace D) {N j : ℕ} {ℓ : F[X]}
    (h : IsLevel D j ℓ) (hN : D.card = 2 ^ N) :
    (D.image (fun x => ℓ.eval x)).card = 2 ^ (N - j) := by
  have h1 := h.image_card hD
  have hj := h.level_le hD hN
  have h2 : (2 : ℕ) ^ N = 2 ^ (N - j) * 2 ^ j := by rw [← pow_add, Nat.sub_add_cancel hj]
  rw [hN, h2] at h1
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h1

/-- The nonzero values of `ℓ` on `D`, the directions of the level, number at most `2 ^ (N - j)`
(exactly `2 ^ (N - j) - 1`). -/
theorem IsLevel.dirs_card_le {D : Finset F} (hD : IsSubspace D) {N j : ℕ} {ℓ : F[X]}
    (h : IsLevel D j ℓ) (hN : D.card = 2 ^ N) :
    ((D.image (fun x => ℓ.eval x)).erase 0).card ≤ 2 ^ (N - j) :=
  (Finset.card_erase_le).trans (h.image_card_eq hD hN).le

/-- Below the top level there is a nonzero direction. -/
theorem IsLevel.exists_dir {D : Finset F} (hD : IsSubspace D) {N j : ℕ} {ℓ : F[X]}
    (h : IsLevel D j ℓ) (hN : D.card = 2 ^ N) (hj : j < N) :
    ∃ a ∈ D.image (fun x => ℓ.eval x), a ≠ 0 := by
  have h1 := h.image_card_eq hD hN
  have h2 : 1 < (D.image (fun x => ℓ.eval x)).card := by
    rw [h1]
    exact Nat.one_lt_two_pow (by omega)
  exact Finset.exists_mem_ne h2 0

/-! ### Level polynomials are subspace polynomials -/

/-- A level polynomial of level `j` is the subspace polynomial of a subspace of `D` with `2 ^ j`
elements. -/
theorem IsLevel.exists_subspace {D : Finset F} (hD : IsSubspace D) {j : ℕ} {ℓ : F[X]}
    (h : IsLevel D j ℓ) :
    ∃ U : Finset F, U ⊆ D ∧ IsSubspace U ∧ U.card = 2 ^ j ∧ ℓ = subPoly U := by
  induction h with
  | zero =>
    refine ⟨{0}, ?_, ⟨by simp, ?_⟩, by simp, by simp [subPoly]⟩
    · intro x hx
      rw [Finset.mem_singleton.mp hx]
      exact hD.1
    · intro x hx y hy
      rw [Finset.mem_singleton.mp hx, Finset.mem_singleton.mp hy]
      simp
  | @succ j ℓ a h ha ha0 ih =>
    obtain ⟨U, hUD, hU, hUc, rfl⟩ := ih
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    have hbU : b ∉ U := fun hbU => ha0 (subPoly_eval_eq_zero hbU)
    have hinj : Function.Injective (fun x : F => x + b) := add_left_injective b
    have hdisj : Disjoint U (U.image (fun x => x + b)) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx'
      apply hbU
      have h1 : b = u + (u + b) := by
        rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
      rw [h1]
      exact hU.2 u hu _ hx
    refine ⟨U ∪ U.image (fun x => x + b), ?_, ⟨?_, ?_⟩, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hUD hx
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
        exact hD.2 u (hUD hu) b hb
    · exact Finset.mem_union_left _ hU.1
    · intro x hx y hy
      rcases Finset.mem_union.mp hx with hx | hx
      · rcases Finset.mem_union.mp hy with hy | hy
        · exact Finset.mem_union_left _ (hU.2 x hx y hy)
        · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
          refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x + u, hU.2 x hx u hu, ?_⟩)
          ring
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
        rcases Finset.mem_union.mp hy with hy | hy
        · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u + y, hU.2 u hu y hy, ?_⟩)
          ring
        · obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hy
          refine Finset.mem_union_left _ ?_
          have h1 : u + b + (u' + b) = u + u' := by
            calc u + b + (u' + b) = u + u' + (b + b) := by ring
              _ = u + u' := by rw [CharTwo.add_self_eq_zero, add_zero]
          rw [h1]
          exact hU.2 u hu u' hu'
    · rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj, hUc, pow_succ]
      ring
    · have h1 : subPoly (U ∪ U.image (fun x => x + b))
          = subPoly U * (subPoly U).comp (X + C b) := by
        unfold subPoly
        rw [Finset.prod_union hdisj, Finset.prod_image (fun x _ y _ hxy => hinj hxy),
          Polynomial.prod_comp]
        congr 1
        refine Finset.prod_congr rfl fun u _ => ?_
        rw [sub_comp, X_comp, C_comp, C_add]
        linear_combination (-(C b)) * (CharTwo.two_eq_zero : (2 : F[X]) = 0)
      rw [h1, h.comp_translate b]
      unfold qPoly
      simp only [add_comp, pow_comp, mul_comp, X_comp, C_comp]
      ring

end CharTwo

end PeriodDescent
