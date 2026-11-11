module

public import VCVio.Quantum.Oracle.Compressed.CommutatorBound
public import QuantumFoundations.MatrixMap.Norm

@[expose] public section

/-!
# One cell: the forward block on reachable contents

A cell of the compressed oracle that has been written holds a vector orthogonal to the uniform
superposition `|φ₀⟩`, since the compression sends `|φ₀⟩` to the empty cell `|⊥⟩`. On such
contents, the projector `cellReach = 1 - |φ₀⟩⟨φ₀|` acts as the identity. Let a set of at most `s`
values of the cell be good, with `λ = s / N`, `N = |Y|`. The block of the phase oracle from the
contents that are not good to the good ones, restricted to reachable contents,
`diag(good) · phaseCell χ · diag(not good) · cellReach`, has squared norm at most `λ (2 + 4 λ)`
(`Qrom.norm_cellFwd_sq_le`), against `6 λ` without the restriction. The rows of the good values
`g` differ from `-χ w / N`, `-(1 - χ g) / N` and `N^(-1/2) χ g` by multiples of `⟨φ₀|`, which
`cellReach` kills.
-/

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Qrom

open Quantum

section cell

variable (Y : Type) [Fintype Y] [DecidableEq Y]

/-- The projector onto the contents of a cell orthogonal to the uniform superposition. -/
noncomputable def cellReach : Matrix (Option Y) (Option Y) ℂ :=
  1 - vecMulVec (cellUniform Y) (cellUniform Y)

theorem cellReach_apply (a b : Option Y) :
    cellReach Y a b = (if a = b then 1 else 0) - cellUniform Y a * cellUniform Y b := by
  simp [cellReach, vecMulVec_apply, Matrix.one_apply]

omit [DecidableEq Y] in
theorem sum_cellUniform_mul_self [Nonempty Y] :
    ∑ b, cellUniform Y b * cellUniform Y b = 1 := by
  rw [Fintype.sum_option]
  simp only [cellUniform_none, mul_zero, zero_add]
  have : ∀ y, cellUniform Y (some y) = cellAmp Y := fun _ ↦ rfl
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, cellAmp_mul_self]
  have hN : (Fintype.card Y : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

theorem conjTranspose_cellReach : (cellReach Y)ᴴ = cellReach Y := by
  ext a b
  rw [conjTranspose_apply, cellReach_apply, cellReach_apply]
  rcases a with _ | a <;> rcases b with _ | b <;>
    simp [cellUniform, eq_comm, apply_ite (star : ℂ → ℂ), star_cellAmp, mul_comm]

theorem cellUniform_mul_cellReach [Nonempty Y] (a : Option Y) :
    ∑ b, cellUniform Y b * cellReach Y b a = 0 := by
  simp only [cellReach_apply, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [show ∑ b, cellUniform Y b * (cellUniform Y b * cellUniform Y a) =
      (∑ b, cellUniform Y b * cellUniform Y b) * cellUniform Y a by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ ↦ by ring,
    sum_cellUniform_mul_self, one_mul, sub_self]

theorem cellReach_mul_self [Nonempty Y] : cellReach Y * cellReach Y = cellReach Y := by
  ext a b
  rw [mul_apply]
  simp only [cellReach_apply]
  have h := sum_cellUniform_mul_self Y
  have e : ∀ c, ((if a = c then (1 : ℂ) else 0) - cellUniform Y a * cellUniform Y c) *
      ((if c = b then 1 else 0) - cellUniform Y c * cellUniform Y b) =
      (if a = c then (if c = b then 1 else 0) else 0) -
        (if a = c then cellUniform Y c * cellUniform Y b else 0) -
        cellUniform Y a * cellUniform Y c * (if c = b then 1 else 0) +
        cellUniform Y a * cellUniform Y b * (cellUniform Y c * cellUniform Y c) := by
    intro c
    split_ifs <;> ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', ← Finset.mul_sum,
    h]
  ring

theorem norm_cellReach_le_one [Nonempty Y] : ‖cellReach Y‖ ≤ 1 :=
  MatrixMap.l2_opNorm_le_one_of_proj (conjTranspose_cellReach Y) (cellReach_mul_self Y)

variable {Y} [AddCommGroup Y] [Nonempty Y]

/-- The indicator of the good contents of a cell; the empty cell is not good. -/
def goodInd (G : Y → Prop) [DecidablePred G] : Option Y → ℂ
  | none => 0
  | some y => if G y then 1 else 0

omit [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Nonempty Y] in
@[simp]
theorem goodInd_none (G : Y → Prop) [DecidablePred G] : goodInd G none = 0 :=
  rfl

/-- The forward block on one cell, restricted to reachable contents. -/
noncomputable def cellFwd (χ : AddChar Y ℂ) (G : Y → Prop) [DecidablePred G] :
    Matrix (Option Y) (Option Y) ℂ :=
  diagonal (goodInd G) * phaseCell Y χ * diagonal (1 - goodInd G) * cellReach Y

/-- The block with a multiple of `⟨φ₀|` taken off each good row. -/
noncomputable def cellFwdD (χ : AddChar Y ℂ) (G : Y → Prop) [DecidablePred G] :
    Matrix (Option Y) (Option Y) ℂ :=
  of fun a' a ↦ goodInd G a' * phaseCell Y χ a' a * (1 - goodInd G a) -
    goodInd G a' * ((Fintype.card Y : ℂ)⁻¹ * (1 - χ (a'.getD 0))) *
      (if a = none then 0 else 1)

theorem cellFwd_eq (χ : AddChar Y ℂ) (G : Y → Prop) [DecidablePred G] :
    cellFwd χ G = cellFwdD χ G * cellReach Y := by
  have hN : (Fintype.card Y : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hamp : (Fintype.card Y : ℂ) * (cellAmp Y * cellAmp Y) = 1 := by
    rw [cellAmp_mul_self, mul_inv_cancel₀ hN]
  have hU : ∀ a' a, ∑ b, (goodInd G a' * ((Fintype.card Y : ℂ)⁻¹ * (1 - χ (a'.getD 0))) *
      (if b = none then 0 else 1)) * cellReach Y b a = 0 := by
    intro a' a
    simp_rw [mul_assoc (goodInd G a' * _), ← Finset.mul_sum]
    have : ∑ b, (if b = none then (0 : ℂ) else 1) * cellReach Y b a =
        (cellAmp Y)⁻¹ * ∑ b, cellUniform Y b * cellReach Y b a := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ ↦ ?_
      rcases b with _ | b
      · simp
      · have hA : cellAmp Y ≠ 0 := by
          intro h
          rw [h, mul_zero, mul_zero] at hamp
          exact zero_ne_one hamp
        simp only [reduceCtorEq, ↓reduceIte, one_mul, cellUniform]
        simp only [Option.elim_some]
        rw [← mul_assoc, inv_mul_cancel₀ hA, one_mul]
    rw [this, cellUniform_mul_cellReach, mul_zero, mul_zero]
  ext a' a
  rw [cellFwd, mul_apply, mul_apply]
  simp only [cellFwdD, of_apply, sub_mul, Finset.sum_sub_distrib, hU, sub_zero]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  simp only [mul_diagonal, diagonal_mul, Pi.sub_apply, Pi.one_apply]

omit [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Nonempty Y] in
theorem goodInd_mul_one_sub (G : Y → Prop) [DecidablePred G] (a : Option Y) :
    goodInd G a * (1 - goodInd G a) = 0 := by
  rcases a with _ | a
  · simp [goodInd]
  · by_cases h : G a <;> simp [goodInd, h]

/-- The squared entries of a good row of the block, for a nontrivial character. -/
theorem sum_norm_cellFwdD_row_le {χ : AddChar Y ℂ} (hχ : χ ≠ 0) (G : Y → Prop) [DecidablePred G]
    (s : ℕ) (hs : (Finset.univ.filter G).card ≤ s) {g : Y} (hg : G g) :
    ∑ a, ‖cellFwdD χ G (some g) a‖ ^ 2 ≤
      2 / Fintype.card Y + 4 * s / (Fintype.card Y : ℝ) ^ 2 := by
  have hNpos : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.mpr Fintype.card_pos
  have hgi : goodInd G (some g) = 1 := by simp [goodInd, hg]
  rw [Fintype.sum_option]
  have hnone : ‖cellFwdD χ G (some g) none‖ ^ 2 = (Fintype.card Y : ℝ)⁻¹ := by
    simp only [cellFwdD, of_apply, hgi, one_mul, phaseCell_some_none hχ, goodInd_none, sub_zero,
      mul_one, ↓reduceIte, mul_zero]
    rw [norm_mul, AddChar.norm_apply, mul_one, norm_cellAmp_sq]
  have hsome : ∀ w, ‖cellFwdD χ G (some g) (some w)‖ ^ 2 ≤
      if G w then 4 / (Fintype.card Y : ℝ) ^ 2 else 1 / (Fintype.card Y : ℝ) ^ 2 := by
    intro w
    simp only [cellFwdD, of_apply, hgi, one_mul, phaseCell_some_some hχ, reduceCtorEq,
      ↓reduceIte, mul_one, Option.getD_some]
    by_cases hw : G w
    · simp only [goodInd, hw, ↓reduceIte, sub_self, mul_zero, zero_sub, norm_neg, norm_mul,
        norm_inv, Complex.norm_natCast]
      have h1 : ‖(1 : ℂ) - χ g‖ ≤ 2 := (norm_sub_le _ _).trans (by
        rw [norm_one, AddChar.norm_apply]; norm_num)
      rw [mul_pow, inv_pow]
      calc ((Fintype.card Y : ℝ) ^ 2)⁻¹ * ‖(1 : ℂ) - χ g‖ ^ 2
          ≤ ((Fintype.card Y : ℝ) ^ 2)⁻¹ * 2 ^ 2 := by gcongr
        _ = _ := by ring
    · have hgw : g ≠ w := fun h ↦ hw (h ▸ hg)
      simp only [goodInd, hw, ↓reduceIte, sub_zero, mul_one, hgw]
      have e : (0 + (Fintype.card Y : ℂ)⁻¹ * (1 - χ g - χ w)) -
          (Fintype.card Y : ℂ)⁻¹ * (1 - χ g) = -((Fintype.card Y : ℂ)⁻¹ * χ w) := by ring
      rw [e, norm_neg, norm_mul, AddChar.norm_apply, mul_one, norm_inv, Complex.norm_natCast,
        inv_pow]
      exact le_of_eq (by ring)
  rw [hnone]
  have hsum : ∑ w, ‖cellFwdD χ G (some g) (some w)‖ ^ 2 ≤
      4 * s / (Fintype.card Y : ℝ) ^ 2 + 1 / Fintype.card Y := by
    refine (Finset.sum_le_sum fun w _ ↦ hsome w).trans ?_
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hc1 : ((Finset.univ.filter G).card : ℝ) ≤ s := by exact_mod_cast hs
    have hc2 : ((Finset.univ.filter fun w ↦ ¬ G w).card : ℝ) ≤ Fintype.card Y := by
      exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
    calc ((Finset.univ.filter G).card : ℝ) * (4 / (Fintype.card Y : ℝ) ^ 2) +
          ((Finset.univ.filter fun w ↦ ¬ G w).card : ℝ) * (1 / (Fintype.card Y : ℝ) ^ 2)
        ≤ s * (4 / (Fintype.card Y : ℝ) ^ 2) + Fintype.card Y * (1 / (Fintype.card Y : ℝ) ^ 2) := by
          gcongr
      _ = _ := by field_simp
  calc (Fintype.card Y : ℝ)⁻¹ + ∑ w, ‖cellFwdD χ G (some g) (some w)‖ ^ 2
      ≤ (Fintype.card Y : ℝ)⁻¹ + (4 * s / (Fintype.card Y : ℝ) ^ 2 + 1 / Fintype.card Y) := by
        gcongr
    _ = _ := by field_simp; ring

/-- **The forward block of one cell, on reachable contents.** -/
theorem norm_cellFwd_sq_le (χ : AddChar Y ℂ) (G : Y → Prop) [DecidablePred G] (s : ℕ)
    (hs : (Finset.univ.filter G).card ≤ s) :
    ‖cellFwd χ G‖ ^ 2 ≤ (s / Fintype.card Y : ℝ) * (2 + 4 * (s / Fintype.card Y)) := by
  have hNpos : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.mpr Fintype.card_pos
  rw [cellFwd_eq]
  have hle : ‖cellFwdD χ G * cellReach Y‖ ≤ ‖cellFwdD χ G‖ :=
    (l2_opNorm_mul _ _).trans (by
      simpa using mul_le_mul_of_nonneg_left (norm_cellReach_le_one Y) (norm_nonneg (cellFwdD χ G)))
  refine (pow_le_pow_left₀ (norm_nonneg _) hle 2).trans ((l2_opNorm_sq_le_sum_sq _).trans ?_)
  have hrow0 : ∀ a' a, ¬ (∃ g, a' = some g ∧ G g) → cellFwdD χ G a' a = 0 := by
    intro a' a h
    rcases a' with _ | g
    · simp [cellFwdD, goodInd]
    · have hg : ¬ G g := fun hg ↦ h ⟨g, rfl, hg⟩
      simp [cellFwdD, goodInd, hg]
  rw [Fintype.sum_option]
  simp only [hrow0 none _ (by simp), norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, Finset.sum_const_zero, zero_add]
  by_cases hχ : χ = 0
  · -- the trivial character moves nothing
    subst hχ
    have hz : ∀ g a, cellFwdD (0 : AddChar Y ℂ) G (some g) a = 0 := by
      intro g a
      simp only [cellFwdD, of_apply, phaseCell_zero, AddChar.zero_apply, sub_self, mul_zero,
        zero_mul, sub_zero]
      rcases a with _ | a
      · simp
      · by_cases h : g = a
        · subst h
          rw [Matrix.one_apply_eq, mul_one, goodInd_mul_one_sub]
        · simp [h]
    simp only [hz, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero]
    positivity
  · calc ∑ g, ∑ a, ‖cellFwdD χ G (some g) a‖ ^ 2
        ≤ ∑ g, if G g then 2 / Fintype.card Y + 4 * s / (Fintype.card Y : ℝ) ^ 2 else 0 := by
          refine Finset.sum_le_sum fun g _ ↦ ?_
          by_cases hg : G g
          · rw [ite_eq_left hg]
            exact sum_norm_cellFwdD_row_le hχ G s hs hg
          · rw [ite_eq_right hg]
            simp [hrow0 (some g) _ (by simp [hg])]
      _ = ((Finset.univ.filter G).card : ℝ) *
            (2 / Fintype.card Y + 4 * s / (Fintype.card Y : ℝ) ^ 2) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      _ ≤ s * (2 / Fintype.card Y + 4 * s / (Fintype.card Y : ℝ) ^ 2) := by
          gcongr
      _ = _ := by field_simp

end cell

end Qrom
