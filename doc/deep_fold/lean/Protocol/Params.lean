/-
The parameter claims at level 0 of a commitment of `2^30` elements (Proposition 7.1 of the paper;
rows M0 and M2 of Theorem 5.2), as checked arithmetic.

Parameters: `q = 2^128`, `d = 2^24 + 5` (`κ = 24`, `ℓ = 6`), so `ε = (2^24 + 5 + 63) / q`;
list bound `L = 2^40`; `K₀ = 2^9 q = 2^137`, `M = 2 q = 2^129`,
`B = K₀ (K₀ - 1) (K₀ - M)`; `τ = 2^-119`. With `s = 12` points in one batch, or with the ladder
`6 + 1 + 1 + 2 + 1 + 1`, the point message has error at most `2^-110`; the fold message has error
at most `2^-118`, and `2^-119` in the last round of a level. All of it is `norm_num` on explicit
numerals.
-/
import Protocol.Ladder

open Finset
open scoped Classical

namespace Protocol

/-- The point message of level 0 with one batch of 12 points:
`[C(L, 2) + L^3 q^6 / (K₀ (K₀ - 1) (K₀ - 2 q)) · ∑_{j < 6} τ^(-j)] ε^12 ≤ 2^-110`. -/
theorem point_error_level0_arith :
    ((((2 ^ 40 : ℕ).choose 2 : ℕ) : ℚ) +
        ((2 ^ 40 : ℕ) : ℚ) ^ 3 * ((2 ^ 128 : ℕ) : ℚ) ^ 6 /
            ((2 ^ 137 * (2 ^ 137 - 1) * (2 ^ 137 - 2 ^ 129) : ℕ) : ℚ) *
          ∑ j ∈ range 6, ((1 / 2 ^ 119 : ℚ)⁻¹) ^ j) *
      (((2 ^ 24 + 5 + 2 ^ 6 - 1 : ℕ) : ℚ) / ((2 ^ 128 : ℕ) : ℚ)) ^ 12 ≤ 1 / 2 ^ 110 := by
  rw [Nat.choose_two_right]
  norm_num [Finset.sum_range_succ]

/-- Eleven points are not enough for this bound: at `s = 11` the same expression exceeds
`2^-110`. So 12 is the least number of points of one batch for which the bound of Theorem 5.2 of
the paper is at most `2^-110` (Section 7.1, the entry 12 at list `2^40`). -/
theorem point_error_level0_arith_11 :
    1 / 2 ^ 110 < ((((2 ^ 40 : ℕ).choose 2 : ℕ) : ℚ) +
        ((2 ^ 40 : ℕ) : ℚ) ^ 3 * ((2 ^ 128 : ℕ) : ℚ) ^ 6 /
            ((2 ^ 137 * (2 ^ 137 - 1) * (2 ^ 137 - 2 ^ 129) : ℕ) : ℚ) *
          ∑ j ∈ range 6, ((1 / 2 ^ 119 : ℚ)⁻¹) ^ j) *
      (((2 ^ 24 + 5 + 2 ^ 6 - 1 : ℕ) : ℚ) / ((2 ^ 128 : ℕ) : ℚ)) ^ 11 := by
  rw [Nat.choose_two_right]
  norm_num [Finset.sum_range_succ]

/-- The schedule `6 + 1 + 1 + 2 + 1 + 1` of Section 7.1 of the paper at level 0: the number of
fresh points sent with the fold challenge of round `k + 1`. The first batch has 6 points. -/
def ladder0 (k : ℕ) : ℕ := if k = 2 then 2 else if k < 5 then 1 else 0

/-- The points held at the six rounds of the schedule: 6, 7, 8, 10, 11, 12. -/
theorem held_ladder0 :
    held ladder0 0 6 0 = 6 ∧ held ladder0 0 6 1 = 7 ∧ held ladder0 0 6 2 = 8 ∧
      held ladder0 0 6 3 = 10 ∧ held ladder0 0 6 4 = 11 ∧ held ladder0 0 6 5 = 12 := by
  simp [held, ladder0, Finset.sum_range_succ]

/-- The first point message of level 0 on the ladder `6 + 1 + 1 + 2 + 1 + 1`:
`C(L, 2) ε^6 + (L^3 q^6 / B) ∑_{j < 6} τ^(-j) ε^(σ_{j+1}) ≤ 2^-110`. -/
theorem ladder_error_level0_arith :
    (((2 ^ 40 : ℕ).choose 2 : ℕ) : ℚ) *
        (((2 ^ 24 + 5 + 2 ^ 6 - 1 : ℕ) : ℚ) / ((2 ^ 128 : ℕ) : ℚ)) ^ 6 +
      ∑ j ∈ range 6, ((1 / 2 ^ 119 : ℚ)⁻¹) ^ j *
        (((2 ^ 40 : ℕ) : ℚ) ^ 3 * ((2 ^ 128 : ℕ) : ℚ) ^ 6 *
          (((2 ^ 24 + 5 + 2 ^ 6 - 1 : ℕ) : ℚ) / ((2 ^ 128 : ℕ) : ℚ)) ^ held ladder0 0 6 j /
            ((2 ^ 137 * (2 ^ 137 - 1) * (2 ^ 137 - 2 ^ 129) : ℕ) : ℚ)) ≤ 1 / 2 ^ 110 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := held_ladder0
  rw [Nat.choose_two_right]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h0, h1, h2, h3, h4, h5]
  norm_num

/-- The fold message: `(K₀ - 1) / q^2 + τ ≤ 2^-118` at `K₀ = 2^9 q`, `τ = 2^-119`. -/
theorem fold_error_arith :
    (((2 ^ 137 : ℕ) : ℚ) - 1) / ((2 ^ 128 : ℕ) : ℚ) ^ 2 + 1 / 2 ^ 119 ≤ 1 / 2 ^ 118 := by
  norm_num

/-- The fold message of the last round of a level (no `τ`): `(K₀ - 1) / q^2 ≤ 2^-119`. -/
theorem fold_error_last_arith :
    (((2 ^ 137 : ℕ) : ℚ) - 1) / ((2 ^ 128 : ℕ) : ℚ) ^ 2 ≤ 1 / 2 ^ 119 := by
  norm_num

/-- `K₀ > M = 2 q` and the threshold is positive: (S4) of Section 5.1 of the paper at the deployed
constants. -/
theorem threshold_level0_pos : 0 < 2 ^ 137 * (2 ^ 137 - 1) * (2 ^ 137 - 2 ^ 129) := by
  norm_num

section Deployed

variable {K : Type*} [Field K] [Fintype K]

/-- The point message of level 0, one batch (row M0 of Theorem 5.2 of the paper at the deployed
sizes). Over a field of `2^128` elements, for a level with 6 lane variables and degree bound
`2^24 + 5`, if every word of the level has at most `2^40` list members, then 12 independent
uniform points fail to be good for the committed word with probability at most `2^-110`. -/
theorem level0_point_error (hq : Fintype.card K = 2 ^ 128) (D : Finset K) (thr : ℕ → ℕ)
    (hL : ∀ k r, k + r = 6 → ∀ O' : Word K r,
      (listW D O' (2 ^ 24 + 5) (thr k)).card ≤ 2 ^ 40) (O : Word K 6) :
    dens (fun z : Fin 12 → K × K => ¬ Good (1 / 2 ^ 119) D (2 ^ 24 + 5) thr 12
      (2 ^ 137 * (2 ^ 137 - 1) * (2 ^ 137 - 2 ^ 129)) 6 O z) ≤ 1 / 2 ^ 110 := by
  have h := dens_not_good_le (τ := 1 / 2 ^ 119) (D := D) (d := 2 ^ 24 + 5) (thr := thr)
    (s := 12) (by norm_num) threshold_level0_pos (by norm_num : 1 ≤ 6) hL O
  rw [hq] at h
  exact h.trans point_error_level0_arith

/-- The first point message of level 0 on the ladder `6 + 1 + 1 + 2 + 1 + 1` (row M0 of
Theorem 5.2 of the paper for this schedule, at the deployed sizes): 6 independent uniform points
fail to be good with probability at most `2^-110`. -/
theorem level0_ladder_error (hq : Fintype.card K = 2 ^ 128) (D : Finset K) (thr : ℕ → ℕ)
    (hL : ∀ k r, k + r = 6 → ∀ O' : Word K r,
      (listW D O' (2 ^ 24 + 5) (thr k)).card ≤ 2 ^ 40) (O : Word K 6) :
    dens (fun p : Fin 6 → K × K => ¬ GoodS (1 / 2 ^ 119) D (2 ^ 24 + 5) thr ladder0
      (2 ^ 137 * (2 ^ 137 - 1) * (2 ^ 137 - 2 ^ 129)) 6 O p) ≤ 1 / 2 ^ 110 := by
  have h := dens_not_goodS_le (τ := 1 / 2 ^ 119) (D := D) (d := 2 ^ 24 + 5) (thr := thr)
    (bt := ladder0) (B := 2 ^ 137 * (2 ^ 137 - 1) * (2 ^ 137 - 2 ^ 129)) (by norm_num)
    (by norm_num : 1 ≤ 6) hL O 6
  rw [hq] at h
  exact h.trans ladder_error_level0_arith

end Deployed

end Protocol
