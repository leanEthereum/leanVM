/-
  LeanVM.Protocol.ToArkLib.Whir.AffineCombinerDeployed

  A Boolean check of one fold round's interpolation parameters, as the Rust's `combiner_within`
  checks them, and its soundness: the parameters are admissible and the round's escape count
  `q · nAff + 2 L q²` is at most `budget · q²`.
-/

module

public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerParams

/-!
# Checking a fold round

Round `j` (`1 ≤ j ≤ k`) of a level with `κ` message variables, rate exponent `R`, `k` fold rounds
and final threshold `Aend` is analysed (Annex B, `thm:rbr`) on `n = 2^(κ+R)` points at the level's
final degree `d = 2^κ - 1 + k` and threshold `A = Aend - (k - j)` (`roundN`, `roundD`, `roundA`).
`foldRoundOK κ R k Aend j m D B budget` checks, in natural numbers:

* `Admissible n d A m D B` and `n d < (A - 1)²`;
* `n (n - 1) / 2 ≤ q` with `q = 2^128` (`qE`), so `max(q, C(n, 2)) = q`;
* `jl n B (d + 1) + 2 jl n (A - 1) d ≤ budget`;
* `D² (A - B)² + 4 d² M² D³ n² ≤ (budget - jl n B (d + 1) - 2 jl n (A - 1) d) q (A - B)²`,
  `crates/pcs/src/whir_config/affine_mca.rs`, `combiner_within`, exactly.

`foldRoundOK_sound`: a passing round has `Admissible`, `n d < (A - 1)²`, and the fold row `q · nAff + 2 jl n (A - 1) d q² ≤ budget q²`
(in `ℚ`), which with `card_foldBad_le_nAff_of_lemma43` bounds the round's escapes by
`budget · q²`, a probability of `budget / q`.
-/

namespace LeanVM.Protocol.Whir.AffineCombiner

open Finset

@[expose] public section

/-- `|E| = 2^128`. -/
abbrev qE : ℕ := 2 ^ 128

/-- The block length `2^(κ + R)`. -/
def roundN (κ R : ℕ) : ℕ := 2 ^ (κ + R)

/-- The degree bound of every round of a level of `k` folds, `2^κ - 1 + k`. -/
def roundD (κ k : ℕ) : ℕ := 2 ^ κ - 1 + k

/-- Round `j`'s threshold `Aend - (k - j)`. -/
def roundA (k Aend j : ℕ) : ℕ := Aend - (k - j)

/-! ## Closed forms of the interpolation sums -/

/-- Six times `Σ_{j ≤ N} (c - d j)(e - j)`, in closed form. -/
def sixSum (c d e N : ℕ) : ℤ :=
  6 * c * e * (N + 1) + d * N * (N + 1) * (2 * N + 1) - 3 * (c + d * e) * N * (N + 1)

/-- The closed form of `Σ_{j ≤ N} (c - d j)(e - j)` when every term is a product of naturals. -/
theorem six_mul_sum_eq (c d e N : ℕ) (hc : d * N ≤ c) (he : N ≤ e) :
    6 * ((∑ j ∈ range (N + 1), (c - d * j) * (e - j) : ℕ) : ℤ) = sixSum c d e N := by
  induction N with
  | zero => simp [sixSum]; ring
  | succ N ih =>
    rw [sum_range_succ, Nat.cast_add, mul_add, ih (le_trans (Nat.mul_le_mul_left _
      (Nat.le_succ N)) hc) (by omega), Nat.cast_mul, Nat.cast_sub hc, Nat.cast_sub he]
    simp only [sixSum]
    push_cast
    ring

/-- `Admissible`, with the interpolation sums in closed form. -/
def admissibleFast (n d A m D B : ℕ) : Bool :=
  let M := bigM d A m D
  decide (1 ≤ d) && decide (A ≤ n) && decide (1 ≤ m) && decide (1 ≤ M) &&
    decide ((n : ℤ) * sixSum m 1 (D + 1) (min (m - 1) M) < sixSum (m * A - D) d (D + 1) M) &&
    decide (d + 1 < B) && decide (B < A) && decide (n * (d + 1) < B * B)

theorem admissible_of_fast {n d A m D B : ℕ} (h : admissibleFast n d A m D B = true) :
    Admissible n d A m D B := by
  simp only [admissibleFast, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hd, hAn⟩, hm⟩, hM⟩, hineq⟩, hB1⟩, hBA⟩, hB2⟩ := h
  refine ⟨hd, hAn, hm, hM, ?_, hB1, hBA, hB2⟩
  set M := bigM d A m D
  have hMD : M ≤ D := min_le_left _ _
  have hdM : d * M ≤ m * A - D := by
    have : M ≤ (m * A - D - 1) / d := min_le_right _ _
    have h2 := Nat.mul_le_mul_left d this
    have h3 := Nat.mul_div_le (m * A - D - 1) d
    omega
  have hU : 6 * ((unknowns d A m D : ℕ) : ℤ) = sixSum (m * A - D) d (D + 1) M := by
    have hs : unknowns d A m D =
        ∑ j ∈ range (M + 1), (m * A - D - d * j) * (D + 1 - j) := by
      refine sum_congr rfl fun j hj ↦ ?_
      have : j ≤ D := (Nat.lt_succ_iff.mp (mem_range.mp hj)).trans hMD
      congr 1
      omega
    rw [hs]
    exact six_mul_sum_eq _ _ _ _ hdM (by omega)
  set N := min (m - 1) M
  have hNM : N ≤ M := min_le_right _ _
  have hE : 6 * ((equations n d A m D : ℕ) : ℤ) = n * sixSum m 1 (D + 1) N := by
    have hs : ∑ s ∈ range (N + 1), (m - s) * (D - s + 1) =
        ∑ s ∈ range (N + 1), (m - 1 * s) * (D + 1 - s) := by
      refine sum_congr rfl fun s hs ↦ ?_
      have : s ≤ D := (Nat.lt_succ_iff.mp (mem_range.mp hs)).trans (hNM.trans hMD)
      rw [one_mul]
      congr 1
      omega
    rw [equations, Nat.cast_mul, ← mul_assoc, mul_comm 6, mul_assoc, hs,
      six_mul_sum_eq _ _ _ _ (by have := min_le_left (m - 1) M; omega) (by omega)]
  have : 6 * ((equations n d A m D : ℕ) : ℤ) < 6 * ((unknowns d A m D : ℕ) : ℤ) := by
    rw [hU, hE]; exact hineq
  exact_mod_cast (lt_of_mul_lt_mul_left this (by norm_num))

/-- **The check of one fold round**, as the Rust's `check_fold_round`. -/
def foldRoundOK (κ R k Aend j m D B budget : ℕ) : Bool :=
  let n := roundN κ R
  let d := roundD κ k
  let A := roundA k Aend j
  admissibleFast n d A m D B && decide (n * d < (A - 1) * (A - 1)) &&
    decide (n * (n - 1) / 2 ≤ qE) &&
    decide (jl n B (d + 1) + 2 * jl n (A - 1) d ≤ budget) &&
    decide (D ^ 2 * (A - B) ^ 2 + 4 * d ^ 2 * bigM d A m D ^ 2 * D ^ 3 * n ^ 2 ≤
      (budget - jl n B (d + 1) - 2 * jl n (A - 1) d) * qE * (A - B) ^ 2)

/-- **Soundness of the round check**: admissibility, the Johnson hypothesis, and the fold row
`q · nAff + 2 jl n (A - 1) d q² ≤ budget q²`. -/
theorem foldRoundOK_sound {κ R k Aend j m D B budget : ℕ}
    (h : foldRoundOK κ R k Aend j m D B budget = true) :
    Admissible (roundN κ R) (roundD κ k) (roundA k Aend j) m D B ∧
      roundN κ R * roundD κ k < (roundA k Aend j - 1) * (roundA k Aend j - 1) ∧
      (qE : ℚ) * nAff qE (roundN κ R) (roundD κ k) (roundA k Aend j) m D B +
          2 * jl (roundN κ R) (roundA k Aend j - 1) (roundD κ k) * (qE : ℚ) ^ 2 ≤
        budget * (qE : ℚ) ^ 2 := by
  simp only [foldRoundOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hfast, hgap⟩, hchoose⟩, hbud⟩, hcomb⟩ := h
  have hadm := admissible_of_fast hfast
  set n := roundN κ R
  set d := roundD κ k
  set A := roundA k Aend j
  set M := bigM d A m D
  set lB := jl n B (d + 1)
  set lA := jl n (A - 1) d
  refine ⟨hadm, hgap, ?_⟩
  have hBA : B < A := hadm.2.2.2.2.2.2.1
  have hmax : max qE (n.choose 2) = qE := by
    rw [Nat.choose_two_right]; exact max_eq_left hchoose
  have hAB : (0 : ℚ) < ((A - B : ℕ) : ℚ) := by exact_mod_cast Nat.sub_pos_of_lt hBA
  -- `(D² + 4 d² M² D³ (n/(A-B))²) ≤ (budget - lB - 2 lA) q`.
  have hrest : nAffRest n d A m D B ≤ ((budget - lB - 2 * lA : ℕ) : ℚ) * qE := by
    unfold nAffRest
    have hc : ((D ^ 2 * (A - B) ^ 2 + 4 * d ^ 2 * M ^ 2 * D ^ 3 * n ^ 2 : ℕ) : ℚ) ≤
        (((budget - lB - 2 * lA) * qE * (A - B) ^ 2 : ℕ) : ℚ) := by exact_mod_cast hcomb
    push_cast at hc
    rw [div_pow, ← sub_nonneg]
    have key : ((budget - lB - 2 * lA : ℕ) : ℚ) * (qE : ℚ) - ((D : ℚ) ^ 2 +
        4 * (d : ℚ) ^ 2 * (M : ℚ) ^ 2 * (D : ℚ) ^ 3 * ((n : ℚ) ^ 2 / ((A - B : ℕ) : ℚ) ^ 2)) =
        (((budget - lB - 2 * lA : ℕ) : ℚ) * (qE : ℚ) * ((A - B : ℕ) : ℚ) ^ 2 -
          ((D : ℚ) ^ 2 * ((A - B : ℕ) : ℚ) ^ 2 + 4 * (d : ℚ) ^ 2 * (M : ℚ) ^ 2 * (D : ℚ) ^ 3 *
            (n : ℚ) ^ 2)) / ((A - B : ℕ) : ℚ) ^ 2 := by
      field_simp
    rw [key]
    exact div_nonneg (by push_cast; linarith) (by positivity)
  have hsub : ((budget - lB - 2 * lA : ℕ) : ℚ) = (budget : ℚ) - lB - 2 * lA := by
    rw [Nat.sub_sub, Nat.cast_sub hbud]; push_cast; ring
  rw [hsub] at hrest
  unfold nAff nAffPersistent
  rw [hmax]
  have hq : (0 : ℚ) ≤ (qE : ℚ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hrest hq
  push_cast at hmul ⊢
  nlinarith

end

end LeanVM.Protocol.Whir.AffineCombiner
