module

public import FORS.CoverBound.SecondMoment
public import Mathlib.Data.List.GetD

@[expose] public section

/-! **Rational upper bounds of the per-tree moments.** The closed forms of `Ψ1(n)` and `Ψ2(n)`
(`CoverBound/FirstMoment`, `CoverBound/SecondMoment`) are exact fractions over `A^n` and `A^(n+1)`,
`A = 2^a` the number of leaves of a FORS tree. The kernel computes their numerators over `2^128`,
rounded up (`cdiv`): for `Ψ2`, whose numerator is an alternating sum, in `ℕ` and proved equal to the
rounding in `ℤ` (`p2N_eq`). -/

open ENNReal

namespace FORS.Security.H0

set_option linter.unusedSectionVars false

/-! ### Lists over a range -/

theorem getD_map_range {α : Type} (f : ℕ → α) (d : α) (N i : ℕ) (hi : i < N) :
    ((List.range N).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]

/-- A sum over `range` as a list sum. -/
theorem list_sum_range {M : Type} [AddCommMonoid M] (f : ℕ → M) : ∀ n,
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => rfl
  | n + 1 => by
      rw [List.range_succ, List.map_append, List.sum_append, list_sum_range f n,
        Finset.sum_range_succ]
      simp

/-! ### Rounding up -/

/-- `⌈a / b⌉`. -/
def cdiv (a b : ℕ) : ℕ := (a + b - 1) / b

theorem self_le_cdiv_mul (a b : ℕ) (hb : 0 < b) : a ≤ cdiv a b * b := by
  unfold cdiv
  have h1 := Nat.lt_div_mul_add (a := a + b - 1) hb
  have h2 := Nat.div_mul_le_self (a + b - 1) b
  generalize (a + b - 1) / b = q at *
  omega

theorem le_cdiv {a b : ℕ} (hb : 0 < b) : (a : ℝ) / b ≤ (cdiv a b : ℝ) := by
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast self_le_cdiv_mul a b hb

/-- The quotient of two naturals, below its numerator rounded up over `2^128`. -/
theorem div_le_cdiv_div {x d : ℕ} (hd : 0 < d) :
    (x : ℝ) / d ≤ ((cdiv (2 ^ 128 * x) d : ℕ) : ℝ) / 2 ^ 128 := by
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 128)]
  calc (x : ℝ) / d * 2 ^ 128 = ((2 ^ 128 * x : ℕ) : ℝ) / d := by push_cast; ring
    _ ≤ _ := le_cdiv hd

/-- `⌈x / y⌉` for `y > 0`. -/
def cdivZ (x y : ℤ) : ℤ := -((-x) / y)

theorem le_cdivZ {x y : ℤ} (hy : 0 < y) : (x : ℚ) / y ≤ cdivZ x y := by
  have h := Int.ediv_mul_le (-x) (ne_of_gt hy)
  have h' : x ≤ cdivZ x y * y := by unfold cdivZ; linarith
  rw [div_le_iff₀ (by exact_mod_cast hy)]
  exact_mod_cast h'

theorem cdivZ_natCast (a b : ℕ) (hb : 0 < b) : cdivZ a b = (cdiv a b : ℤ) := by
  unfold cdivZ cdiv
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  have h1 := Nat.div_add_mod (a + b - 1) b
  have h2 := Nat.mod_lt (a + b - 1) hb
  have h3 : ((a + b - 1 : ℕ) : ℤ) = a + b - 1 := by omega
  have h1' : (b : ℤ) * ((a + b - 1) / b : ℕ) + ((a + b - 1) % b : ℕ) = a + b - 1 := by
    rw [← h3]; exact_mod_cast h1
  have h2' : (((a + b - 1) % b : ℕ) : ℤ) < b := by exact_mod_cast h2
  have h4 : (0 : ℤ) ≤ (((a + b - 1) % b : ℕ) : ℤ) := by positivity
  have key : -(a : ℤ) / b = -(((a + b - 1) / b : ℕ) : ℤ) := by
    rw [Int.ediv_eq_iff_of_pos hb']
    constructor <;> nlinarith
  rw [key, neg_neg]

theorem cdivZ_eq_ceil (n : ℤ) (d : ℕ) : cdivZ n d = ⌈(n / d : ℚ)⌉ := by
  rw [Rat.ceil_intCast_div_natCast]; rfl

/-- `q ≤ ⌈x / y⌉ / 2^P` once `q 2^P = x / y`. -/
theorem le_cdivZ_div {q : ℚ} {x y : ℤ} {P : ℕ} (hy : 0 < y) (h : q * 2 ^ P = x / y) :
    q ≤ (cdivZ x y : ℚ) / 2 ^ P := by
  rw [le_div_iff₀ (by positivity), h]
  exact le_cdivZ hy

/-- The quotient of two integers, below its numerator rounded up over `2^128`. -/
theorem div_le_cdivZ_div {x d : ℤ} (hd : 0 < d) :
    (x : ℝ) / d ≤ (((cdivZ (2 ^ 128 * x) d).toNat : ℕ) : ℝ) / 2 ^ 128 := by
  set y : ℤ := 2 ^ 128 * x with hy
  have h : (y : ℚ) / d ≤ (cdivZ y d : ℚ) := le_cdivZ hd
  have h' : (y : ℝ) / d ≤ ((cdivZ y d : ℤ) : ℝ) := by exact_mod_cast h
  have h'' : ((cdivZ y d : ℤ) : ℝ) ≤ (((cdivZ y d).toNat : ℕ) : ℝ) := by
    exact_mod_cast Int.self_le_toNat (cdivZ y d)
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 128)]
  calc (x : ℝ) / d * 2 ^ 128 = (y : ℝ) / d := by rw [hy]; push_cast; ring
    _ ≤ _ := le_trans h' h''

/-! ### The numerators of the moments -/

/-- The numerator over `2^128` of the bound of `Ψ1(n)`, for trees of height `a`. -/
def p1N (a n : ℕ) : ℕ := cdiv (2 ^ 128 * ((2 ^ a) ^ n - (2 ^ a - 1) ^ n)) ((2 ^ a) ^ n)

/-- The exact numerator of `Ψ2(n)` over `A^(n+1)`, `A = 2^a`. -/
def z2N (a n : ℕ) : ℤ :=
  (2 ^ a : ℤ) ^ (n + 1) - 2 * 2 ^ a * (2 ^ a - 1) ^ n + (2 ^ a - 1) ^ n +
    (2 ^ a - 1) * (2 ^ a - 2) ^ n

/-- The numerator over `2^128` of the bound of `Ψ2(n)`, for trees of height `a`: `z2N` rounded up, computed
in `ℕ` (`p2N_eq`). -/
def p2N (a n : ℕ) : ℕ :=
  cdiv (2 ^ 128 * ((2 ^ a) ^ (n + 1) + (2 ^ a - 1) ^ n + (2 ^ a - 1) * (2 ^ a - 2) ^ n - 2 * 2 ^ a * (2 ^ a - 1) ^ n))
    ((2 ^ a) ^ (n + 1))

theorem p2N_eq {a : ℕ} (ha : 1 ≤ a) (n : ℕ) :
    p2N a n = (cdivZ (2 ^ 128 * z2N a n) ((2 ^ a : ℤ) ^ (n + 1))).toNat := by
  have hA : 2 ≤ 2 ^ a := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) ha)
  set X := (2 ^ a) ^ (n + 1) + (2 ^ a - 1) ^ n + (2 ^ a - 1) * (2 ^ a - 2) ^ n
  set Y := 2 * 2 ^ a * (2 ^ a - 1) ^ n
  have hz : z2N a n = (X : ℤ) - Y := by
    simp only [z2N, X, Y]
    push_cast [Nat.cast_sub (show 1 ≤ 2 ^ a by omega), Nat.cast_sub hA]
    ring
  have hD : 0 < (2 ^ a) ^ (n + 1) := by positivity
  have hD' : ((2 ^ a : ℤ) ^ (n + 1)) = (((2 ^ a) ^ (n + 1) : ℕ) : ℤ) := by push_cast; rfl
  unfold p2N
  rw [hz, hD']
  rcases le_total Y X with h | h
  · rw [show (2 : ℤ) ^ 128 * ((X : ℤ) - Y) = ((2 ^ 128 * (X - Y) : ℕ) : ℤ) by push_cast [Nat.cast_sub h]; ring,
      cdivZ_natCast _ _ hD, Int.toNat_natCast]
  · rw [Nat.sub_eq_zero_of_le h, Nat.mul_zero]
    have h0 : cdivZ ((2 : ℤ) ^ 128 * ((X : ℤ) - Y)) (((2 ^ a) ^ (n + 1) : ℕ) : ℤ) ≤ 0 := by
      unfold cdivZ
      have : 0 ≤ -((2 : ℤ) ^ 128 * ((X : ℤ) - Y)) := by
        have : (X : ℤ) ≤ Y := by exact_mod_cast h
        nlinarith
      have := Int.ediv_nonneg this (by positivity : (0 : ℤ) ≤ (((2 ^ a) ^ (n + 1) : ℕ) : ℤ))
      omega
    rw [Int.toNat_of_nonpos h0]
    unfold cdiv
    exact Nat.div_eq_of_lt (by omega)

/-- The bound of `Ψ1(n)`. -/
def P1Q (a n : ℕ) : ℚ := (p1N a n : ℚ) / 2 ^ 128

/-- The bound of `Ψ2(n)`. -/
def P2Q (a n : ℕ) : ℚ := (p2N a n : ℚ) / 2 ^ 128

/-! ### Soundness -/

variable [Params]

open Concrete

/-- `Ψ1(n) = (A^n - (A-1)^n) / A^n`. -/
theorem Ψ1R_frac (n : ℕ) :
    Ψ1R n = (((2 ^ forsHeight) ^ n - (2 ^ forsHeight - 1) ^ n : ℕ) : ℝ) /
      (((2 ^ forsHeight) ^ n : ℕ) : ℝ) := by
  have hL : leavesR ≠ 0 := ne_of_gt leavesR_pos
  have hA : 1 ≤ 2 ^ forsHeight := Nat.one_le_two_pow
  have hnum : (((2 ^ forsHeight) ^ n - (2 ^ forsHeight - 1) ^ n : ℕ) : ℝ) =
      leavesR ^ n - (leavesR - 1) ^ n := by
    simp only [leavesR]
    push_cast [Nat.cast_sub (Nat.pow_le_pow_left (Nat.sub_le (2 ^ forsHeight) 1) n),
      Nat.cast_sub hA]
    ring
  have hden : (((2 ^ forsHeight) ^ n : ℕ) : ℝ) = leavesR ^ n := by
    simp only [leavesR]
    push_cast
    ring
  rw [hnum, hden, Ψ1R_eq, show (1 : ℝ) - 1 / leavesR = (leavesR - 1) / leavesR by field_simp,
    div_pow]
  field_simp

/-- `Ψ2(n) = z2(n) / A^(n+1)`. -/
theorem Ψ2R_frac (n : ℕ) :
    Ψ2R n = ((z2N forsHeight n : ℤ) : ℝ) / (((2 ^ forsHeight : ℤ) ^ (n + 1) : ℤ) : ℝ) := by
  have hL : leavesR ≠ 0 := ne_of_gt leavesR_pos
  have hden : (((2 ^ forsHeight : ℤ) ^ (n + 1) : ℤ) : ℝ) = leavesR ^ (n + 1) := by
    rw [leavesR]; push_cast; ring
  rw [hden, Ψ2R_eq, show (1 : ℝ) - 1 / leavesR = (leavesR - 1) / leavesR by field_simp,
    show (1 : ℝ) - 2 / leavesR = (leavesR - 2) / leavesR by field_simp, div_pow, div_pow, z2N]
  push_cast
  rw [show ((2 : ℝ) ^ forsHeight) = leavesR from rfl]
  field_simp
  ring

/-- **The first moment bound.** -/
theorem Ψ1R_le (n : ℕ) : Ψ1R n ≤ ((P1Q forsHeight n : ℚ) : ℝ) := by
  have hcast : ((P1Q forsHeight n : ℚ) : ℝ) = ((p1N forsHeight n : ℕ) : ℝ) / 2 ^ 128 := by
    rw [P1Q]; push_cast; ring
  rw [hcast, Ψ1R_frac, p1N]
  exact div_le_cdiv_div (by positivity)

/-- **The second moment bound.** -/
theorem Ψ2R_le (n : ℕ) : Ψ2R n ≤ ((P2Q forsHeight n : ℚ) : ℝ) := by
  have hcast : ((P2Q forsHeight n : ℚ) : ℝ) = ((p2N forsHeight n : ℕ) : ℝ) / 2 ^ 128 := by
    rw [P2Q]; push_cast; ring
  rw [hcast, Ψ2R_frac, p2N_eq (by have := Params.forsHeight_ge; omega)]
  exact div_le_cdivZ_div (by positivity)

end FORS.Security.H0
