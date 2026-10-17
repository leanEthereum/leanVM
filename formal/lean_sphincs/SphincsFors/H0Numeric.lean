import Mathlib

/-! Rational arithmetic for H-term certificates: Stirling rows by a linear list recursion, Touchard
sums, and the per-interval check and interval chain of the product-majorant certificate format. -/

namespace SphincsFors.Security.H0

/-! ### Stirling rows -/

/-- `[k x_0, (k+1) x_1, …]`. -/
def mulIdx : ℕ → List ℕ → List ℕ
  | _, [] => []
  | k, x :: xs => k * x :: mulIdx (k + 1) xs

/-- Pointwise sum with zero padding. -/
def addLists : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => (x + y) :: addLists xs ys

/-- Next Stirling row: `S(n+1, j) = j S(n, j) + S(n, j-1)`. -/
def stirNext (row : List ℕ) : List ℕ := addLists (mulIdx 0 row) (0 :: row)

/-- The row `S(n, 0..n)` of Stirling numbers of the second kind. -/
def stirRow : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => stirNext (stirRow n)

theorem mulIdx_getD : ∀ (l : List ℕ) (k j : ℕ), (mulIdx k l).getD j 0 = (k + j) * l.getD j 0
  | [], k, j => by simp [mulIdx]
  | x :: xs, k, 0 => by simp [mulIdx]
  | x :: xs, k, j + 1 => by
      simp only [mulIdx, List.getD_cons_succ, mulIdx_getD xs (k + 1) j]
      ring_nf

theorem addLists_getD : ∀ (a b : List ℕ) (j : ℕ), (addLists a b).getD j 0 = a.getD j 0 + b.getD j 0
  | [], b, j => by simp [addLists]
  | x :: xs, [], j => by simp [addLists]
  | x :: xs, y :: ys, 0 => by simp [addLists]
  | x :: xs, y :: ys, j + 1 => by
      simp only [addLists, List.getD_cons_succ]
      exact addLists_getD xs ys j

theorem mulIdx_length : ∀ (l : List ℕ) (k : ℕ), (mulIdx k l).length = l.length
  | [], _ => rfl
  | x :: xs, k => by simp [mulIdx, mulIdx_length xs (k + 1)]

theorem addLists_length : ∀ (a b : List ℕ), (addLists a b).length = max a.length b.length
  | [], b => by simp [addLists]
  | x :: xs, [] => by simp [addLists]
  | x :: xs, y :: ys => by simp [addLists, addLists_length xs ys, Nat.succ_max_succ]

theorem stirRow_length : ∀ n, (stirRow n).length = n + 1
  | 0 => rfl
  | n + 1 => by
      simp only [stirRow, stirNext, addLists_length, mulIdx_length, List.length_cons, stirRow_length n]
      omega

theorem stirRow_getD : ∀ n j, (stirRow n).getD j 0 = Nat.stirlingSecond n j
  | 0, 0 => rfl
  | 0, j + 1 => by simp [stirRow]
  | n + 1, 0 => by
      simp only [stirRow, stirNext, addLists_getD, mulIdx_getD, List.getD_cons_zero]
      simp
  | n + 1, j + 1 => by
      simp only [stirRow, stirNext, addLists_getD, mulIdx_getD, List.getD_cons_succ, stirRow_getD n,
        Nat.stirlingSecond_succ_succ]
      ring

/-! ### Touchard sums -/

/-- `touchGo l μ p = p Σ_j l_j μ^j`. -/
def touchGo : List ℕ → ℚ → ℚ → ℚ
  | [], _, _ => 0
  | s :: l, μ, p => (s : ℚ) * p + touchGo l μ (p * μ)

theorem touchGo_eq : ∀ (l : List ℕ) (μ p : ℚ),
    touchGo l μ p = p * ∑ j ∈ Finset.range l.length, (l.getD j 0 : ℚ) * μ ^ j
  | [], _, _ => by simp [touchGo]
  | s :: l, μ, p => by
      rw [touchGo, touchGo_eq l μ (p * μ), List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      rw [add_comm]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => by ring
      · ring

/-- Touchard polynomial `T_n(μ) = Σ_j S(n,j) μ^j`, computed from the Stirling row. -/
def touchQ (n : ℕ) (μ : ℚ) : ℚ := touchGo (stirRow n) μ 1

theorem touchQ_eq (n : ℕ) (μ : ℚ) :
    touchQ n μ = ∑ j ∈ Finset.range (n + 1), (Nat.stirlingSecond n j : ℚ) * μ ^ j := by
  rw [touchQ, touchGo_eq, one_mul, stirRow_length]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [stirRow_getD]

/-! ### The interval check -/

/-- Upper bound for the Poisson rate at the right end `qb` of an interval. -/
def muExactQ (b N qb R : ℕ) : ℚ :=
  ((N : ℚ) / 2 ^ b) * (1 + 2 ^ 26 / ((2 : ℚ) ^ 128 - qb - 2 ^ 32)) ^ (24 * R) *
    (1 + ((N : ℚ) * 2 ^ (26 - b) + qb) / ((2 : ℚ) ^ 128 - qb - 2 ^ 32))

/-- Lower bound for the baseline at the right end of an interval. -/
def betaQ (qb : ℕ) : ℚ := ((2 : ℚ) ^ 128 - 2 * qb) / (((2 : ℚ) ^ 128 - qb) * 2 ^ 127)

/-- Poisson mean of the per-leaf factor `(1 + 2^e 2^-266 k^24)^R`. -/
def PQ (R e : ℕ) (μ : ℚ) : ℚ :=
  ∑ s ∈ Finset.range (R + 1), (R.choose s : ℚ) * ((2 : ℚ) ^ e / 2 ^ 266) ^ s * touchQ (24 * s) μ

/-- `c_R = (R-1)^(R-1) / R^R`. -/
def cRQ (R : ℕ) : ℚ := ((R - 1 : ℕ) : ℚ) ^ (R - 1) / (R : ℚ) ^ R

/-- Prefactor `c_R / (t^R β^(R-1))`. -/
def AQ (R e : ℕ) (β : ℚ) : ℚ := cRQ R / (((2 : ℚ) ^ e) ^ R * β ^ (R - 1))

/-- A certificate entry: `(qa, qb, R, e, m)` with `t = 2^e` and rate bound `m / 2^64`. -/
abbrev Entry := ℕ × ℕ × ℕ × ℕ × ℕ

end SphincsFors.Security.H0
