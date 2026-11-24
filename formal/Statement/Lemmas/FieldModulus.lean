/-
  Statement.Lemmas.FieldModulus

  `y^2 + x·y + 1` is irreducible over `GF(2^64)`: the law `Statement/Field.lean` needs to make
  `E = K[y]/(y^2 + x·y + 1)` a field. Proved here, on CompPoly's `BF64`, so that a reviewer of
  `Statement/` reads only its statement (`ePoly_irreducible`, `Field.lean`).
-/

module

public import CompPoly.Fields.Binary.BF64

@[expose] public section

namespace LeanVM.Parameters.FieldModulus

open Polynomial

/-- `t ↦ Σ_{i < n} t^(2^i)` from `acc`, by repeated squaring: what the kernel evaluates. -/
def traceIter : ℕ → BF64 → BF64 → BF64
  | 0, _, acc => acc
  | n + 1, t, acc => traceIter n (t * t) (acc + t)

theorem traceIter_eq (n : ℕ) (t acc : BF64) :
    traceIter n t acc = acc + ∑ i ∈ Finset.range n, t ^ 2 ^ i := by
  induction n generalizing t acc with
  | zero => simp [traceIter]
  | succ n ih =>
    rw [traceIter, ih, Finset.sum_range_succ', pow_zero, pow_one, add_assoc, add_comm t]
    congr 2
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← sq, ← pow_mul, pow_succ, mul_comm]

/-- `x⁻¹ = x^63 + x^3 + x^2 + 1`, as `x · (x^63 + x^3 + x^2 + 1) = x^64 + x^4 + x^3 + x = 1`. -/
theorem x_mul_inv_word :
    BF64.ofBitVec (BitVec.ofNat 64 2) * BF64.ofBitVec (BitVec.ofNat 64 0x800000000000000D) = 1 := by
  decide +kernel

/-- The absolute trace of `x^-2` is one. -/
theorem traceIter_inv_sq :
    traceIter 64 (BF64.ofBitVec (BitVec.ofNat 64 0x800000000000000D) *
      BF64.ofBitVec (BitVec.ofNat 64 0x800000000000000D)) 0 = 1 := by
  decide +kernel

/-- In characteristic two the trace of `t^2 + t` vanishes: it telescopes to `t^(2^64) + t`. -/
theorem trace_sq_add_self (t : BF64) : ∑ i ∈ Finset.range 64, (t ^ 2 + t) ^ 2 ^ i = 0 := by
  let := Fintype.ofFinite BF64
  have hadd : ∀ i : ℕ, (t ^ 2 + t) ^ 2 ^ i = t ^ 2 ^ (i + 1) + t ^ 2 ^ i := fun i ↦ by
    rw [add_pow_char_pow, ← pow_mul, ← pow_succ']
  have tel : ∀ n : ℕ, ∑ i ∈ Finset.range n, (t ^ 2 ^ (i + 1) + t ^ 2 ^ i) = t ^ 2 ^ n + t := by
    intro n
    induction n with
    | zero => simp [CharTwo.add_self_eq_zero]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      calc t ^ 2 ^ n + t + (t ^ 2 ^ (n + 1) + t ^ 2 ^ n)
          = t ^ 2 ^ (n + 1) + t + (t ^ 2 ^ n + t ^ 2 ^ n) := by ring
        _ = t ^ 2 ^ (n + 1) + t := by rw [CharTwo.add_self_eq_zero, add_zero]
  have hq : t ^ 2 ^ 64 = t := by
    have := FiniteField.pow_card t
    rwa [BF64.card_bf64] at this
  simp only [hadd]
  rw [tel, hq, CharTwo.add_self_eq_zero]

/-- `y^2 + x·y + 1` has no root in `GF(2^64)`: a root `a` gives `t = a/x` with `t^2 + t = x^-2`,
whose trace is then zero, while the kernel computes it to be one. -/
theorem no_root (a : BF64) :
    ¬ (X ^ 2 + C (BF64.ofBitVec (BitVec.ofNat 64 2)) * X + 1 : Polynomial BF64).IsRoot a := by
  intro h
  have ha : a ^ 2 + BF64.ofBitVec (BitVec.ofNat 64 2) * a + 1 = 0 := by
    simpa [Polynomial.IsRoot] using h
  set gi : BF64 := BF64.ofBitVec (BitVec.ofNat 64 0x800000000000000D)
  have hg : BF64.ofBitVec (BitVec.ofNat 64 2) * gi = 1 := x_mul_inv_word
  have key : (a * gi) ^ 2 + a * gi + gi * gi = 0 := by
    calc (a * gi) ^ 2 + a * gi + gi * gi
        = (a ^ 2 + BF64.ofBitVec (BitVec.ofNat 64 2) * a + 1) * (gi * gi) := by
          linear_combination (-(a * gi)) * hg
      _ = 0 := by rw [ha, zero_mul]
  have ht : (a * gi) ^ 2 + a * gi = gi * gi := by
    rwa [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at key
  have h0 := trace_sq_add_self (a * gi)
  rw [ht] at h0
  have h1 := traceIter_inv_sq
  rw [traceIter_eq, zero_add] at h1
  rw [h1] at h0
  exact one_ne_zero h0

/-- **`y^2 + x·y + 1` is irreducible over `GF(2^64)`.** -/
theorem irreducible :
    Irreducible (X ^ 2 + C (BF64.ofBitVec (BitVec.ofNat 64 2)) * X + 1 : Polynomial BF64) := by
  have hdeg : (X ^ 2 + C (BF64.ofBitVec (BitVec.ofNat 64 2)) * X + 1 : Polynomial BF64).natDegree =
      2 := by compute_degree!
  exact Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) no_root

end LeanVM.Parameters.FieldModulus
