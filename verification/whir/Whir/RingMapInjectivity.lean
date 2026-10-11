import Whir.RingSwitch
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Frobenius pairing injectivity

A direct root-count version of Annex A's transpose argument. Raising the `k`th
zero pairing to `2^(n-k)` makes every error coefficient acquire the same power
`2^n`. The resulting degree-at-most-`n` polynomial has the `n+1` distinct
Frobenius conjugates of `x` as roots. This works over the extension field itself,
so coefficients need not lie in the binary base field or its degree-64 extension;
in particular no cubic-coordinate independence assumption is necessary.
-/
namespace Whir.RingMapInjectivity

open scoped BigOperators

variable {E : Type*} [Field E] [CharP E 2]

/-- The coefficient of the `k`th Frobenius term in an erroneous ring-switch target. -/
def pairing {n : ℕ} (x : E) (δ : Fin (n + 1) → E) (k : Fin (n + 1)) : E :=
  ∑ i, x ^ i.val * δ i ^ (2 ^ k.val)

/-- Distinct conjugates suffice even when the errors lie in an arbitrary extension. -/
theorem eq_zero_of_pairings_eq_zero {n : ℕ} (x : E)
    (conjugates : Function.Injective (fun k : Fin (n + 1) => x ^ (2 ^ k.val)))
    (δ : Fin (n + 1) → E) (h : ∀ k, pairing x δ k = 0) : δ = 0 := by
  classical
  let p : Polynomial E := ∑ i : Fin (n + 1),
    Polynomial.monomial i.val (δ i ^ (2 ^ n))
  have heval (k : Fin (n + 1)) : p.eval (x ^ (2 ^ k.val)) = 0 := by
    let r : Fin (n + 1) := ⟨n - k.val, by omega⟩
    have hr : r.val + k.val = n := by dsimp [r]; omega
    have hp := congrArg (fun a : E => a ^ (2 ^ k.val)) (h r)
    rw [zero_pow (by positivity)] at hp
    simp only [pairing, sum_pow_char_pow, mul_pow, ← pow_mul,
      ← Nat.pow_add, hr] at hp
    simpa only [p, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
      ← pow_mul, Nat.mul_comm, mul_comm] using hp
  have hdegree : p.natDegree ≤ n := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    exact (Polynomial.natDegree_monomial_le _).trans (by omega)
  have hp : p = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    p conjugates heval (by simpa using Nat.lt_succ_of_le hdegree)
  funext i
  have hc := congrArg (fun q : Polynomial E => q.coeff i.val) hp
  simpa [p, Polynomial.coeff_monomial, ← Fin.ext_iff] using hc

/-- The whole Frobenius pairing map is injective, not merely nonzero on errors. -/
theorem pairing_injective {n : ℕ} (x : E)
    (conjugates : Function.Injective (fun k : Fin (n + 1) => x ^ (2 ^ k.val))) :
    Function.Injective (pairing (n := n) x) := by
  intro δ ε heq
  have hz : δ - ε = 0 := eq_zero_of_pairings_eq_zero x conjugates (δ - ε) (by
    intro k
    have hk := congrFun heq k
    simpa only [pairing, Pi.sub_apply, sub_pow_char_pow, mul_sub,
      Finset.sum_sub_distrib, sub_eq_zero] using hk)
  exact sub_eq_zero.mp hz

/-- The 64-term endpoint consumed by the actual six-stage map discrepancy proof. -/
theorem exists_nonzero_pairing (x : E)
    (conjugates : Function.Injective (fun k : Fin 64 => x ^ (2 ^ k.val)))
    (δ : Fin 64 → E) (hne : δ ≠ 0) :
    ∃ k : Fin 64, (∑ i : Fin 64, x ^ i.val * δ i ^ (2 ^ k.val)) ≠ 0 := by
  by_contra! h
  exact hne (eq_zero_of_pairings_eq_zero (n := 63) x conjugates δ h)

omit [CharP E 2] in
/-- Field embeddings preserve the exact conjugate-distinctness prerequisite. -/
theorem conjugates_map {K : Type*} [Field K] {n : ℕ} (φ : K →+* E) (x : K)
    (conjugates : Function.Injective (fun k : Fin (n + 1) => x ^ (2 ^ k.val))) :
    Function.Injective (fun k : Fin (n + 1) => φ x ^ (2 ^ k.val)) := by
  intro k l h
  apply conjugates
  apply φ.injective
  simpa only [map_pow] using h

/-- Base-field powers are embedded before multiplying arbitrary extension-field errors. -/
theorem exists_nonzero_pairing_over_base {K : Type*} [Field K] (φ : K →+* E) (x : K)
    (conjugates : Function.Injective (fun k : Fin 64 => x ^ (2 ^ k.val)))
    (δ : Fin 64 → E) (hne : δ ≠ 0) :
    ∃ k : Fin 64, (∑ i : Fin 64, φ (x ^ i.val) * δ i ^ (2 ^ k.val)) ≠ 0 := by
  simpa only [map_pow] using
    exists_nonzero_pairing (φ x) (conjugates_map (n := 63) φ x conjugates) δ hne

end Whir.RingMapInjectivity
