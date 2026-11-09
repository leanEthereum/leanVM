/-
Copyright (c) 2026 leanerVM Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Derived-source notice:
Copyright (c) 2026 Leanth Contributors. All rights reserved.
-/

/-
  LeanVM.Protocol.ToCompPoly.PowerBatching

  Power batching of weighted claims, with exponents starting at zero.
-/

module

public import LeanVM.Protocol.ToCompPoly.Multilinear
public import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Power batching

A family of `J` values or tables is combined with powers `ρ^j`, starting at zero.
The difference polynomial has degree at most `J - 1`. A false singleton remains false
at every challenge, including zero. The empty family is handled separately.

Candidate for CompPoly: finite power combinations, their multilinear table pairing and
extension, and the finite-field root count. The values are fixed before the challenge is
chosen.

Derived from the zero-based scalar-batching results in Verified-zkEVM/leanth at
23929f8c922cd4461ab22dbfaa6520f3ad23a3b2, by Aristotle (Harmonic), Stefano Rocca and
Elias Judin: `Leanth/ProofSystem/ZeroCheck.lean:670-697`, `scalarBatch_rejection` and
`scalarBatch_eq_zero`. The current API takes separate actual and claimed values, exposes the
difference polynomial, and includes the empty case. `Leanth/ProofSystem/Stacking.lean:779-804`
uses positive powers in `BatchedAccepts` and `batchPoly`; that distinct convention has an
additional automatic root at zero and a `J` bound.

-/

namespace LeanVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {R : Type*} [CommRing R] {J μ : ℕ}

/-- A finite power combination, with coefficient zero weighted by one. -/
def powerBatch (a : Fin J → R) (ρ : R) : R := ∑ j : Fin J, a j * ρ ^ j.val

/-- Batch weight tables pointwise with the same powers as their targets. -/
def batchWeight (w : Fin J → CMlPolynomialEval R μ) (ρ : R) : CMlPolynomialEval R μ :=
  Vector.ofFn fun x ↦ powerBatch (fun j ↦ (w j)[x]) ρ

/-- Pairing is linear in a family of weights on the same arbitrary committed column. -/
theorem pairing_batchWeight (w : Fin J → CMlPolynomialEval R μ)
    (q : CMlPolynomialEval R μ) (ρ : R) :
    sumCube (hadamard (batchWeight w ρ) q) =
      powerBatch (fun j ↦ sumCube (hadamard (w j) q)) ρ := by
  simp only [sumCube, hadamard, batchWeight, Fin.getElem_fin, Vector.getElem_ofFn, powerBatch]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_right_comm _ (ρ ^ _) _]

/-- Multilinear extension commutes with power batching, at every point, including off the cube. -/
theorem evalMle_batchWeight (w : Fin J → CMlPolynomialEval R μ) (ρ : R) (r : Vector R μ) :
    evalMle (batchWeight w ρ) r = powerBatch (fun j ↦ evalMle (w j) r) ρ := by
  simp only [evalMle_eq_sum, batchWeight, Fin.getElem_fin, Vector.getElem_ofFn, powerBatch]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_right_comm _ (ρ ^ _) _]

/-- The polynomial whose coefficients are the differences of the individual claims. -/
noncomputable def batchDifference (a v : Fin J → R) : Polynomial R :=
  ∑ j : Fin J, Polynomial.monomial j.val (a j - v j)

/-- The coefficient at index `j` is precisely the difference of claim `j`. -/
theorem coeff_batchDifference (a v : Fin J → R) (j : Fin J) :
    (batchDifference a v).coeff j.val = a j - v j := by
  classical
  simp [batchDifference, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Fin.val_inj]

/-- A false component makes the difference polynomial nonzero. -/
theorem batchDifference_ne_zero (a v : Fin J → R) (h : ∃ j, a j ≠ v j) :
    batchDifference a v ≠ 0 := by
  obtain ⟨j, hj⟩ := h
  intro hp
  have hc := coeff_batchDifference a v j
  rw [hp, Polynomial.coeff_zero] at hc
  exact hj (sub_eq_zero.mp hc.symm)

/-- Evaluation of the difference polynomial is the difference of the two batches. -/
theorem eval_batchDifference (a v : Fin J → R) (ρ : R) :
    (batchDifference a v).eval ρ = powerBatch a ρ - powerBatch v ρ := by
  simp [batchDifference, powerBatch, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, Finset.sum_sub_distrib]

/-- The zero polynomial convention makes the same natural-degree bound valid when `J = 0`. -/
theorem natDegree_batchDifference_le (a v : Fin J → R) :
    (batchDifference a v).natDegree ≤ J - 1 := by
  unfold batchDifference
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ ↦ ?_
  exact (Polynomial.natDegree_monomial_le (a j - v j)).trans (by have := j.isLt; omega)

/-- A false singleton has no successful challenge; a zero challenge cannot erase its error. -/
theorem singleton_batch_ne (a v : Fin 1 → R) (h : a 0 ≠ v 0) (ρ : R) :
    powerBatch a ρ ≠ powerBatch v ρ := by
  simpa [powerBatch] using h

section FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- At most `J - 1` challenges make a false family appear true after power batching. -/
theorem card_false_batch_le (a v : Fin J → F) (h : ∃ j, a j ≠ v j) :
    (Finset.univ.filter fun ρ ↦ powerBatch a ρ = powerBatch v ρ).card ≤ J - 1 := by
  have hp := batchDifference_ne_zero a v h
  calc
    _ ≤ (batchDifference a v).roots.toFinset.card := by
      apply Finset.card_le_card
      intro ρ hρ
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]
      exact (eval_batchDifference a v ρ).trans
        (sub_eq_zero.mpr (Finset.mem_filter.mp hρ).2)
    _ ≤ (batchDifference a v).roots.card := Multiset.toFinset_card_le _
    _ ≤ (batchDifference a v).natDegree := Polynomial.card_roots' _
    _ ≤ J - 1 := natDegree_batchDifference_le a v

end FiniteField

end
end LeanVM.Protocol
