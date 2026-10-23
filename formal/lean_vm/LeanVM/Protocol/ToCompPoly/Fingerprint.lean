/-
Copyright (c) 2026 leanerVM Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Derived-source notice:
Copyright (c) 2026 Leanth Contributors. All rights reserved.
-/

/-
  LeanVM.Protocol.ToCompPoly.Fingerprint

  Symbolic fingerprints of hypercube tables over arbitrary commutative rings.
-/

module

public import LeanVM.Protocol.ToCompPoly.Multilinear
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Multilinear fingerprints

Candidate for CompPoly: the symbolic multilinear extension of a hypercube value table,
with coordinate `j` reading the low-order bit `j`. Evaluation agrees with CompPoly's
mixed-ring evaluator. No base/extension-field protocol assembly is defined here.

Derived from Verified-zkEVM/leanth at 23929f8c922cd4461ab22dbfaa6520f3ad23a3b2,
by Aristotle (Harmonic), Stefano Rocca and Elias Judin,
`Leanth/ProofSystem/Logup.lean:275-444`: `fingerprintPoly`, `eval_fingerprintPoly`,
`fingerprintPoly_injective`, and `totalDegree_fingerprintPoly`. The original notice above
is retained for this derived algebra. No logarithmic derivative or
characteristic-versus-multiplicity assumption enters this module.

The fingerprint has `n` variables. The grand-product challenge is a separate polynomial
variable over this coefficient ring, so it cannot be confused with a fingerprint coordinate.
-/

namespace LeanVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

/-- The symbolic multilinear extension of a tuple, with little-endian Boolean indexing. -/
noncomputable def fingerprintPoly (t : CMlPolynomialEval R n) : MvPolynomial (Fin n) R :=
  ∑ i : Fin (2 ^ n), MvPolynomial.C t[i] *
    ∏ j : Fin n, if i.val.testBit j.val then MvPolynomial.X j else 1 - MvPolynomial.X j

/-- Symbolic evaluation agrees with the actual CompPoly mixed-ring multilinear evaluator. -/
theorem eval₂_fingerprintPoly (t : CMlPolynomialEval R n) (φ : R →+* S)
    (z : Vector S n) :
    MvPolynomial.eval₂ φ (fun j ↦ z[j]) (fingerprintPoly t) = eval₂Mle t φ z := by
  rw [eval₂Mle, evalMle_eq_sum]
  simp [fingerprintPoly, CMlPolynomialEval.map, lagrangeBasis_getElem_nat, apply_ite]

/-- Boolean evaluation reads the corresponding input coordinate, in every characteristic. -/
theorem eval_fingerprintPoly_boolVec (t : CMlPolynomialEval R n) (i : Fin (2 ^ n)) :
    MvPolynomial.eval (fun j ↦ (boolVec i : Vector R n)[j]) (fingerprintPoly t) = t[i] := by
  have h := eval₂_fingerprintPoly t (RingHom.id R) (boolVec i)
  simpa [eval₂Mle, CMlPolynomialEval.map, evalMle_boolVec] using h

/-- Distinct tuples give distinct symbolic fingerprints; no field hypothesis is needed. -/
theorem fingerprintPoly_injective :
    Function.Injective (fingerprintPoly (R := R) (n := n)) := by
  intro t u h
  apply Vector.ext
  intro i hi
  have ht := eval_fingerprintPoly_boolVec t ⟨i, hi⟩
  have hu := eval_fingerprintPoly_boolVec u ⟨i, hi⟩
  rw [h] at ht
  simpa only [Fin.getElem_fin] using ht.symm.trans hu

/-- Each Boolean basis factor has degree at most one, so the total degree is at most `n`. -/
theorem totalDegree_fingerprintPoly (t : CMlPolynomialEval R n) :
    (fingerprintPoly t).totalDegree ≤ n := by
  classical
  nontriviality R using (Subsingleton.elim (fingerprintPoly t) 0)
  unfold fingerprintPoly
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
  refine Finset.sup_le fun i _ ↦ ?_
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc
    _ ≤ ∑ _j : Fin n, 1 := by
      apply Finset.sum_le_sum
      intro j _
      split
      · simp
      · refine (MvPolynomial.totalDegree_sub _ _).trans ?_
        simp
    _ = n := by simp

/-- Coefficient mapping commutes with fingerprints, including noninjective maps. -/
theorem map_fingerprintPoly (t : CMlPolynomialEval R n) (φ : R →+* S) :
    MvPolynomial.map φ (fingerprintPoly t) =
      fingerprintPoly (CMlPolynomialEval.map φ t) := by
  classical
  simp [fingerprintPoly, CMlPolynomialEval.map, apply_ite]

/-- Reflecting inequality after a coefficient map needs the map's injectivity. -/
theorem mapped_fingerprint_ne {R S : Type*} [Semiring R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Injective φ)
    {t u : CMlPolynomialEval R n} (htu : t ≠ u) :
    fingerprintPoly (CMlPolynomialEval.map φ t) ≠
      fingerprintPoly (CMlPolynomialEval.map φ u) := by
  exact fun h ↦ htu ((Vector.map_inj_right fun _ _ h ↦ hφ h).mp
    (fingerprintPoly_injective h))

/-- A grand-product factor with a distinct formal challenge at `none`; the fingerprint
coordinates occupy `some j`. -/
noncomputable def fingerprintFactorPoly (t : CMlPolynomialEval R n) :
    MvPolynomial (Option (Fin n)) R :=
  MvPolynomial.X none - MvPolynomial.rename some (fingerprintPoly t)

/-- The extra formal variable evaluates to the grand-product challenge. -/
theorem eval₂_fingerprintFactorPoly (t : CMlPolynomialEval R n) (φ : R →+* S)
    (z : Vector S n) (β : S) :
    MvPolynomial.eval₂ φ (fun i ↦ i.elim β (fun j ↦ z[j])) (fingerprintFactorPoly t) =
      β - eval₂Mle t φ z := by
  rw [fingerprintFactorPoly, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_X,
    MvPolynomial.eval₂_rename]
  exact congrArg (β - ·) (eval₂_fingerprintPoly t φ z)

/-- Adding the separate grand-product challenge gives joint degree at most `max 1 n`, not
`n + 1`. -/
theorem totalDegree_fingerprintFactorPoly (t : CMlPolynomialEval R n) :
    (fingerprintFactorPoly t).totalDegree ≤ max 1 n := by
  classical
  nontriviality R using (Subsingleton.elim (fingerprintFactorPoly t) 0)
  refine (MvPolynomial.totalDegree_sub _ _).trans ?_
  apply max_le_max
  · simp
  · exact (MvPolynomial.totalDegree_rename_le some (fingerprintPoly t)).trans
      (totalDegree_fingerprintPoly t)

end
end LeanVM.Protocol
