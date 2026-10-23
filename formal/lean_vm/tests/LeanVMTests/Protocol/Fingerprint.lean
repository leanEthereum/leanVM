/-
  LeanVMTests.Protocol.Fingerprint

  Regression controls for symbolic fingerprints and the separate product challenge.
-/

module

public import LeanVM.Protocol.ToCompPoly.Fingerprint
import Mathlib.Algebra.Field.ZMod
import LeanVM.Protocol.Field

/-!
# Fingerprint controls

The actual sixteen-coordinate shape has degree four. A change in the domain-separator
coordinate produces a different symbolic polynomial, without a characteristic assumption.
-/

namespace LeanVMTests.Protocol

open LeanVM.Protocol CompPoly CMlPolynomialEval

@[expose] public section

example {R : Type*} [CommRing R] (t : CMlPolynomialEval R 4) :
    (fingerprintPoly t).totalDegree ≤ 4 := totalDegree_fingerprintPoly t

example {R : Type*} [CommRing R] (t u : CMlPolynomialEval R 4)
    (h : t[0] ≠ u[0]) : fingerprintPoly t ≠ fingerprintPoly u := by
  intro hp
  exact h (congrArg (fun v : CMlPolynomialEval R 4 ↦ v[0]) (fingerprintPoly_injective hp))

example {R : Type*} [CommRing R] (t : CMlPolynomialEval R 4) :
    MvPolynomial.eval (fun j ↦ (boolVec (0 : Fin 16) : Vector R 4)[j])
      (fingerprintPoly t) = t[(0 : Fin 16)] := eval_fingerprintPoly_boolVec t 0

-- The product challenge is separate: four fingerprint variables still give joint degree four.
example {R : Type*} [CommRing R] (t : CMlPolynomialEval R 4) :
    (fingerprintFactorPoly t).totalDegree ≤ 4 := totalDegree_fingerprintFactorPoly t

-- An asymmetric off-cube point distinguishes evaluation from Boolean coordinate selection.
example : MvPolynomial.eval (fun _ : Fin 1 ↦ (2 : ℚ))
    (fingerprintPoly (#v[2, 5] : CMlPolynomialEval ℚ 1)) = 8 := by
  calc
    _ = eval₂Mle (#v[2, 5] : CMlPolynomialEval ℚ 1) (RingHom.id ℚ) #v[2] := by
      simpa using eval₂_fingerprintPoly (#v[2, 5] : CMlPolynomialEval ℚ 1) (RingHom.id ℚ) #v[2]
    _ = 8 := by norm_num [eval₂Mle, CMlPolynomialEval.map, Vector.head]

example : MvPolynomial.eval (fun i : Option (Fin 1) ↦ i.elim (11 : ℚ) (fun _ ↦ 2))
    (fingerprintFactorPoly (#v[2, 5] : CMlPolynomialEval ℚ 1)) = 3 := by
  calc
    _ = 11 - eval₂Mle (#v[2, 5] : CMlPolynomialEval ℚ 1) (RingHom.id ℚ) #v[2] := by
      simpa using eval₂_fingerprintFactorPoly (#v[2, 5] : CMlPolynomialEval ℚ 1)
        (RingHom.id ℚ) #v[2] 11
    _ = 3 := by norm_num [eval₂Mle, CMlPolynomialEval.map, Vector.head]

-- Low bit first is observable at an asymmetric point in two dimensions.
example : MvPolynomial.eval (fun j : Fin 2 ↦ (#v[(2 : ℚ), 3] : Vector ℚ 2)[j])
    (fingerprintPoly (#v[2, 5, 7, 13] : CMlPolynomialEval ℚ 2)) = 41 := by
  calc
    _ = eval₂Mle (#v[2, 5, 7, 13] : CMlPolynomialEval ℚ 2)
        (RingHom.id ℚ) #v[2, 3] := eval₂_fingerprintPoly _ _ _
    _ = 41 := by norm_num [eval₂Mle, CMlPolynomialEval.map, Vector.head]

example : MvPolynomial.eval (fun j : Fin 2 ↦ (#v[(3 : ℚ), 2] : Vector ℚ 2)[j])
    (fingerprintPoly (#v[2, 5, 7, 13] : CMlPolynomialEval ℚ 2)) = 39 := by
  calc
    _ = eval₂Mle (#v[2, 5, 7, 13] : CMlPolynomialEval ℚ 2)
        (RingHom.id ℚ) #v[3, 2] := eval₂_fingerprintPoly _ _ _
    _ = 39 := by norm_num [eval₂Mle, CMlPolynomialEval.map, Vector.head]

-- At dimension zero the fingerprint is constant, but the separate product variable survives.
example : fingerprintPoly (n := 0) (#v[(7 : ℚ)] : CMlPolynomialEval ℚ 0) =
    MvPolynomial.C (7 : ℚ) := by
  simp [fingerprintPoly]

example : MvPolynomial.eval (fun _ : Option (Fin 0) ↦ (11 : ℚ))
    (fingerprintFactorPoly (#v[7] : CMlPolynomialEval ℚ 0)) = 4 := by
  norm_num [fingerprintFactorPoly, fingerprintPoly]

-- Map/evaluation compatibility does not require an injective coefficient map.
example : MvPolynomial.map (Int.castRingHom (ZMod 2))
    (fingerprintPoly (#v[(2 : ℤ), 5] : CMlPolynomialEval ℤ 1)) =
      fingerprintPoly (n := 1) (#v[0, 1] : CMlPolynomialEval (ZMod 2) 1) := by
  rw [map_fingerprintPoly]
  congr 1
  apply Vector.ext
  intro i hi
  interval_cases i
  · simpa [CMlPolynomialEval.map] using (show (2 : ZMod 2) = 0 by decide)
  · simpa [CMlPolynomialEval.map] using (show (5 : ZMod 2) = 1 by decide)

-- Noninjective maps can identify distinct source fingerprints; the injectivity premise matters.
example : fingerprintPoly (n := 0) (#v[(0 : ℤ)] : CMlPolynomialEval ℤ 0) ≠
      fingerprintPoly (n := 0) (#v[2] : CMlPolynomialEval ℤ 0) ∧
    MvPolynomial.map (Int.castRingHom (ZMod 2))
        (fingerprintPoly (n := 0) (#v[(0 : ℤ)] : CMlPolynomialEval ℤ 0)) =
      MvPolynomial.map (Int.castRingHom (ZMod 2))
        (fingerprintPoly (n := 0) (#v[(2 : ℤ)] : CMlPolynomialEval ℤ 0)) := by
  constructor
  · intro h
    have hzero := congrArg (fun t : CMlPolynomialEval ℤ 0 ↦ t[0])
      (fingerprintPoly_injective h)
    norm_num at hzero
  · rw [map_fingerprintPoly, map_fingerprintPoly]
    congr 1
    apply Vector.ext
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simpa [CMlPolynomialEval.map] using (show (0 : ZMod 2) = 2 by decide)

-- Inequality transport only needs a semiring source, so natural-number tuples are supported.
example {n : ℕ} {t u : CMlPolynomialEval ℕ n} (htu : t ≠ u) :
    fingerprintPoly (CMlPolynomialEval.map (Nat.castRingHom ℤ) t) ≠
      fingerprintPoly (CMlPolynomialEval.map (Nat.castRingHom ℤ) u) :=
  mapped_fingerprint_ne (Nat.castRingHom ℤ) Nat.cast_injective htu

-- The symbolic polynomial stays over K while its evaluation and separate challenge are in E.
example {n : ℕ} (t : CMlPolynomialEval LeanVM.Parameters.K n)
    (z : Vector LeanVM.Parameters.E n) (β : LeanVM.Parameters.E) :
    MvPolynomial.eval₂ (algebraMap LeanVM.Parameters.K LeanVM.Parameters.E)
      (fun i ↦ i.elim β (fun j ↦ z[j])) (fingerprintFactorPoly t) =
      β - eval₂Mle t (algebraMap LeanVM.Parameters.K LeanVM.Parameters.E) z :=
  eval₂_fingerprintFactorPoly _ _ _ _

end
end LeanVMTests.Protocol
