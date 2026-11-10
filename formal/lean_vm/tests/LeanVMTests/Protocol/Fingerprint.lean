/-
  LeanVMTests.Protocol.Fingerprint

  Regression controls for symbolic linear fingerprints and the separate product challenge.
-/

module

public import LeanVM.Protocol.ToCompPoly.Fingerprint
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

/-!
# Fingerprint controls

The sixteen-slot fingerprint has degree one, its product factor too. A change in the
domain-separator slot produces a different symbolic polynomial, without a characteristic
assumption. Evaluation weighs slot `i` by coordinate `i`.
-/

namespace LeanVMTests.Protocol

open LeanVM.Protocol

@[expose] public section

example {R : Type*} [CommRing R] (t : Vector R 16) : (fingerprintPoly t).totalDegree ≤ 1 :=
  totalDegree_fingerprintPoly t

example {R : Type*} [CommRing R] (t : Vector R 16) :
    (fingerprintFactorPoly t).totalDegree ≤ 1 := totalDegree_fingerprintFactorPoly t

example {R : Type*} [CommRing R] (t u : Vector R 16) (h : t[0] ≠ u[0]) :
    fingerprintPoly t ≠ fingerprintPoly u := by
  intro hp
  exact h (congrArg (fun v : Vector R 16 ↦ v[0]) (fingerprintPoly_injective hp))

-- Slot `i` is weighed by coordinate `i`: `3·2 + 7·5`, not `3·5 + 7·2`.
example : MvPolynomial.eval ![(3 : ℚ), 7] (fingerprintPoly (#v[2, 5] : Vector ℚ 2)) = 41 := by
  rw [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, eval₂_fingerprintPoly]
  norm_num [Fin.sum_univ_two]

example : MvPolynomial.eval (fun i : Option (Fin 2) ↦ i.elim (50 : ℚ) ![3, 7])
    (fingerprintFactorPoly (#v[2, 5] : Vector ℚ 2)) = 9 := by
  rw [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, eval₂_fingerprintFactorPoly]
  norm_num [Fin.sum_univ_two]

-- Noninjective coefficient maps can identify distinct fingerprints.
example : fingerprintPoly (#v[(0 : ℤ)] : Vector ℤ 1) ≠ fingerprintPoly #v[(2 : ℤ)] ∧
    MvPolynomial.map (Int.castRingHom (ZMod 2)) (fingerprintPoly (#v[(0 : ℤ)] : Vector ℤ 1)) =
      MvPolynomial.map (Int.castRingHom (ZMod 2)) (fingerprintPoly (#v[(2 : ℤ)] : Vector ℤ 1)) := by
  constructor
  · intro h
    have := congrArg (fun v : Vector ℤ 1 ↦ v[0]) (fingerprintPoly_injective h)
    norm_num at this
  · rw [map_fingerprintPoly, map_fingerprintPoly]
    congr 1
    apply Vector.ext
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simpa using (show (0 : ZMod 2) = 2 by decide)

end
end LeanVMTests.Protocol
