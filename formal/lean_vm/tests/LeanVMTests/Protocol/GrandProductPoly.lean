/-
  LeanVMTests.Protocol.GrandProductPoly

  Regression controls for natural multiplicities and the collision count.
-/

module

public import LeanVM.Protocol.ToArkLib.GrandProductPoly
import Mathlib.Algebra.Field.ZMod

/-!
# Grand-product controls

Natural multiplicities remain visible in characteristic two. A collision at one evaluation
point is compatible with symbolic injectivity, and in dimension zero the collision count is
attained: a singleton and the empty multiset agree at exactly one of the two points. A `β`
correlated with a fingerprint coordinate makes unequal multisets agree everywhere, so the
count needs the point's coordinates independent. The sixteen-coordinate factor contributes
degree four, including the product challenge.
-/

namespace LeanVMTests.Protocol

open LeanVM.Protocol CompPoly CMlPolynomialEval

@[expose] public section

-- In dimension zero `{0}` and `∅` agree at the point `1`.
example : MvPolynomial.eval (fun _ : Option (Fin 0) ↦ (1 : ZMod 2))
      (grandProductPoly ({#v[0]} : Multiset (CMlPolynomialEval (ZMod 2) 0))) =
    MvPolynomial.eval (fun _ : Option (Fin 0) ↦ (1 : ZMod 2))
      (grandProductPoly (0 : Multiset (CMlPolynomialEval (ZMod 2) 0))) := by
  simp [grandProductPoly, fingerprintFactorPoly, fingerprintPoly]

example (t : CMlPolynomialEval (ZMod 2) 4) :
    grandProductPoly ({t, t} : Multiset _) ≠ grandProductPoly (0 : Multiset _) := by
  intro h
  have hc := congrArg Multiset.card (grandProductPoly_injective h)
  simp at hc

example (t : CMlPolynomialEval (ZMod 2) 4) :
    grandProductPoly ({t} : Multiset _) ≠ grandProductPoly ({t, t} : Multiset _) := by
  intro h
  have hc := congrArg Multiset.card (grandProductPoly_injective h)
  simp at hc

example (t u : CMlPolynomialEval (ZMod 2) 4) (h : t[0] ≠ u[0]) :
    grandProductPoly ({t} : Multiset _) ≠ grandProductPoly ({u} : Multiset _) := by
  intro hp
  have ht : t = u := by simpa using grandProductPoly_injective hp
  exact h (congrArg (fun v : CMlPolynomialEval (ZMod 2) 4 ↦ v[0]) ht)

-- Correlating beta with a fingerprint coordinate can make unequal multisets always collide.
example (a : ZMod 2) :
    MvPolynomial.eval (fun i : Option (Fin 1) ↦ i.elim a (fun _ ↦ a))
        (grandProductPoly ({#v[0, 1]} : Multiset (CMlPolynomialEval (ZMod 2) 1))) =
      MvPolynomial.eval (fun i : Option (Fin 1) ↦ i.elim a (fun _ ↦ a))
        (grandProductPoly ({#v[0, 1], #v[0, 1]} :
          Multiset (CMlPolynomialEval (ZMod 2) 1))) := by
  simp [grandProductPoly, fingerprintFactorPoly, fingerprintPoly, Fin.sum_univ_succ]

example {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (M N : Multiset (CMlPolynomialEval F 4)) {cap : ℕ}
    (hM : M.card ≤ cap) (hN : N.card ≤ cap) :
    (grandProductPoly M - grandProductPoly N).totalDegree ≤ 4 * cap :=
  totalDegree_grandProduct_difference_le M N hM hN

-- The empty product is the identity in both representations, including dimension zero.
example {R : Type*} [CommRing R] :
    grandProductPoly (0 : Multiset (CMlPolynomialEval R 0)) = 1 ∧
      grandProductUnivariate (0 : Multiset (CMlPolynomialEval R 0)) = 1 := by
  simp [grandProductPoly, grandProductUnivariate]

-- A zero-dimensional mixed-ring evaluation is still an ordinary product in the beta variable.
example : MvPolynomial.eval₂ (Int.castRingHom ℚ) (fun _ : Option (Fin 0) ↦ (11 : ℚ))
    (grandProductPoly ({#v[(2 : ℤ)], #v[5]} : Multiset (CMlPolynomialEval ℤ 0))) = 54 := by
  calc
    _ = (({#v[(2 : ℤ)], #v[5]} : Multiset (CMlPolynomialEval ℤ 0)).map
        fun t ↦ (11 : ℚ) - eval₂Mle t (Int.castRingHom ℚ) #v[]).prod := by
      have hpoint : (fun i : Option (Fin 0) ↦
          i.elim (11 : ℚ) (fun j ↦ (#v[] : Vector ℚ 0)[j])) = (fun _ ↦ 11) := by
        funext i
        cases i with
        | none => rfl
        | some j => exact Fin.elim0 j
      simpa only [hpoint] using eval₂_grandProductPoly
        ({#v[(2 : ℤ)], #v[5]} : Multiset (CMlPolynomialEval ℤ 0)) (Int.castRingHom ℚ) #v[] 11
    _ = 54 := by norm_num [eval₂Mle, CMlPolynomialEval.map]

-- Coefficient maps commute with products even when they erase source-coordinate distinctions.
example : MvPolynomial.map (Int.castRingHom (ZMod 2))
    (grandProductPoly ({#v[(0 : ℤ)], #v[2]} : Multiset (CMlPolynomialEval ℤ 0))) =
      grandProductPoly ({#v[0], #v[0]} : Multiset (CMlPolynomialEval (ZMod 2) 0)) := by
  have hzero : CMlPolynomialEval.map (n := 0) (Int.castRingHom (ZMod 2))
      (#v[(0 : ℤ)] : CMlPolynomialEval ℤ 0) = (#v[0] : CMlPolynomialEval (ZMod 2) 0) := by
    simp [CMlPolynomialEval.map]
  have htwo : CMlPolynomialEval.map (n := 0) (Int.castRingHom (ZMod 2))
      (#v[(2 : ℤ)] : CMlPolynomialEval ℤ 0) = (#v[0] : CMlPolynomialEval (ZMod 2) 0) := by
    apply Vector.ext
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simpa [CMlPolynomialEval.map] using (show (2 : ZMod 2) = 0 by decide)
  rw [map_grandProductPoly]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, hzero, htwo]

-- The collision count is attained in dimension zero: `{0}` and `∅` agree at one of the two
-- points, and the bound `max 1 0 · 1 · 2⁰` is `1`.
example : (Finset.univ.filter fun x : Option (Fin 0) → ZMod 2 ↦
      MvPolynomial.eval x (grandProductPoly ({#v[0]} : Multiset (CMlPolynomialEval (ZMod 2) 0))) =
        MvPolynomial.eval x (grandProductPoly (0 : Multiset (CMlPolynomialEval (ZMod 2) 0)))).card =
    max 1 0 * 1 * Fintype.card (ZMod 2) ^ 0 := by
  refine le_antisymm (card_grandProduct_collision_le _ _ (by simp) (by simp) (by simp)) ?_
  refine Finset.one_le_card.mpr ⟨fun _ ↦ 1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  simp [grandProductPoly, fingerprintFactorPoly, fingerprintPoly]

end
end LeanVMTests.Protocol
