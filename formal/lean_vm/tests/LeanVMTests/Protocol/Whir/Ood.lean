/-
  LeanVMTests.Protocol.Whir.Ood

  Out-of-domain collision counts for tables on two variables over `ZMod 5`.
-/

import LeanVM.Protocol.ToArkLib.Whir.Ood
import Mathlib.Algebra.Field.ZMod

/-!
# Out-of-domain separation controls

The tables of `0` and of `x₀ x₁` on two variables over `ZMod 5` have equal extensions at the
`9` points with `x₀ = 0` or `x₁ = 0`, within the bound `κ |F|^(κ-1) = 2 · 5 = 10`. The tables of
`0` and `x₀` on one variable meet at the single point `0`, attaining the bound `1 · 5⁰ = 1`.
A three-table list collides at at most `C(3, 2) · 10 = 30` of the `25` points.

**Negative control.** Equal tables agree at all `25` points, beyond `10`: the distinctness
hypothesis of `card_evalMle_eq_le` is load-bearing.
-/

namespace LeanVMTests.Protocol.Whir

open LeanVM.Protocol.Whir Finset CompPoly CMlPolynomialEval

private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

private def zero2 : CMlPolynomialEval (ZMod 5) 2 := #v[0, 0, 0, 0]
private def prod2 : CMlPolynomialEval (ZMod 5) 2 := #v[0, 0, 0, 1]
private def x0 : CMlPolynomialEval (ZMod 5) 2 := #v[0, 1, 0, 1]

#guard (univ.filter fun z : Vector (ZMod 5) 2 ↦ evalMle zero2 z = evalMle prod2 z).card = 9
#guard (univ.filter fun z : Vector (ZMod 5) 1 ↦
  evalMle (#v[0, 0] : CMlPolynomialEval (ZMod 5) 1) z = evalMle #v[0, 1] z).card = 1
#guard (univ.filter fun z : Vector (ZMod 5) 2 ↦
  ∃ g ∈ ({zero2, prod2, x0} : Finset (CMlPolynomialEval (ZMod 5) 2)),
    ∃ g' ∈ ({zero2, prod2, x0} : Finset (CMlPolynomialEval (ZMod 5) 2)),
      g ≠ g' ∧ evalMle g z = evalMle g' z).card = 13
-- Negative control: equal tables meet everywhere.
#guard (univ.filter fun z : Vector (ZMod 5) 2 ↦ evalMle prod2 z = evalMle prod2 z).card = 25

example : (univ.filter fun z : Vector (ZMod 5) 2 ↦ evalMle zero2 z = evalMle prod2 z).card ≤
    2 * Fintype.card (ZMod 5) ^ (2 - 1) :=
  card_evalMle_eq_le fun h ↦ by
    have := congrArg (·[3]) h
    simp [zero2, prod2] at this

example (L : Finset (CMlPolynomialEval (ZMod 5) 2)) :
    (univ.filter fun z : Vector (ZMod 5) 2 ↦
      ∃ g ∈ L, ∃ g' ∈ L, g ≠ g' ∧ evalMle g z = evalMle g' z).card ≤
    L.card.choose 2 * (2 * Fintype.card (ZMod 5) ^ (2 - 1)) :=
  card_ood_collision_le L

/-- **Negative control.** Without distinctness the Schwartz-Zippel count fails. -/
example : ¬ ∀ g g' : CMlPolynomialEval (ZMod 5) 2,
    (univ.filter fun z : Vector (ZMod 5) 2 ↦ evalMle g z = evalMle g' z).card ≤
      2 * Fintype.card (ZMod 5) ^ (2 - 1) := by
  intro h
  have h1 := h prod2 prod2
  have hall : (univ.filter fun z : Vector (ZMod 5) 2 ↦ evalMle prod2 z = evalMle prod2 z) =
      univ := by simp
  rw [hall, Finset.card_univ, card_vector_eq_pow, ZMod.card] at h1
  norm_num at h1

end LeanVMTests.Protocol.Whir
