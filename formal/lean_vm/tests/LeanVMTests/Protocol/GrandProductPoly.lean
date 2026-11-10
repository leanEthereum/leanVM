/-
  LeanVMTests.Protocol.GrandProductPoly

  Regression controls for natural multiplicities, padding leaves and the collision count.
-/

module

public import LeanVM.Protocol.ToArkLib.GrandProductPoly
import Mathlib.Algebra.Field.ZMod

/-!
# Grand-product controls

Natural multiplicities remain visible in characteristic two. In dimension zero the collision
count is attained: a singleton and the empty multiset agree at exactly one of the two points. A
`β` correlated with a fingerprint coordinate makes unequal multisets agree everywhere, so the
count needs the point's coordinates independent. A padding leaf is never zero, the zero tuple's
included, so a padded product still determines its tuples.
-/

namespace LeanVMTests.Protocol

open LeanVM.Protocol

@[expose] public section

example (t : Vector (ZMod 2) 16) :
    grandProductPoly ({t, t} : Multiset _) ≠ grandProductPoly (0 : Multiset _) := by
  intro h
  have hc := congrArg Multiset.card (grandProductPoly_injective h)
  simp at hc

example (t : Vector (ZMod 2) 16) :
    grandProductPoly ({t} : Multiset _) ≠ grandProductPoly ({t, t} : Multiset _) := by
  intro h
  have hc := congrArg Multiset.card (grandProductPoly_injective h)
  simp at hc

-- Correlating beta with a fingerprint coordinate can make unequal multisets always collide.
example (a : ZMod 2) :
    MvPolynomial.eval (fun i : Option (Fin 1) ↦ i.elim a fun _ ↦ a)
        (grandProductPoly ({#v[1]} : Multiset (Vector (ZMod 2) 1))) =
      MvPolynomial.eval (fun i : Option (Fin 1) ↦ i.elim a fun _ ↦ a)
        (grandProductPoly ({#v[1], #v[1]} : Multiset (Vector (ZMod 2) 1))) := by
  rw [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, eval₂_grandProductPoly, eval₂_grandProductPoly]
  simp

example {F : Type} [Field F] (M N : Multiset (Vector F 16)) {cap : ℕ}
    (hM : M.card ≤ cap) (hN : N.card ≤ cap) :
    (grandProductPoly M - grandProductPoly N).totalDegree ≤ cap :=
  totalDegree_grandProduct_difference_le M N hM hN

-- Padding by zero tuples, the honest rows, or by anything else keeps the tuples readable.
example (t u d : Vector (ZMod 2) 16) (h : t ≠ u) :
    paddedProductPoly {0, d} {t} ≠ paddedProductPoly {d, d} {u} := fun hp ↦
  h (by simpa using paddedProductPoly_eq hp)

-- The collision count is attained in dimension zero: `{()}` and `∅` agree at one of the two
-- points, and the bound `1 · 2⁰` is `1`.
example : (Finset.univ.filter fun x : Option (Fin 0) → ZMod 2 ↦
      MvPolynomial.eval x (grandProductPoly ({#v[]} : Multiset (Vector (ZMod 2) 0))) =
        MvPolynomial.eval x (grandProductPoly (0 : Multiset (Vector (ZMod 2) 0)))).card =
    1 * Fintype.card (ZMod 2) ^ 0 := by
  refine le_antisymm (card_grandProduct_collision_le _ _ (by simp) (by simp) (by simp)) ?_
  refine Finset.one_le_card.mpr ⟨fun _ ↦ 1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  simp [grandProductPoly, fingerprintFactorPoly, fingerprintPoly]

end
end LeanVMTests.Protocol
