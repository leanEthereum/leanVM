import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Tactic

namespace Whir.RingSwitch

open scoped BigOperators

variable {E : Type*} [CommRing E]

/-- Bit multiplication is selection, so an additive map suffices; E-linearity is not assumed. -/
def bit (b : Bool) : E := if b then 1 else 0

theorem map_bit_mul (φ : E →+ E) (b : Bool) (x : E) :
    φ (bit b * x) = bit b * φ x := by
  cases b <;> simp [bit]

/-- The six stages in Annex A act additively, not E-linearly. -/
def stage [CharP E 2] (f : E) (shift : ℕ) : E →+ E where
  toFun a := a + f * a ^ (2 ^ shift)
  map_zero' := by simp
  map_add' a b := by
    rw [add_pow_char_pow, mul_add]
    abel

/-- The production shift order is 32,16,8,4,2,1. -/
def composedMap [CharP E 2] (challenges : Fin 6 → E) : E →+ E :=
  (List.finRange 6).foldl
    (fun φ p => (stage (challenges p) (2 ^ (5 - p.val))).comp φ)
    (AddMonoidHom.id E)

theorem composedMap_add [CharP E 2] (challenges : Fin 6 → E) (a b : E) :
    composedMap challenges (a + b) = composedMap challenges a + composedMap challenges b :=
  map_add _ _ _

variable {I U J : Type*} [Fintype I] [Fintype U] [Fintype J]

/-- Packed words, with the choice of basis explicit. The application uses 64 powers of x. -/
def packed (basis : I → E) (bits : I → U → Bool) (u : U) : E :=
  ∑ i, bit (bits i u) * basis i

/-- A slice evaluation, including an arbitrary claim's point weight. -/
def slice (weight : U → E) (bits : I → U → Bool) (i : I) : E :=
  ∑ u, bit (bits i u) * weight u

/-- Annex A equation (complete), for any additive map and any honest bit slices. -/
theorem honest_ring_switch (φ : E →+ E) (basis : I → E)
    (bits : I → U → Bool) (weight : U → E) :
    (∑ i, basis i * φ (slice weight bits i)) =
      ∑ u, φ (weight u) * packed basis bits u := by
  simp only [slice, packed, map_sum, map_bit_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The family target applies the map after batching the slices. -/
def familyTarget (φ : E →+ E) (basis : I → E)
    (scales : J → E) (slices : J → I → E) : E :=
  ∑ i, basis i * φ (∑ j, scales j * slices j i)

/-- Arbitrary points and repeated regions are allowed. Scales stay inside φ. -/
theorem honest_family (φ : E →+ E) (basis : I → E)
    (bits : J → I → U → Bool) (weights : J → U → E) (scales : J → E) :
    familyTarget φ basis scales (fun j => slice (weights j) (bits j)) =
      ∑ j, ∑ u, φ (scales j * weights j u) * packed basis (bits j) u := by
  unfold familyTarget
  simp only [map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have hs (i : I) : scales j * slice (weights j) (bits j) i =
      slice (fun u => scales j * weights j u) (bits j) i := by
    simp only [slice, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring
  simp_rw [hs]
  exact honest_ring_switch φ basis (bits j) (fun u => scales j * weights j u)

/-- Stack placements are injections individually; overlapping regions add their weights. -/
def placeWeight {V : Type*} [Fintype V] [DecidableEq V]
    (positions : U → V) (w : U → E) (v : V) : E :=
  ∑ u, if positions u = v then w u else 0

theorem stacked_claim {V : Type*} [Fintype V] [DecidableEq V]
    (positions : J → U → V) (weights : J → U → E) (stack : V → E) :
    (∑ v, (∑ j, placeWeight (positions j) (weights j) v) * stack v) =
      ∑ j, ∑ u, weights j u * stack (positions j u) := by
  simp only [placeWeight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp

/-- Padding outside every claim's support cannot change the stacked claim. -/
theorem padding_noninterference {V : Type*} [Fintype V] [DecidableEq V]
    (positions : J → U → V) (weights : J → U → E) (stack padded : V → E)
    (agree : ∀ j u, padded (positions j u) = stack (positions j u)) :
    (∑ v, (∑ j, placeWeight (positions j) (weights j) v) * padded v) =
      ∑ v, (∑ j, placeWeight (positions j) (weights j) v) * stack v := by
  rw [stacked_claim, stacked_claim]
  simp_rw [agree]

end Whir.RingSwitch
