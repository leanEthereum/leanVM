import KeccakGkr.Multilinear
import KeccakGkr.Keccak
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Lanes, positions, slots and instances on cubes

A lane is a point of `Cube 5`, a position `(ℓ, z)` the point of `Cube 11` of the number
`z + 64 ℓ` (the low six coordinates the slice, the high five the lane), the slot of lane `ℓ` of
segment `m` the point of `Cube 6` of `25 m + ℓ`, each number's bits low first. A table on lanes or
positions is padded with zeros to a table on the cube (`pad`).

The sixteen instances of a pack are the points of `Cube 4`, numbered the same way (`instEquiv`).
-/

namespace KeccakGkr

/-- The cube point of the bits of `m`, low first. -/
def cubeOf (k m : ℕ) : Cube k := fun i => m.testBit i

theorem cubeOf_injective {k a b : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k)
    (h : cubeOf k a = cubeOf k b) : a = b := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  by_cases hi : i < k
  · exact congrFun h ⟨i, hi⟩
  · have hk : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right two_pos (not_lt.mp hi)
    rw [Nat.testBit_lt_two_pow (ha.trans_le hk), Nat.testBit_lt_two_pow (hb.trans_le hk)]

/-- Lane `ℓ`, on `Cube 5`. -/
def laneCube (ℓ : Lane) : Cube 5 := cubeOf 5 ℓ.val

/-- Position `(ℓ, z)`, on `Cube 11`. -/
def posCube (j : Pos) : Cube 11 := cubeOf 11 (j.2.val + 64 * j.1.val)

/-- Lane `ℓ` of segment `m`'s committed input, on `Cube 6`. -/
def slotCube (m : Bool) (ℓ : Lane) : Cube 6 := cubeOf 6 (25 * m.toNat + ℓ.val)

theorem laneCube_injective : Function.Injective laneCube := fun a b h =>
  Fin.ext (cubeOf_injective (by omega) (by omega) h)

theorem posCube_injective : Function.Injective posCube := fun a b h => by
  have := cubeOf_injective (by omega) (by omega) h
  ext <;> omega

theorem slotCube_injective : Function.Injective fun mℓ : Bool × Lane => slotCube mℓ.1 mℓ.2 :=
  fun a b h => by
    have := cubeOf_injective (by cases a.1 <;> simp <;> omega)
      (by cases b.1 <;> simp <;> omega) h
    rcases a with ⟨_ | _, a⟩ <;> rcases b with ⟨_ | _, b⟩ <;> simp at this <;>
      simp [Fin.ext_iff] <;> omega

/-- The instances of a pack, numbered. -/
def instEquiv : Cube 4 ≃ Fin 16 :=
  (Equiv.arrowCongr (Equiv.refl (Fin 4)) finTwoEquiv.symm).trans finFunctionFinEquiv

variable {E : Type} [Field E]

/-- A table on `T`, padded with zeros to a table on the cube along `enc`. -/
def pad {k : ℕ} {T : Type} [Fintype T] [DecidableEq (Cube k)] (enc : T → Cube k) (f : T → E)
    (x : Cube k) : E :=
  ∑ j, if enc j = x then f j else 0

section pad

variable {k : ℕ} {T : Type} [Fintype T] (enc : T → Cube k)

theorem pad_enc (henc : Function.Injective enc) (f : T → E) (j : T) : pad enc f (enc j) = f j := by
  rw [pad, Finset.sum_eq_single j]
  · simp
  · intro i _ hi; simp [henc.ne hi]
  · simp

theorem sum_pad_mul (f : T → E) (g : Cube k → E) :
    ∑ x, pad enc f x * g x = ∑ j, f j * g (enc j) := by
  simp only [pad, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem mle_pad (f : T → E) (z : Fin k → E) :
    mle (pad enc f) z = ∑ j, eqPoly z (toPt (enc j)) * f j := by
  simp only [mle, mul_comm (eqPoly z _)]
  rw [sum_pad_mul]

end pad

end KeccakGkr
