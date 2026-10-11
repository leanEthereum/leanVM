import Whir.FieldInverse

/-! A computational extension-field dictionary for extraction. The existing algebraic field dictionary uses finite-field choice for inversion. This local dictionary instead uses a fixed square-and-multiply ladder and retains the canonical executable ring operations. It is not installed as a global instance. -/
namespace Whir.ExtractionField
open Concrete

/-- At depth `n`, this computes `a^(2^(n+1)-2)` using exactly two multiplications per recursive step. -/
def inversePower : Nat → E → E
  | 0, _ => 1
  | n + 1, a =>
    let square := a * a
    square * inversePower n square

theorem inversePower_eq (n : Nat) (a : E) : inversePower n a = a ^ (2 ^ (n + 1) - 2) := by
  induction n generalizing a with
  | zero => simp [inversePower]
  | succ n ih =>
    rw [inversePower, ih, ← pow_two, ← pow_succ', ← pow_mul]
    congr 1
    have positive : 2 ≤ 2 ^ (n + 1) := by
      calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.pow_succ]
    omega

def inverse (a : E) : E := inversePower 191 a

theorem inverse_eq (a : E) : inverse a = a⁻¹ := by
  rw [inverse, inversePower_eq]
  by_cases zero : a = 0
  · subst a
    simp
  · have fermat := FiniteField.pow_card_sub_one_eq_one a zero
    rw [FieldModel.card_E] at fermat
    apply (mul_left_cancel₀ zero)
    rw [mul_inv_cancel₀ zero, ← pow_succ']
    convert fermat using 1

/-- Proofs are erased; all data operations come from the concrete ring and the fixed inversion ladder. -/
abbrev field : Field E where
  toCommRing := FieldModel.instCommRingE
  toNontrivial := (inferInstance : Nontrivial E)
  inv := inverse
  div a b := E.mul a (inverse b)
  div_eq_mul_inv _ _ := rfl
  zpow z a := match z with
    | Int.ofNat n => FieldModel.instCommRingE.npow n a
    | Int.negSucc n => inverse (FieldModel.instCommRingE.npow (n + 1) a)
  nnratCast q := E.mul (FieldModel.instCommRingE.natCast q.num)
    (inverse (FieldModel.instCommRingE.natCast q.den))
  ratCast q := E.mul (FieldModel.instCommRingE.intCast q.num)
    (inverse (FieldModel.instCommRingE.natCast q.den))
  mul_inv_cancel a nonzero := by rw [inverse_eq]; exact mul_inv_cancel₀ nonzero
  inv_zero := by rw [inverse_eq]; exact inv_zero
  nnqsmul q a := E.mul (E.mul (FieldModel.instCommRingE.natCast q.num)
    (inverse (FieldModel.instCommRingE.natCast q.den))) a
  qsmul q a := E.mul (E.mul (FieldModel.instCommRingE.intCast q.num)
    (inverse (FieldModel.instCommRingE.natCast q.den))) a

/-- Cost-instrumented execution of the very same ladder. The first projection is
proved equal to the dictionary's implementation, so the count cannot describe a
different inverse algorithm. One unit is one concrete extension multiplication;
array traffic and word instructions are not included. -/
def countedInversePower : Nat → E → E × Nat
  | 0, _ => (1, 0)
  | n + 1, a =>
    let square := a * a
    let tail := countedInversePower n square
    (square * tail.1, tail.2 + 2)

theorem countedInversePower_value (n : Nat) (a : E) :
    (countedInversePower n a).1 = inversePower n a := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [countedInversePower, inversePower, ih]

theorem countedInversePower_cost (n : Nat) (a : E) :
    (countedInversePower n a).2 = 2 * n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [countedInversePower, ih, Nat.mul_add]

theorem inverse_191_steps_382_multiplications (a : E) :
    (countedInversePower 191 a).1 = inverse a ∧
      (countedInversePower 191 a).2 = 382 := by
  exact ⟨countedInversePower_value 191 a, countedInversePower_cost 191 a⟩

end Whir.ExtractionField
