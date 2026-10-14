import Whir.FieldIrreducible
import Whir.FieldFinite
import Whir.FieldExtension
import Whir.FieldEquality

/-! The cubic is irreducible over the certified 64-dimensional binary field.
A cubic root would satisfy `x^8 = x`; combining this with `x^(2^64) = x`
forces `x^2 = x`, contradicting the cubic at both zero and one. -/
namespace Whir.FieldModel
open Concrete Polynomial
noncomputable section

private theorem cubic_no_root (x : BaseQuotient) : ¬ extensionModulus.IsRoot x := by
  intro hx
  have h0 : x^3 + x + 1 = 0 := by
    simpa only [IsRoot, extensionModulus, eval_add, eval_pow, eval_X, eval_one] using hx
  have h3 : x^3 = x+1 := CharTwo.add_eq_zero.mp (by simpa only [add_assoc] using h0)
  have h4 : x^4 = x^2+x := by
    calc
      x^4 = x^3*x := by ring
      _ = (x+1)*x := by rw [h3]
      _ = x^2+x := by ring
  have h6 : x^6 = x^2+1 := by
    calc
      x^6 = (x^3)^2 := by ring
      _ = (x+1)^2 := by rw [h3]
      _ = x^2+1 := by ring_nf; simp [CharTwo.two_eq_zero]
  have h8 : x^8 = x := by
    calc
      x^8 = x^6*x^2 := by ring
      _ = (x^2+1)*x^2 := by rw [h6]
      _ = x^4+x^2 := by ring
      _ = (x^2+x)+x^2 := by rw [h4]
      _ = x := by rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]
  have hp : ∀ n : Nat, x^(2^(3*n+1)) = x^2 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [show 3*(n+1)+1 = (3*n+1)+3 by omega, pow_add,
        show (2 : Nat)^3 = 8 by decide, mul_comm (2^(3*n+1)) 8, pow_mul, h8, ih]
  have hf : x^(2^64) = x := by
    have h := FiniteField.pow_card x
    rw [card_BaseQuotient] at h
    exact h
  have hs : x^2 = x := (hp 21).symm.trans hf
  have hz : x * (x-1) = 0 := by
    rw [mul_sub, ← pow_two, mul_one, hs, sub_self]
  rcases mul_eq_zero.mp hz with hz | ho
  · subst x; simp at h0
  · have h1 : x = 1 := sub_eq_zero.mp ho
    rw [h1] at h0
    simp only [one_pow, CharTwo.add_self_eq_zero, zero_add] at h0
    exact one_ne_zero h0

theorem extensionModulus_irreducible : Irreducible extensionModulus := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_eq_of_degree_eq_some extensionModulus_degree]
    decide
  · exact cubic_no_root

instance : Fact (Irreducible extensionModulus) := ⟨extensionModulus_irreducible⟩

instance : IsDomain E := toExtensionQuotient_injective.isDomain extensionRingHom

/-- A field structure extending the already-proved, executable `E` ring.
The inverse is the unique algebraic inverse; no separate executable extension
inverse existed in `Concrete`. -/
instance : Field E := Fintype.fieldOfDomain E

theorem E_field_add_def (a b : E) : a + b = E.add a b := rfl
theorem E_field_mul_def (a b : E) : a * b = E.mul a b := rfl
theorem E_field_zero_def : (0 : E) = E.zero := rfl
theorem E_field_one_def : (1 : E) = E.one := rfl

end

/-- Executable ring kernels must not synthesize their operation dictionaries
through the noncomputable finite-field inverse. These are exactly the
previously proved concrete ring's superclass dictionaries, not new operations. -/
instance : AddZeroClass E := instCommRingE.toAddZeroClass
instance : AddCommMonoid E := instCommRingE.toAddCommMonoid
instance : CommMonoid E := instCommRingE.toCommMonoid
instance : Monoid E := instCommRingE.toMonoid
instance : Sub E := instCommRingE.toSub

end Whir.FieldModel
