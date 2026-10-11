import Whir.FieldModel

/-! The actual three-coordinate multiplication reduces by `X³ + X + 1`.
This representation is a ring bridge, not a claim that the quotient is a field. -/
namespace Whir.FieldModel
open Concrete Polynomial
noncomputable section

/-- The exact cubic used by `Concrete.E.mul`. -/
def extensionModulus : BaseQuotient[X] := X^3 + X + 1

abbrev ExtensionQuotient := AdjoinRoot extensionModulus

def extensionPoly (a : E) : BaseQuotient[X] :=
  C (toBaseQuotient a.c0) + C (toBaseQuotient a.c1) * X +
    C (toBaseQuotient a.c2) * X^2

def toExtensionQuotient (a : E) : ExtensionQuotient :=
  AdjoinRoot.mk extensionModulus (extensionPoly a)

@[simp] theorem extensionPoly_zero : extensionPoly E.zero = 0 := by
  simp [extensionPoly, E.zero]

@[simp] theorem extensionPoly_one : extensionPoly E.one = 1 := by
  simp [extensionPoly, E.one]

@[simp] theorem extensionPoly_add (a b : E) :
    extensionPoly (E.add a b) = extensionPoly a + extensionPoly b := by
  simp only [extensionPoly, E.add, toBaseQuotient_xor, map_add]
  ring

@[simp] theorem toExtensionQuotient_zero : toExtensionQuotient E.zero = 0 := by
  simp [toExtensionQuotient]

@[simp] theorem toExtensionQuotient_one : toExtensionQuotient E.one = 1 := by
  simp [toExtensionQuotient]

@[simp] theorem toExtensionQuotient_add (a b : E) :
    toExtensionQuotient (E.add a b) = toExtensionQuotient a + toExtensionQuotient b := by
  simp [toExtensionQuotient]

/-- Polynomial reduction witness, retaining the concrete nine `kmul` calls. -/
theorem extensionPoly_mul (a b : E) :
    extensionPoly (E.mul a b) = extensionPoly a * extensionPoly b +
      extensionModulus *
        (C (toBaseQuotient a.c1 * toBaseQuotient b.c2 +
            toBaseQuotient a.c2 * toBaseQuotient b.c1) +
          C (toBaseQuotient a.c2 * toBaseQuotient b.c2) * X) := by
  simp only [extensionPoly, E.mul, toBaseQuotient_xor, toBaseQuotient_kmul,
    map_add, map_mul, extensionModulus]
  ring_nf
  simp [CharTwo.two_eq_zero]

/-- Exact operation preservation for the production extension multiplication. -/
theorem toExtensionQuotient_mul (a b : E) :
    toExtensionQuotient (E.mul a b) = toExtensionQuotient a * toExtensionQuotient b := by
  simp [toExtensionQuotient, extensionPoly_mul, AdjoinRoot.mk_self]

theorem extensionModulus_degree : extensionModulus.degree = 3 := by
  unfold extensionModulus
  compute_degree <;> norm_num

theorem extensionModulus_monic : extensionModulus.Monic := by
  have h : (X + (1 : BaseQuotient[X])).degree < 3 := by compute_degree; norm_num
  convert monic_X_pow_add h using 1; simp only [extensionModulus]; ring

theorem extensionPoly_degree_lt (a : E) : (extensionPoly a).degree < 3 := by
  unfold extensionPoly
  compute_degree; norm_num

theorem extensionPoly_injective : Function.Injective extensionPoly := by
  intro a b h
  have h0 := congrArg (fun p : BaseQuotient[X] => p.coeff 0) h
  have h1 := congrArg (fun p : BaseQuotient[X] => p.coeff 1) h
  have h2 := congrArg (fun p : BaseQuotient[X] => p.coeff 2) h
  simp [extensionPoly, coeff_C_mul, coeff_X, coeff_X_pow] at h0 h1 h2
  have e0 := toBaseQuotient_injective h0
  have e1 := toBaseQuotient_injective h1
  have e2 := toBaseQuotient_injective h2
  cases a; cases b
  simp_all

theorem toExtensionQuotient_injective : Function.Injective toExtensionQuotient := by
  intro a b h
  apply extensionPoly_injective
  apply sub_eq_zero.mp
  by_contra hn
  have hd := (degree_sub_le (extensionPoly a) (extensionPoly b)).trans_lt
    (max_lt (extensionPoly_degree_lt a) (extensionPoly_degree_lt b))
  rw [← extensionModulus_degree] at hd
  exact extensionModulus_monic.not_dvd_of_degree_lt hn hd (AdjoinRoot.mk_eq_mk.mp h)

instance : Nontrivial ExtensionQuotient := by
  refine ⟨⟨toExtensionQuotient E.zero, toExtensionQuotient E.one, ?_⟩⟩
  intro h
  have := toExtensionQuotient_injective h
  exact (by decide : E.zero ≠ E.one) this

instance : CharP ExtensionQuotient 2 :=
  charP_of_injective_algebraMap (algebraMap F₂ ExtensionQuotient).injective 2

instance : Neg E := ⟨id⟩

/-- Ring laws for the existing `E.add` and `E.mul`, obtained from the faithful
polynomial-quotient representation, not asserted as correctness assumptions. -/
instance : CommRing E where
  add := E.add
  zero := E.zero
  mul := E.mul
  one := E.one
  neg := id
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc a b c := by
    change E.add (E.add a b) c = E.add a (E.add b c)
    apply toExtensionQuotient_injective
    simp only [toExtensionQuotient_add]; ring
  zero_add a := by
    change E.add E.zero a = a
    apply toExtensionQuotient_injective
    simp only [toExtensionQuotient_add, toExtensionQuotient_zero, zero_add]
  add_zero a := by
    change E.add a E.zero = a
    apply toExtensionQuotient_injective
    simp only [toExtensionQuotient_add, toExtensionQuotient_zero, add_zero]
  add_comm a b := by
    change E.add a b = E.add b a
    apply toExtensionQuotient_injective
    simp only [toExtensionQuotient_add]; ring
  neg_add_cancel a := by
    change E.add a a = E.zero
    apply toExtensionQuotient_injective
    simp only [toExtensionQuotient_add, toExtensionQuotient_zero, CharTwo.add_self_eq_zero]
  mul_assoc a b c := by
    change E.mul (E.mul a b) c = E.mul a (E.mul b c)
    apply toExtensionQuotient_injective
    simp only [toExtensionQuotient_mul]; ring
  one_mul a := by
    change E.mul E.one a = a
    apply toExtensionQuotient_injective
    simp only [toExtensionQuotient_mul, toExtensionQuotient_one, one_mul]
  mul_one a := by
    change E.mul a E.one = a
    apply toExtensionQuotient_injective
    simp only [toExtensionQuotient_mul, toExtensionQuotient_one, mul_one]
  mul_comm a b := by
    change E.mul a b = E.mul b a
    apply toExtensionQuotient_injective
    simp only [toExtensionQuotient_mul]; ring
  left_distrib a b c := by
    change E.mul a (E.add b c) = E.add (E.mul a b) (E.mul a c)
    apply toExtensionQuotient_injective
    simp only [toExtensionQuotient_mul, toExtensionQuotient_add]; ring
  right_distrib a b c := by
    change E.mul (E.add a b) c = E.add (E.mul a c) (E.mul b c)
    apply toExtensionQuotient_injective
    simp only [toExtensionQuotient_mul, toExtensionQuotient_add]; ring
  zero_mul a := by
    change E.mul E.zero a = E.zero
    apply toExtensionQuotient_injective
    simp only [toExtensionQuotient_mul, toExtensionQuotient_zero, zero_mul]
  mul_zero a := by
    change E.mul a E.zero = E.zero
    apply toExtensionQuotient_injective
    simp only [toExtensionQuotient_mul, toExtensionQuotient_zero, mul_zero]

instance : Nontrivial E := ⟨⟨E.zero, E.one, by decide⟩⟩

def extensionRingHom : E →+* ExtensionQuotient where
  toFun := toExtensionQuotient
  map_zero' := toExtensionQuotient_zero
  map_one' := toExtensionQuotient_one
  map_add' := toExtensionQuotient_add
  map_mul' := toExtensionQuotient_mul

instance : CharP E 2 := extensionRingHom.charP toExtensionQuotient_injective 2

/-- Definitional compatibility with the executable operations already used by
`Protocol`, including code elaborated before this ring instance existed. -/
theorem E_add_def (a b : E) : a + b = E.add a b := rfl
theorem E_mul_def (a b : E) : a * b = E.mul a b := rfl
theorem E_zero_def : (0 : E) = E.zero := rfl
theorem E_one_def : (1 : E) = E.one := rfl
theorem E_default_def : (default : E) = E.zero := rfl


end
end Whir.FieldModel
