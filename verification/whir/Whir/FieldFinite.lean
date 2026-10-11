import Whir.FieldModel

/-! Cardinality and surjectivity of the faithful binary-word quotient map. -/
namespace Whir.FieldModel
open Concrete Polynomial
noncomputable section

instance : Module.Finite F₂ BaseQuotient := baseModulus_monic.finite_adjoinRoot
instance : Finite BaseQuotient := Module.finite_of_finite F₂
instance : Fintype BaseQuotient := Fintype.ofFinite _

theorem baseQuotient_finrank : Module.finrank F₂ BaseQuotient = 64 := by
  rw [(AdjoinRoot.powerBasis' baseModulus_monic).finrank, AdjoinRoot.powerBasis'_dim]
  exact natDegree_eq_of_degree_eq_some baseModulus_degree

@[simp] theorem card_BaseQuotient : Fintype.card BaseQuotient = 2^64 := by
  rw [Module.card_eq_pow_finrank (K := F₂), baseQuotient_finrank]
  simp [F₂]

theorem toBaseQuotient_bijective : Function.Bijective toBaseQuotient :=
  (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨toBaseQuotient_injective, by rw [card_K, card_BaseQuotient]⟩

/-- Every quotient class has exactly one 64-bit representative.  Multiplication
and XOR preservation are `toBaseQuotient_kmul` and `toBaseQuotient_xor`. -/
def baseEquiv : K ≃ BaseQuotient := Equiv.ofBijective _ toBaseQuotient_bijective

@[simp] theorem baseEquiv_apply (a : K) : baseEquiv a = toBaseQuotient a := rfl

end
end Whir.FieldModel
