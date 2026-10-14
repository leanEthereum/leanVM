import Whir.FieldTower

/-! Embedding the certified base quotient into the actual extension carrier. -/
namespace Whir.FieldModel
open Concrete Polynomial
noncomputable section

@[simp] theorem toBaseQuotient_baseEquiv_symm (a : BaseQuotient) :
    toBaseQuotient (baseEquiv.symm a) = a := baseEquiv.apply_symm_apply a

@[simp] theorem toExtensionQuotient_ofK (a : K) :
    toExtensionQuotient (E.ofK a) =
      AdjoinRoot.of extensionModulus (toBaseQuotient a) := by
  simp [toExtensionQuotient, extensionPoly, E.ofK]

/-- The polynomial-base inclusion, expressed on the actual extension words. -/
def baseEmbedding : BaseQuotient →+* E where
  toFun a := E.ofK (baseEquiv.symm a)
  map_zero' := by
    apply toExtensionQuotient_injective
    change toExtensionQuotient (E.ofK (baseEquiv.symm 0)) = toExtensionQuotient E.zero
    simp [toExtensionQuotient_ofK]
  map_one' := by
    apply toExtensionQuotient_injective
    change toExtensionQuotient (E.ofK (baseEquiv.symm 1)) = toExtensionQuotient E.one
    simp [toExtensionQuotient_ofK]
  map_add' a b := by
    apply toExtensionQuotient_injective
    change toExtensionQuotient (E.ofK (baseEquiv.symm (a+b))) =
      toExtensionQuotient (E.add (E.ofK (baseEquiv.symm a)) (E.ofK (baseEquiv.symm b)))
    simp
  map_mul' a b := by
    apply toExtensionQuotient_injective
    change toExtensionQuotient (E.ofK (baseEquiv.symm (a*b))) =
      toExtensionQuotient (E.mul (E.ofK (baseEquiv.symm a)) (E.ofK (baseEquiv.symm b)))
    simp [toExtensionQuotient_mul]

@[simp] theorem baseEmbedding_word (a : K) :
    baseEmbedding (toBaseQuotient a) = E.ofK a := by
  change E.ofK (baseEquiv.symm (baseEquiv a)) = E.ofK a
  rw [baseEquiv.symm_apply_apply]

theorem ofK_injective : Function.Injective E.ofK := by
  intro a b h
  exact congrArg E.c0 h

@[simp] theorem ofK_one : E.ofK (1 : K) = (1 : E) := rfl
@[simp] theorem ofK_zero : E.ofK (0 : K) = (0 : E) := rfl

theorem ofK_xor (a b : K) : E.ofK (a ^^^ b) = E.ofK a + E.ofK b := by
  simpa only [map_add, baseEmbedding_word] using congrArg baseEmbedding (toBaseQuotient_xor a b)

theorem ofK_kmul (a b : K) : E.ofK (kmul a b) = E.ofK a * E.ofK b := by
  simpa only [map_mul, baseEmbedding_word] using
    congrArg baseEmbedding (toBaseQuotient_kmul a b)

end
end Whir.FieldModel
