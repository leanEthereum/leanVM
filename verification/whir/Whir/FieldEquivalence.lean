import Whir.FieldInverse
import Whir.FieldConjugates

/-! Final, assumption-free representation endpoints.  The base carrier is kept
separate from `UInt64`'s native modular-integer arithmetic.  The extension ring
is exactly the existing three-word `Concrete.E` operations. -/
namespace Whir.FieldModel
open Concrete Polynomial
noncomputable section

instance : Module.Finite BaseQuotient ExtensionQuotient :=
  extensionModulus_monic.finite_adjoinRoot
instance : Finite ExtensionQuotient := Module.finite_of_finite BaseQuotient
instance : Fintype ExtensionQuotient := Fintype.ofFinite _

theorem extensionQuotient_finrank : Module.finrank BaseQuotient ExtensionQuotient = 3 := by
  rw [(AdjoinRoot.powerBasis' extensionModulus_monic).finrank, AdjoinRoot.powerBasis'_dim]
  exact natDegree_eq_of_degree_eq_some extensionModulus_degree

@[simp] theorem card_ExtensionQuotient : Fintype.card ExtensionQuotient = 2^192 := by
  rw [Module.card_eq_pow_finrank (K := BaseQuotient), extensionQuotient_finrank,
    card_BaseQuotient]
  norm_num

theorem toExtensionQuotient_bijective : Function.Bijective toExtensionQuotient :=
  (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨toExtensionQuotient_injective, by rw [card_E, card_ExtensionQuotient]⟩

/-- The actual extension arithmetic is isomorphic to the specified cubic quotient.
Both quotient irreducibilities were kernel checked before constructing this map. -/
def extensionRingEquiv : E ≃+* ExtensionQuotient :=
  RingEquiv.ofBijective extensionRingHom toExtensionQuotient_bijective

@[simp] theorem extensionRingEquiv_apply (a : E) :
    extensionRingEquiv a = toExtensionQuotient a := rfl

/-- The exact base generator used by the machine polynomial basis. -/
theorem baseEmbedding_root : baseEmbedding (AdjoinRoot.root baseModulus) = E.ofK 2 := by
  rw [← toBaseQuotient_two, baseEmbedding_word]

/-- The 64 Frobenius conjugates of the actual word `ofK 2` are distinct. -/
theorem actual_conjugates_injective : Function.Injective
    (fun k : Fin 64 => (E.ofK 2) ^ (2 ^ k.val)) := by
  simpa only [baseEmbedding_root] using embedded_base_conjugates_injective baseEmbedding

/-- No field laws for native `UInt64` arithmetic are installed: the explicit
word bijection has precisely the executable operation-preservation contract. -/
theorem baseEquiv_operations (a b : K) :
    baseEquiv (kadd a b) = baseEquiv a + baseEquiv b ∧
    baseEquiv (kmul a b) = baseEquiv a * baseEquiv b ∧
    baseEquiv (kinv a) = (baseEquiv a)⁻¹ := by
  exact ⟨toBaseQuotient_xor a b, toBaseQuotient_kmul a b, toBaseQuotient_kinv a⟩

end
end Whir.FieldModel
