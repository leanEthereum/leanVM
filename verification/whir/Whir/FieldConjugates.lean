import Whir.FieldTower
import Whir.RingMapInjectivity

/-!
# The 64 distinct conjugates of the actual binary quotient generator

The quotient generator determines every binary-algebra endomorphism. Therefore
equality of two Frobenius powers on that generator gives equality of the entire
endomorphisms. Frobenius has order equal to the certified extension degree 64,
so its first 64 powers, and hence these generator conjugates, are distinct.
-/
namespace Whir.FieldModel

noncomputable section

/-- The exact conjugate-distinctness prerequisite of the ring-switching proof,
now discharged for the actual irreducible degree-64 base modulus. -/
theorem base_conjugates_injective : Function.Injective
    (fun k : Fin 64 => (AdjoinRoot.root baseModulus) ^ (2 ^ k.val)) := by
  intro i j h
  apply Fin.ext
  have hhom : (FiniteField.frobeniusAlgHom F₂ BaseQuotient) ^ i.val =
      (FiniteField.frobeniusAlgHom F₂ BaseQuotient) ^ j.val := by
    apply AdjoinRoot.algHom_ext
    simpa only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate,
      F₂, ZMod.card] using h
  exact pow_injOn_Iio_orderOf
    (by simpa only [FiniteField.orderOf_frobeniusAlgHom, baseQuotient_finrank,
      Set.mem_Iio] using i.isLt)
    (by simpa only [FiniteField.orderOf_frobeniusAlgHom, baseQuotient_finrank,
      Set.mem_Iio] using j.isLt) hhom

/-- Any exact base-field embedding transports the certified 64 distinct roots. -/
theorem embedded_base_conjugates_injective {E : Type*} [Field E]
    (φ : BaseQuotient →+* E) : Function.Injective
      (fun k : Fin 64 => φ (AdjoinRoot.root baseModulus) ^ (2 ^ k.val)) :=
  RingMapInjectivity.conjugates_map φ _ base_conjugates_injective

end
end Whir.FieldModel
