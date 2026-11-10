module

public import LeanVM.Parameters.Field
meta import LeanVM.Parameters.Field
meta import CompPoly.Fields.Binary.BF64

/-!
# Tests: fields and limbs

Executable checks (`#guard`, compiled) of the limb view, the defining relation, and `IsInK` on
concrete words, with mutated words; and kernel checks
(`decide +kernel`) of what the kernel can reduce from a `module` file: literal words and the
predicate on them.
-/

namespace LeanVMTests.Parameters

open LeanVM.Parameters

public section

/-! ## Limbs and the defining relation -/

#guard (E.ofLimbs 1 (K.ofBits 2)).limb 0 = 1
#guard (E.ofLimbs 1 (K.ofBits 2)).limb 1 = K.ofBits 2
#guard E.ofLimbs 1 (K.ofBits 3) = ofK 1 + ofK (K.ofBits 3) * y
#guard y ^ 2 = E.ofLimbs 1 g
-- Mutation: the modulus `y^2 + y + 1` would give `(1, 1)`.
#guard y ^ 2 ≠ E.ofLimbs 1 1
#guard toString (E.ofLimbs 1 (K.ofBits 2)) = "E(0x00000000000000020000000000000001)"

/-! ## `IsInK` -/

#guard IsInK (ofK (K.ofBits 5))
#guard IsInK (E.ofLimbs (K.ofBits 7) 0)
-- Mutation: a `y` limb.
#guard ¬ IsInK (E.ofLimbs (K.ofBits 7) 1)
#guard ¬ IsInK y

/-- The predicate decides in the kernel on literal words. -/
example : IsInK (E.ofLimbs (K.ofBits 7) 0) ∧ ¬ IsInK (E.ofLimbs (K.ofBits 7) 1) := by
  decide +kernel

/-! ## Field structure -/

-- Natural-number casts follow characteristic two; wire words preserve their bits.
#guard (2 : K) = 0
#guard K.ofBits 2 ≠ (2 : K)
#guard (K.ofBits 2).toBitVec = 2#64

/-- Instance search finds CompPoly's field structure on `K`; nothing else is installed. -/
example : (inferInstance : Field K) = BF64.instField := rfl

end
end LeanVMTests.Parameters
