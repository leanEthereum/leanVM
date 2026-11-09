module

public import LeanVM.Parameters.Field
meta import LeanVM.Parameters.Field
meta import CompPoly.Fields.Binary.BF64

/-!
# Tests: fields and limbs

Executable checks (`#guard`, compiled) of the limb view, the defining relation, and the two
predicates on concrete words, with one mutated word per predicate; and kernel checks
(`decide +kernel`) of what the kernel can reduce from a `module` file: literal words and the
predicates on them.
-/

namespace LeanVMTests.Parameters

open LeanVM.Parameters

public section

/-! ## Limbs and the defining relation -/

#guard (E.ofLimbs 1 (K.ofBits 2) (K.ofBits 3)).limb 0 = 1
#guard (E.ofLimbs 1 (K.ofBits 2) (K.ofBits 3)).limb 1 = K.ofBits 2
#guard (E.ofLimbs 1 (K.ofBits 2) (K.ofBits 3)).limb 2 = K.ofBits 3
#guard E.ofLimbs 1 (K.ofBits 2) (K.ofBits 3) = ofK 1 + ofK (K.ofBits 2) * y + ofK (K.ofBits 3) * y ^ 2
#guard y ^ 3 = E.ofLimbs 1 1 0
#guard toString (E.ofLimbs 1 (K.ofBits 2) (K.ofBits 3)) = "E(0x000000000000000300000000000000020000000000000001)"

/-! ## `IsInK` and `IsCanonical128` -/

#guard IsInK (ofK (K.ofBits 5))
#guard IsInK (E.ofLimbs (K.ofBits 7) 0 0)
-- Mutations: a `y` limb, then a `y²` limb.
#guard ¬ IsInK (E.ofLimbs (K.ofBits 7) 1 0)
#guard ¬ IsInK (E.ofLimbs (K.ofBits 7) 0 1)
#guard IsCanonical128 (E.ofLimbs 1 (K.ofBits 2) 0)
#guard ¬ IsCanonical128 (E.ofLimbs 0 0 1)
#guard ¬ IsCanonical128 (y ^ 2)

/-- The predicates decide in the kernel on literal words. -/
example : IsInK (E.ofLimbs (K.ofBits 7) 0 0) ∧ ¬ IsInK (E.ofLimbs (K.ofBits 7) 1 0) ∧
    IsCanonical128 (E.ofLimbs 1 (K.ofBits 2) 0) ∧ ¬ IsCanonical128 (E.ofLimbs 0 0 1) := by
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
