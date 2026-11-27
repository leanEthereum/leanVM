/-
  LeanVM.Guest.B1.Sig.Decide

  Equality of words and atoms decided by the kernel, words compared limb by limb.
-/

module

public import LeanVM.Guest.Renumber
import Mathlib.Data.List.GetD

/-!
# Deciding atom equality

The derived `DecidableEq E` (through `Vector`) does not reduce in the kernel, so words are compared
by their limbs (`eDecEq`, scoped to `Dec`) and `Atom`'s equality is derived again over it
(`Dec.instDecidableEqAtom`), which the modules deciding atom lists by `decide +kernel` use.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

namespace Dec

/-- Equality of words by their limbs. -/
scoped instance (priority := high) eDecEq : DecidableEq E := fun a b =>
  decidable_of_iff (a.limb 0 = b.limb 0 ∧ a.limb 1 = b.limb 1) (by
    constructor
    · rintro ⟨h0, h1⟩
      rw [← ofLimbs_limb a, ← ofLimbs_limb b, h0, h1]
    · rintro rfl
      exact ⟨rfl, rfl⟩)

open scoped Dec in
deriving instance DecidableEq for Atom

end Dec

attribute [-instance] Dec.instDecidableEqAtom

end
end LeanVM.Guest.B1.Sig
