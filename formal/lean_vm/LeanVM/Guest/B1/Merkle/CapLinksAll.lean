/-
  LeanVM.Guest.B1.Merkle.CapLinksAll

  `verify_merkle_cap`'s deployed specializations at the guest's `coreProgram`: `CapLinks.lean`
  instantiated.
-/

module

public import LeanVM.Guest.B1.Merkle.CapLinks
public import LeanVM.Guest.B1.Common.Family

namespace LeanVM.Guest.B1

open LeanVM.Guest.Core

@[expose] public section

/-- `verify_merkle_cap__L{D}`'s core IR is its meaning, `2 ≤ D ≤ 8`. -/
def verify_merkle_cap_Spec : Prop := verify_merkle_cap_SpecP coreProgram

core_find «verify_merkle_cap__L2» «verify_merkle_cap__L3» «verify_merkle_cap__L4»
  «verify_merkle_cap__L5» «verify_merkle_cap__L6» «verify_merkle_cap__L7» «verify_merkle_cap__L8»

/-- **`verify_merkle_cap`'s core IR is its meaning**, at the deployed cap depths. -/
theorem verify_merkle_cap_holds : verify_merkle_cap_Spec :=
  verify_merkle_cap_of_linked coreProgram fun s hs ↦ by
    simp only [capSpecs, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [find_verify_merkle_cap_L2, find_verify_merkle_cap_L3, find_verify_merkle_cap_L4,
      find_verify_merkle_cap_L5, find_verify_merkle_cap_L6, find_verify_merkle_cap_L7,
      find_verify_merkle_cap_L8]

end
end LeanVM.Guest.B1
