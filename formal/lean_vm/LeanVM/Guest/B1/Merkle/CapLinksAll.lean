/-
  LeanVM.Guest.B1.Merkle.CapLinksAll

  `verify_merkle_cap`'s deployed specializations at the guest's `coreProgram`, from their links:
  `CapLinks.lean` instantiated.
-/

module

public import LeanVM.Guest.B1.Merkle.CapLinks
public import LeanVM.Guest.B1.Merkle.CapAll

namespace LeanVM.Guest.B1

open LeanVM.Guest.Core

public section

/-- **`verify_merkle_cap`'s core IR is its meaning**, at the deployed cap depths, from the links
to its reference function. -/
theorem verify_merkle_cap_holds_of_linked : verify_merkle_cap_Spec :=
  verify_merkle_cap_of_linked coreProgram fun s hs ↦ by
    simp only [capSpecs, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Finds.find

end
end LeanVM.Guest.B1
