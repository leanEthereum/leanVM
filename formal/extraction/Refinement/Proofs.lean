module

public import Refinement.Spec

/-!
# Proofs of the claims
-/

@[expose] public section

namespace Refinement.Proofs

open Aeneas.Std LeanVM.Parameters

/-- Reading a word as a field element is the statement's lane encoding. -/
theorem k_eq_ofLane (w : U64) : Spec.k w = K.ofLane ⟨w.bv⟩ := rfl

end Refinement.Proofs
