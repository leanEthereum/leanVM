/-
  LeanVM.Guest.B1.Merkle.CapAll

  B1 for the deployed `verify_merkle_cap` specializations at the guest's `coreProgram`:
  `CapAllP.lean` instantiated.
-/

module

public import LeanVM.Guest.B1.Merkle.CapAllP
public import LeanVM.Guest.B1.Common.Find

namespace LeanVM.Guest.B1

open LeanVM.Guest.Core

@[expose] public section

/-- `verify_merkle_cap__L{D}`'s core IR is its meaning, `2 ≤ D ≤ 8`. -/
def verify_merkle_cap_Spec : Prop := verify_merkle_cap_SpecP coreProgram

set_option maxRecDepth 100000 in
theorem find_verify_merkle_cap_L2 :
    coreProgram.find? "verify_merkle_cap__L2" = some fn% «verify_merkle_cap__L2» :=
  coreProgram_find?_at (j := idx% «verify_merkle_cap__L2») rfl

instance finds_verify_merkle_cap_L2 :
    Finds coreProgram "verify_merkle_cap__L2" Fn.«verify_merkle_cap__L2».core :=
  ⟨find_verify_merkle_cap_L2⟩

set_option maxRecDepth 100000 in
theorem find_verify_merkle_cap_L3 :
    coreProgram.find? "verify_merkle_cap__L3" = some fn% «verify_merkle_cap__L3» :=
  coreProgram_find?_at (j := idx% «verify_merkle_cap__L3») rfl

instance finds_verify_merkle_cap_L3 :
    Finds coreProgram "verify_merkle_cap__L3" Fn.«verify_merkle_cap__L3».core :=
  ⟨find_verify_merkle_cap_L3⟩

set_option maxRecDepth 100000 in
theorem find_verify_merkle_cap_L4 :
    coreProgram.find? "verify_merkle_cap__L4" = some fn% «verify_merkle_cap__L4» :=
  coreProgram_find?_at (j := idx% «verify_merkle_cap__L4») rfl

instance finds_verify_merkle_cap_L4 :
    Finds coreProgram "verify_merkle_cap__L4" Fn.«verify_merkle_cap__L4».core :=
  ⟨find_verify_merkle_cap_L4⟩

set_option maxRecDepth 100000 in
theorem find_verify_merkle_cap_L5 :
    coreProgram.find? "verify_merkle_cap__L5" = some fn% «verify_merkle_cap__L5» :=
  coreProgram_find?_at (j := idx% «verify_merkle_cap__L5») rfl

instance finds_verify_merkle_cap_L5 :
    Finds coreProgram "verify_merkle_cap__L5" Fn.«verify_merkle_cap__L5».core :=
  ⟨find_verify_merkle_cap_L5⟩

set_option maxRecDepth 100000 in
theorem find_verify_merkle_cap_L6 :
    coreProgram.find? "verify_merkle_cap__L6" = some fn% «verify_merkle_cap__L6» :=
  coreProgram_find?_at (j := idx% «verify_merkle_cap__L6») rfl

instance finds_verify_merkle_cap_L6 :
    Finds coreProgram "verify_merkle_cap__L6" Fn.«verify_merkle_cap__L6».core :=
  ⟨find_verify_merkle_cap_L6⟩

set_option maxRecDepth 100000 in
theorem find_verify_merkle_cap_L7 :
    coreProgram.find? "verify_merkle_cap__L7" = some fn% «verify_merkle_cap__L7» :=
  coreProgram_find?_at (j := idx% «verify_merkle_cap__L7») rfl

instance finds_verify_merkle_cap_L7 :
    Finds coreProgram "verify_merkle_cap__L7" Fn.«verify_merkle_cap__L7».core :=
  ⟨find_verify_merkle_cap_L7⟩

set_option maxRecDepth 100000 in
theorem find_verify_merkle_cap_L8 :
    coreProgram.find? "verify_merkle_cap__L8" = some fn% «verify_merkle_cap__L8» :=
  coreProgram_find?_at (j := idx% «verify_merkle_cap__L8») rfl

instance finds_verify_merkle_cap_L8 :
    Finds coreProgram "verify_merkle_cap__L8" Fn.«verify_merkle_cap__L8».core :=
  ⟨find_verify_merkle_cap_L8⟩

/-- **`verify_merkle_cap`'s core IR is its meaning**, at the deployed cap depths. -/
theorem verify_merkle_cap_holds : verify_merkle_cap_Spec := verify_merkle_cap_holdsP coreProgram

end
end LeanVM.Guest.B1
