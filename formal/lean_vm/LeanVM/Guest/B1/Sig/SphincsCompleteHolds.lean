/-
  LeanVM.Guest.B1.Sig.SphincsCompleteHolds

  leanSPHINCS's guest functions at leanVM main 40f877dc are complete (`SphincsCompleteSpecs`): `sp_wots`
  and `verify_sig_lean_sphincs`.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsCompleteStmt
public import LeanVM.Guest.B1.Sig.SphincsComplete
public import LeanVM.Guest.B1.Sig.SphincsCompleteConv

namespace LeanVM.Guest.B1.Sig

@[expose] public section

/-- **leanSPHINCS's guest functions are complete**: `sp_wots` (`sp_wots_complete`) and
`verify_sig_lean_sphincs` (`verify_sig_lean_sphincs_complete_loads_of`), given its blocks'
completeness. -/
theorem sphincs_complete_of (hB : SphincsBlocksComplete) : SphincsCompleteSpecs :=
  ⟨sp_wots_complete, verify_sig_lean_sphincs_complete_loads_of hB⟩

/-- **leanSPHINCS's guest functions are complete.** -/
theorem sphincs_complete : SphincsCompleteSpecs := sphincs_complete_of sphincsBlocksComplete

end
end LeanVM.Guest.B1.Sig
