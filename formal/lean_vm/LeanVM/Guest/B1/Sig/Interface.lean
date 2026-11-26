/-
  LeanVM.Guest.B1.Sig.Interface

  B1's signature verifiers at the guest's `coreProgram`: the functions found, and the call
  relation unfolded to a body.
-/

module

public import LeanVM.Guest.CoreData
public import LeanVM.Guest.B1.Main.Frames
public import LeanVM.Guest.B1.Sig.InterfaceP
public import LeanVM.Guest.B1.Common.Find
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sig_lean_sphincs»

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-! ## The functions, found -/

theorem verify_sig_lean_sphincs_params : (fn% «verify_sig_lean_sphincs»).params = [.n (val% «verify_sig_lean_sphincs» "signer"), .n (val% «verify_sig_lean_sphincs» "byte_bits")] :=
  rfl

theorem find_sp_wots : coreProgram.find? "sp_wots" = some fn% «sp_wots» :=
  coreProgram_find?_at (j := idx% «sp_wots») rfl

instance finds_sp_wots : Finds coreProgram "sp_wots" Fn.«sp_wots».core := ⟨find_sp_wots⟩

theorem find_verify_sig_lean_sphincs :
    coreProgram.find? "verify_sig_lean_sphincs" = some fn% «verify_sig_lean_sphincs» :=
  coreProgram_find?_at (j := idx% «verify_sig_lean_sphincs») rfl

/-! ## The call relation -/

variable {rd : Reader}

theorem rel_iff_body {name : String} {fn : Fn} (h : coreProgram.find? name = some fn)
    (args rets : List E) :
    coreProgram.Rel rd name args rets ↔
      ∃ σ : Val, fn.params.map σ = args ∧
        Stmt.HoldsList (coreProgram.Rel rd) rd σ fn.body False (fun rs => rs = rets) := by
  rw [rel_iff]
  simp only [h, Option.some.injEq, exists_eq_left', Fn.Sem]

end
end LeanVM.Guest.B1.Sig
