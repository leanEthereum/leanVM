/-
  LeanVM.Guest.B1.Tables.VerifyTablesCAtD

  `verify_tables` is complete, placed (`CompleteTablesAt`).
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesCWrap
public import LeanVM.Guest.B1.Tables.VtPlaced
public import LeanVM.Guest.B1.Tables.VtFitsC

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest.B1

@[expose] public section

/-- **`verify_tables` is complete, placed.** -/
theorem verify_tables_completeAt (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} (hκ : 7 ≤ κ)
    (bytecode : List K) : CompleteTablesAt fs cert κ bytecode TCtx :=
  verify_tables_completeAt_of vt_placed_ok vt_fits fs cert hκ bytecode

end
end LeanVM.Guest.B1.VerifySub
