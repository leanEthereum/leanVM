/-
  LeanVM.Guest.B1.Tables.TermAt

  `check_opening_terminal` complete in the uniform placed form (`CompleteTermAt'`).
-/

module

public import LeanVM.Guest.B1.VerifySub.CompleteIface

/-!
# `check_opening_terminal`, placed

`CompleteTermAt'`: `CompleteTermAt` with the table point `chis` that `TCtx` names fixed outside
the memory, the words at `args[1]`: the terminal's own prefix chain over `chis` is then one
buffer for every memory.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

section Placed

open LeanVM.Guest.B1.Main (MemL)

variable (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ)
  (TCtx : Reader → Layout → BusResult → List ColumnClaim → List E → Prop)
  (PCtx : Reader → List ℕ → E → E → Prop)

/-- **`check_opening_terminal`, placed**, for an explicit layout, claims, opening's end that the
terminal's check accepts and table point `chis` (at `args[1]`, its length at `args[4]`), each
claim's point of its
column's length, on the words `TermPre` reads. -/
def CompleteTermAt' : Prop :=
  ∀ (layout : Layout) (bus : BusResult) (claims : List ColumnClaim) (lam : E)
    (flockPoint coeffs : List E) (w : WhirEnd) (chis : List E) (args : List E) (Lin : Main.Layout),
    w.Accepts (stackWeight layout claims flockPoint coeffs lam) →
    (∀ c ∈ claims, c.point.length = (layout.placements.getD c.column default).vars) →
    args.getD 4 0 = gen ^ chis.length →
    (∀ rd, LowDef k rd → MemL rd Lin →
      TermPre TCtx PCtx rd layout bus claims lam flockPoint coeffs w args ∧
        ReadsAt rd (args.getD 1 0) chis) →
    CompleteAtD fs cert k "check_opening_terminal" Lin args (Returns [])

end Placed

end
end LeanVM.Guest.B1.VerifySub
