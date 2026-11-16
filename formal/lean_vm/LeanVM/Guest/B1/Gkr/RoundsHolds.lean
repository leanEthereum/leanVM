/-
  LeanVM.Guest.B1.Gkr.RoundsHolds

  `gkr_rounds__L{1,2}` are sound in the form the bus's layers use: B1-a's
  `gkr_rounds_holds`.
-/

module

public import LeanVM.Guest.B1.Gkr.Holds
public import LeanVM.Guest.B1.Sumcheck.Gkr

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- **`gkr_rounds__L{n}`, `n ∈ {1, 2}`, is sound** (from B1-a's `gkr_rounds_holds`). -/
theorem tb_gkr_rounds_holds : tb_gkr_rounds_Spec :=
  fun n hn rd _ _ _ _ _ _ h hc => tbGkrRoundsOut_of_out ((gkr_rounds_holds n hn rd _ _).mp h).2 hc

/-- **`verify_bus_gkr` is sound** (`verify_bus_gkr_holds_of` on B1-a's rounds). -/
theorem verify_bus_gkr_holds {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ) :
    verify_bus_gkr_Spec Lm.read :=
  verify_bus_gkr_holds_of tb_gkr_rounds_holds hμ Lm

end
end LeanVM.Guest.B1.Tables
