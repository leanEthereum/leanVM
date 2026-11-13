/-
  LeanVM.Guest.B1.Gkr.RoundsHolds

  `gkr_rounds__L{1,2,4,6}` are sound in the form the bus's layers use: B1-a's
  `gkr_rounds_holds`.
-/

module

public import LeanVM.Guest.B1.Gkr.Holds
public import LeanVM.Guest.B1.Sumcheck.Gkr

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- B1-a's meaning of `gkr_rounds` gives the rounds between records. -/
theorem tbGkrRoundsOut_of_meaning {n : ℕ} {rd : Reader} {rec pt tabs : E} {rets : List E}
    (h : MeaningGkrRounds n rd [rec, pt, tabs] rets) : TbGkrRoundsOut n rd rec pt := by
  obtain ⟨-, cap, cur, claim, cs, es, h1, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨cap, cur, claim, cs, es, h1, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- **`gkr_rounds__L{n}`, `n ∈ {1, 2, 4, 6}`, is sound** (from B1-a's `gkr_rounds_holds`). -/
theorem tb_gkr_rounds_holds : tb_gkr_rounds_Spec :=
  fun n hn rd _ _ _ _ h => tbGkrRoundsOut_of_meaning ((gkr_rounds_holds.1 n hn rd _ _).mp h)

/-- **`verify_bus_gkr` is sound** (`verify_bus_gkr_holds_of` on B1-a's rounds). -/
theorem verify_bus_gkr_holds {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ) :
    verify_bus_gkr_Spec Lm.read :=
  verify_bus_gkr_holds_of tb_gkr_rounds_holds hμ Lm

end
end LeanVM.Guest.B1.Tables
