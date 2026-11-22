/-
  LeanVM.Guest.B1.Gkr.VbgWordsC

  `verify_bus_gkr` complete within its words interface's bound (`vbgMax`).
-/

module

public import LeanVM.Guest.B1.Gkr.VbgB
public import LeanVM.Guest.B1.Gkr.VbgWords

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **`verify_bus_gkr` is complete, placed, within `vbgMax`**, at a depth `2 ≤ depth < 32`, given its words facts. -/
theorem verify_bus_gkr_completeAtW {κ depth : ℕ} (hd2 : 2 ≤ depth) (hd : depth < 32)
    (hκ : 6 ≤ κ) {cap0 xs : List E} {r : E × List E × List E} {cap' : List E}
    (hrun : RunsTo (gkrPhase depth) ⟨cap0, []⟩ xs r ⟨cap', []⟩)
    (hc : ∃ sp, (⟨cap0, []⟩ : Fs).Carries sp) (tabs stream : E) (ec ez : ℕ) (W : VbgWords fs) :
    CompleteAtB fs cert κ "verify_bus_gkr" [(ec, xs), (ez, r.2.1)]
      (cap0 ++ [ofK (addressOfIndex ec), gen ^ depth, ofK (addressOfIndex ez), tabs, stream])
      (VbgOut cap' (ofK (addressOfIndex ec) * gen ^ xs.length) r.2.2) (vbgMax fs W) :=
  (verify_bus_gkr_completeAtTB hd2 hd.le hκ hrun hc tabs stream ec ez W.hL W.h8).toCompleteAtB.mono le_rfl
    (vbgBound_le_vbgMax W hd)

end
end LeanVM.Guest.B1.Tables
