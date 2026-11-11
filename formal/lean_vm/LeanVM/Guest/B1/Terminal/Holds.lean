/-
  LeanVM.Guest.B1.Terminal.Holds

  **`check_opening_terminal` is sound** (G:3437-3524; TRIAGE #70).
-/

module

public import LeanVM.Guest.B1.Terminal.HoldsOf
public import LeanVM.Guest.B1.Ring.Weight
public import LeanVM.Guest.B1.Eq.EqPrefix
public import LeanVM.Guest.B1.Eq.RsEqRun

/-!
# `check_opening_terminal`, with its callees

`check_opening_terminal_holds_of` (`Terminal/HoldsOf`) with the callees' meanings:
`eq_prefix_chain_holds` and `ring_switch_weight_holds`. The selectors' functions are B1-c's:
`column_selector_Spec` and `selector_tables_Spec` are hypotheses.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1

@[expose] public section

/-- **`check_opening_terminal` is sound**, given B1-c's selectors, on a memory image of at most
`2^32` words. -/
theorem check_opening_terminal_holds (hcs : Tables.column_selector_Spec)
    (hst : Tables.selector_tables_Spec) {μ : ℕ} (hμ : μ ≤ 32) (Lm : MemoryImage μ) :
    check_opening_terminal_Spec Lm.read :=
  check_opening_terminal_holds_of eq_prefix_chain_holds ring_switch_weight_holds
    hcs hst hμ Lm

end
end LeanVM.Guest.B1.VerifySub
