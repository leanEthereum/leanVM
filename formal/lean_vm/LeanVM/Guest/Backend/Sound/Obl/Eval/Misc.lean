/-
  LeanVM.Guest.Backend.Sound.Obl.Eval.Misc

  The guest's facts the composition reads off the data: `verify_sub` with B1's facts, the
  table's postconditions and relations, the skipped functions' names.
-/

module

public import LeanVM.Guest.Data.Core
public import LeanVM.Guest.Backend.Sound.Obl.GuestTab
public import LeanVM.Guest.Backend.Sound.Obl.CheckSound

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **The analysis accepts `verify_sub`** with B1's facts (`vsFacts`). -/
theorem evalVs : chkFnF guestTab vsFacts (Data.coreFunctions.getD vsIdx default) = true := by
  decide +kernel

/-- `verify_sub`'s name and parameters. -/
theorem vs_fn : (Data.coreFunctions.getD vsIdx default).name = "verify_sub" ∧
    (Data.coreFunctions.getD vsIdx default).params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] := by
  decide +kernel

/-- `verify_sub` takes the exponent table as argument `4`. -/
theorem vs_xpre : (guestTab.sig "verify_sub").xpre = [(4, 0)] := by decide +kernel

/-- The guest's core program has `1601` functions. -/
theorem core_length : Data.coreFunctions.length = 1601 := by decide +kernel

/-- Only `exponent_tables` has an `xpost`: its return is in relation `0`. -/
theorem guestTab_xpost : ∀ p ∈ guestTab.sigs, p.2.xpost ≠ [] →
    p.1 = "exponent_tables" ∧ p.2.xpost = [(0, 0)] := by
  decide +kernel

/-- The functions with a postcondition. -/
def postNames : List String := ["list_split", "log2_ceil_in_the_exponent__L0_L34", "da_row_shape"]

/-- Only `postNames` have a postcondition. -/
theorem guestTab_post : ∀ p ∈ guestTab.sigs, p.2.post ≠ [] → p.1 ∈ postNames := by
  decide +kernel

/-- The functions the analysis skips have no postcondition. -/
theorem skip_names : ((vsIdx :: guestXIdx).all fun j =>
    !postNames.contains (Data.coreFunctions.getD j default).name) = true := by
  decide +kernel

end
end LeanVM.Guest.Backend.Obl
