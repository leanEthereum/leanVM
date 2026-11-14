/-
  LeanVM.Guest.Backend.Sound.Obl.Eval.Misc

  The guest's facts the composition reads off the data: `verify_sub` with B1's facts, the
  skipped functions' postconditions, the table's powers and relations.
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

/-- The skipped functions have no postcondition. -/
theorem skip_post : ((vsIdx :: guestRestIdx).all fun j =>
    (guestTab.sig (Data.coreFunctions.getD j default).name).post.isEmpty) = true := by
  decide +kernel

/-- The guest's core program has `1601` functions. -/
theorem core_length : Data.coreFunctions.length = 1601 := by decide +kernel

/-- **The powers the table lists are right.** -/
theorem guestTab_pows : PowsOk guestTab := by
  unfold PowsOk
  decide +kernel

/-- Only `exponent_tables` has an `xpost`: its return is in relation `0`. -/
theorem guestTab_xpost : ∀ p ∈ guestTab.sigs, p.2.xpost ≠ [] →
    p.1 = "exponent_tables" ∧ p.2.xpost = [(0, 0)] := by
  decide +kernel

end
end LeanVM.Guest.Backend.Obl
