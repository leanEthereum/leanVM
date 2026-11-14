module

public import LeanVM.Guest.Mode.Hints
public import LeanVM.Guest.Data.AdviceHints

/-!
# The guest's advice, by function

The guest's advice by function, in order: what the mode walk's certificates' hints are checked against (`Pack/*/ModeH`, `hintsOk_of_fn`).
-/

namespace LeanVM.Guest.Mode

public section

theorem adviceFns_ok : fnsOk Data.adviceFns 0 = true := by decide +kernel

theorem adviceHints_eq : Data.adviceHints = flatFns Data.adviceFns := rfl

end

end LeanVM.Guest.Mode
