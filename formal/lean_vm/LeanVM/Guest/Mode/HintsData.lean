module

public import LeanVM.Guest.Mode.Hints
public import Statement.Data.AdviceHints
import all Statement.Data.AdviceHints

/-!
# The guest's advice, by function

The guest's advice by function, in order (`adviceFns_ok`), and its hints the parse of its text
(`adviceHints_eq`).
-/

namespace LeanVM.Guest.Mode

public section

theorem adviceFns_ok : fnsOk Data.adviceFns 0 = true := by decide +kernel

theorem adviceHints_eq : Data.adviceHints = flatFns Data.adviceFns := by rfl

end

end LeanVM.Guest.Mode
