/-
  LeanVM.Guest.B1.Whir.IsZeroDefs

  `is_zero`'s meaning, apart from its proof at `coreProgram` (`IsZero`), so that a template module
  can name it without importing the guest's bodies.
-/

module

public import LeanVM.Guest.Word

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- **`is_zero(w)`**: `1` at `w = 0`, else `0`. -/
def MeaningIsZero : List E → List E → Prop
  | [w], rets => rets = [if w = 0 then 1 else 0]
  | _, _ => False

end
end LeanVM.Guest.B1
