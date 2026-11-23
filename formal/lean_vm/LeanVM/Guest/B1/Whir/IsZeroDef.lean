/-
  LeanVM.Guest.B1.Whir.IsZeroDef

  `is_zero`'s meaning, apart from its proof so that per-function proofs reading it import no core IR.
-/

module

public import LeanVM.Guest.B1.Common.Basic

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- **`is_zero(w)`**: `1` at `w = 0`, else `0`. -/
def MeaningIsZero : List E → List E → Prop
  | [w], rets => rets = [if w = 0 then 1 else 0]
  | _, _ => False

end
end LeanVM.Guest.B1
