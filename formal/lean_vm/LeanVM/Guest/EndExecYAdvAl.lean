/-
  LeanVM.Guest.EndExecYAdvAl

  The deployed alignment's advice by function is the advice's own.
-/

module

public import LeanVM.Guest.Bridge.PairChk.All
public import LeanVM.Guest.B2C.CplRun
public import LeanVM.Guest.Mode.Hints
import all LeanVM.Guest.Data.Functions
import all Statement.Data.AdviceHints

/-!
# The alignment's advice

`adviceOf_fns`: compiled function `j`'s advice in the alignment check (`Bridge.adviceOf j`) is the
`j`-th of the advice's functions, of its code's length: the data check's (`Bridge.PairJ`) for every
function but `__jump_tables`, which `adviceOf_zero` decides.
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Guest

public section

/-- `__jump_tables`' advice, which the data check leaves out. -/
theorem adviceOf_zero :
    Data.adviceFns[0]? = some (Bridge.adviceOf 0) ∧ (Bridge.adviceOf 0).2.1 = (fnOf 0).instructionCount := by
  decide +kernel

theorem adviceOf_fns {j : ℕ} (hj : j < nFns) :
    Data.adviceFns[j]? = some (Bridge.adviceOf j) ∧ (Bridge.adviceOf j).2.1 = (fnOf j).code.length := by
  rw [CompiledFunction.length_code (CompiledFunction.wellChunked_of_mem (B2C.fnOf_memC hj))]
  rcases Nat.eq_zero_or_pos j with rfl | h1
  · exact adviceOf_zero
  · exact (Bridge.PairChk.pairJ_all j h1 (by have : nFns = fn_count% := rfl; omega)).2

end

end LeanVM.Guest.EndExec
