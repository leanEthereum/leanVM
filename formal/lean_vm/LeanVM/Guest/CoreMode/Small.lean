/-
  LeanVM.Guest.CoreMode.Small

  A compiled function's instructions have small operands: the guest's check of every function,
  for the core route's functions however long.
-/

module

public import LeanVM.Guest.ExecDecodable

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest

public section

/-- **A compiled function's operands are small** (`Mode.offSmall`), from the check of every function. -/
theorem offSmall_of_mem {f : CompiledFunction} (hf : f ∈ Data.functions) : f.code.all Mode.offSmall = true := by
  have := List.all_eq_true.1 Mode.functions_offSmall f hf
  rw [CompiledFunction.code, List.all_eq_true]
  intro x hx
  obtain ⟨l, hl, hx⟩ := List.mem_flatten.1 hx
  exact List.all_eq_true.1 (List.all_eq_true.1 this l hl) x hx

end

end LeanVM.Guest.CoreMode
