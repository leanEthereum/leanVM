module

public import NativeRustcVmX64.Layout.Ladder.Tail
public import NativeRustcVmX64.Code.Vm.Ladder.Names

/-!
# `ladder` on x86-64

Outside the window, `None` (`outside`). Inside, the level count and the registers of the levels
past the third from `μ` (`head`), the query counts from `QUERY_TABLE` and the result stored
(`tail`): the `Whir.ladder μ r` the statement tabulates (`ladder_eq`).
-/

namespace NativeRustcVmX64.Layout.Ladder

open NativeRustcX64 NativeRustcVmX64.Vm.Ladder LeanVM.Parameters

public section

variable [Host] {k : Nat}

/-- **`ladder`'s contract.** -/
theorem ladder_spec (hp : Placed code k) : Spec (Labels.label NativeRustcVmX64.Vm.Ladder.entryLabel) LadderPre LadderPost := by
  intro m hpre
  unfold NativeRustcVmX64.Vm.Ladder.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.Ladder.entry_at]
  by_cases hadm : Whir.Admissible (reg m .rsi).toNat (reg m .rdx).toNat
  · exact head hp hpre hadm fun st hpc h9 ↦ tail hp hpre hadm hpc h9
  · exact outside hp hpre hadm

end

end NativeRustcVmX64.Layout.Ladder
