module

public import NativeRustcVmArm.Code.Vm.Ladder.Names
public import NativeRustcVmArm.Layout.Ladder.Head

/-!
# `ladder`

Outside the window, `None` (`outside`). Inside, the level count and the levels past the third from
`μ` (`head`), the query counts from `QUERY_TABLE` (`mid`), the result stored (`tail`): the
`Whir.ladder μ r` the statement tabulates (`ladder_eq`).
-/

namespace NativeRustcVmArm.Layout.Ladder

open NativeRustcArm NativeRustcVmArm.Vm.Ladder LeanVM.Parameters

public section

variable [Host] {k : Nat}

/-- **`ladder`'s contract.** -/
theorem ladder_spec (hp : Placed code k) : Spec (Labels.label NativeRustcVmArm.Vm.Ladder.entryLabel) LadderPre LadderPost := by
  intro m hpre
  rw [show Labels.label NativeRustcVmArm.Vm.Ladder.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.Ladder.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.Ladder.entryOffset) NativeRustcVmArm.Vm.Ladder.entry_at]
  by_cases hadm : Whir.Admissible m.regs.X1.toNat m.regs.X2.toNat
  · exact head hp hpre hadm fun st hpc h9 ↦ mid hp hpre.1 hpre.2.1 hpre.2.2 hadm hpc h9
      fun st' hpc' h15 ↦ tail hp hpre.2.1 hadm hpc' h15
  · exact outside hp hpre hadm

end

end NativeRustcVmArm.Layout.Ladder
