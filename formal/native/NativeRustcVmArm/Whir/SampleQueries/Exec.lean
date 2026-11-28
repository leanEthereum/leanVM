module

public import NativeRustcVmArm.Whir.Common
public import NativeRustcVmArm.Code.Vm.SampleQueries
public meta import NativeRustcVmArm.Code.Vm.SampleQueries
public meta import NativeRustcVmArm.Whir.Common

/-!
# `sample_queries`'s blocks, run by the symbolic executor

- `entryS` (`b0`, then `b1` or `b6`): region 0 the 112-byte frame below the entry's SP, region 1
  the output's count word (X3).
- `regsS` (`b2`, `b4`, `b5`, `b8`, `b9`, `b13`, `b14`, `b16`, `b17`, and the calls `b3`, `b10`):
  no region.
- `frameS` (`b7`, `b12`, `b18`): region 0 the frame, SP its base.
- `perS` (`b11`): region 0 `PER_CHALLENGE` (X27), the depth (X22) below `129`.
- `pushS` (`b15`): region 0 the frame, region 1 the output's count word (X21), region 2 the slot
  `X21 + 8 X26`.
-/

namespace NativeRustcVmArm.Whir.SampleQueries

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SampleQueries

@[expose] public section

/-- At the entry: the frame below SP (region 0), the output's count word (region 1, X3). -/
def entryS : SState := init [(112, true), (8, false)] (.ptr 0 112) [(.X3, .ptr 1 0)]
/-- Registers only. -/
def regsS : SState := init [] .sp
/-- The frame. -/
def frameS : SState := init [(112, true)] (.ptr 0 0)
/-- `PER_CHALLENGE`. -/
def perS : SState := init [(129, false)] .sp [(.X27, .ptr 0 0)] [] [(.reg .X22, 129)]
/-- The slot address `b15` stores at. -/
def slotAddr : Sym := .bin .add .W64 (.ptr 1 0) (.un (.memExtend ⟨.UXTX, .E3⟩) .W64 (.reg .X26))
/-- The push. -/
def pushS : SState :=
  init [(112, true), (8, false), (8, false)] (.ptr 0 0) [(.X21, .ptr 1 0)] [] [] [(slotAddr, 2, 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b2 := exec b2 regsS
sym_block run_b3 := exec b3 regsS
sym_block run_b4 := exec b4 regsS
sym_block run_b5 := exec b5 regsS
sym_block run_b6 := exec b6 (after b0 entryS)
sym_block run_b7 := exec b7 frameS
sym_block run_b8 := exec b8 regsS
sym_block run_b9 := exec b9 regsS
sym_block run_b10 := exec b10 regsS
sym_block run_b11 := exec b11 perS
sym_block run_b12 := exec b12 frameS
sym_block run_b13 := exec b13 regsS
sym_block run_b14 := exec b14 regsS
sym_block run_b15 := exec b15 pushS
sym_block run_b16 := exec b16 regsS
sym_block run_b17 := exec b17 regsS
sym_block run_b18 := exec b18 frameS

end NativeRustcVmArm.Whir.SampleQueries
