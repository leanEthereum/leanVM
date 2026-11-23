module

public import NativeRustcVmArm.Whir.Common
public import NativeRustcVmArm.Code.Vm.BasisWEval
public meta import NativeRustcVmArm.Code.Vm.BasisWEval
public meta import NativeRustcVmArm.Whir.Common

/-!
# `BasisW::eval`'s blocks, run by the symbolic executor

Region 0 is the 144-byte frame below the entry's SP where a block uses it.
- `entryS` (`b0`): the frame, the `BasisW` (X1).
- `regsS` (`b1`, `b3`, `b8`, `b9`, `b12`, `b14`, `b18`, `b19`, `b21`, `b23`): registers only.
- `scaleS r` (`b2` X19, `b13`, `b20` X28): a scale.
- `ringS` (`b4`): the frame, the `BasisW` (X22), the Keccak output's point count (loaded from the
  `BasisW`).
- `frameS` (`b5`, `b6`, `b16`, `b17`): the frame.
- `claimsS` (`b7`): the `BasisW` (X22), the claims' count (loaded from it).
- `colS` (`b10`): a column claim, X20 16 bytes into it.
- `placeS` (`b11`): the placement entry `b11` computes from the column (X8) and the layout (X23).
- `cwS` (`b15`): the frame, the column claim (X20), the placement entry (X8), the layout's head
  (X23).
- `oodS` (`b22`): the frame, the `BasisW` (X22), the out-of-domain point's count.
- `outS` (`b24`, `b25` after it): the frame, the `Option<EW>` (X27).
-/

namespace NativeRustcVmArm.Whir.BasisWEval

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BasisWEval

@[expose] public section

/-- At the entry. -/
def entryS : SState := init [(144, true), (56, false)] (.ptr 0 144) [(.X1, .ptr 1 0)]
/-- Registers only. -/
def regsS : SState := init [] .sp
/-- A scale at the register `r`. -/
def scaleS (r : XReg) : SState := init [(16, false)] .sp [(r, .ptr 0 0)]
/-- The ring claim's call. -/
def ringS : SState :=
  init [(144, true), (56, false), (8, false)] (.ptr 0 0) [(.X22, .ptr 1 0)] [] []
    [(.load 1 32 8, 2, 0)]
/-- The frame. -/
def frameS : SState := init [(144, true)] (.ptr 0 0)
/-- The claims' count. -/
def claimsS : SState :=
  init [(56, false), (8, false)] .sp [(.X22, .ptr 0 0)] [] [] [(.load 0 40 8, 1, 0)]
/-- A column claim. -/
def colS : SState := init [(608, false)] .sp [(.X20, .ptr 0 16)]
/-- The placement entry's address `b11` computes. -/
def placeSym : Sym :=
  .bin .add .W64 (.bin .mul .W64 (.reg .X8) (.lit 24)) (.bin .add .W64 (.reg .X23) (.lit 120))
/-- The placement entry. -/
def placeS : SState := init [(24, false)] .sp [] [] [] [(placeSym, 0, 0)]
/-- A column claim's call. -/
def cwS : SState :=
  init [(144, true), (608, false), (24, false), (24, false)] (.ptr 0 0)
    [(.X20, .ptr 1 16), (.X8, .ptr 2 0), (.X23, .ptr 3 0)]
/-- The out-of-domain claim's call. -/
def oodS : SState :=
  init [(144, true), (56, false), (8, false)] (.ptr 0 0) [(.X22, .ptr 1 0)] [] []
    [(.load 1 48 8, 2, 0)]
/-- The result. -/
def outS : SState := init [(144, true), (24, false)] (.ptr 0 0) [(.X27, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 regsS
sym_block run_b2 := exec b2 (scaleS .X19)
sym_block run_b3 := exec b3 regsS
sym_block run_b4 := exec b4 ringS
sym_block run_b5 := exec b5 frameS
sym_block run_b6 := exec b6 frameS
sym_block run_b7 := exec b7 claimsS
sym_block run_b8 := exec b8 regsS
sym_block run_b9 := exec b9 regsS
sym_block run_b10 := exec b10 colS
sym_block run_b11 := exec b11 placeS
sym_block run_b12 := exec b12 regsS
sym_block run_b13 := exec b13 (scaleS .X28)
sym_block run_b14 := exec b14 regsS
sym_block run_b15 := exec b15 cwS
sym_block run_b16 := exec b16 frameS
sym_block run_b17 := exec b17 frameS
sym_block run_b18 := exec b18 regsS
sym_block run_b19 := exec b19 regsS
sym_block run_b20 := exec b20 (scaleS .X28)
sym_block run_b21 := exec b21 regsS
sym_block run_b22 := exec b22 oodS
sym_block run_b23 := exec b23 regsS
sym_block run_b24 := exec b24 outS
sym_block run_b25 := exec b25 (after b24 outS)

end NativeRustcVmArm.Whir.BasisWEval
