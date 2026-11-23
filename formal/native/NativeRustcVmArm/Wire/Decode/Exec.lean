module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.Decode
public meta import NativeRustcVmArm.Code.Vm.Decode

/-!
# `decode`'s blocks, run by the symbolic executor

Region 0 is the 96-byte frame below SP throughout; SP at its end at the entry (`entryS`, the
prologue `b0`), at its base after (`frS`). The two stores into the decoded area take region 1
there: the stream's count at X21 (`b5`, `cntS`), the phase count at X21 plus eight times X8
(`b8`, `pcS`).
-/

namespace NativeRustcVmArm.Wire.Decode

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Decode

@[expose] public section

/-- At the entry: the frame (region 0), SP at its end. -/
def entryS : SState := init [(96, true)] (.ptr 0 96)

/-- In the frame (region 0, SP). -/
def frS : SState := init [(96, true)] (.ptr 0 0)

/-- In the frame; the stream's count (region 1) at X21. -/
def cntS : SState := init [(96, true), (8, false)] (.ptr 0 0) [] [] [] [(.reg .X21, 1, 0)]

/-- The phase count's address: X21 plus eight times X8. -/
def pcAddr : Sym := .bin .add .W64 (.reg .X21) (.un (.shift .LSL 3) .W64 (.reg .X8))

/-- In the frame; the phase count (region 1) at `pcAddr`. -/
def pcS : SState := init [(96, true), (8, false)] (.ptr 0 0) [] [] [] [(pcAddr, 1, 0)]

/-- The state `exec ds S` ends in (`S` where it fails). -/
def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 frS
sym_block run_b2 := exec b2 frS
sym_block run_b3 := exec b3 frS
sym_block run_b4 := exec b4 frS
sym_block run_b5 := exec b5 cntS
sym_block run_b6 := exec b6 frS
sym_block run_b7 := exec b7 frS
sym_block run_b8 := exec b8 pcS
sym_block run_b9 := exec b9 frS
sym_block run_b10 := exec b10 frS
sym_block run_b11 := exec b11 frS
sym_block run_b12 := exec b12 frS
sym_block run_b13 := exec b13 frS
sym_block run_b14 := exec b14 frS
sym_block run_b15 := exec b15 frS
sym_block run_b16 := exec b16 frS

end NativeRustcVmArm.Wire.Decode
