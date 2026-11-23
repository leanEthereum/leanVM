module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.BytecodeShare
public meta import NativeRustcVmArm.Code.Vm.BytecodeShare

/-!
# `bytecode_share`'s blocks, run by the symbolic executor

`entryS`, at the entry: region 0 the 432-byte frame below SP. `frS`, in the frame (SP its base).
`frO`: region 1 the output at X19 (`b15`). `frPair`: regions 1, 2 the two elements of
`bytecode_low` and of the point below X11, X12 (`b18`, the pair loop). `frOne`: one element each
(`b21`). `frEnd`: region 1 the output at X19, region 2 the point's last four slots at X9 (`b22`).
-/

namespace NativeRustcVmArm.Bus.BytecodeShare

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BytecodeShare

@[expose] public section

/-- At the entry: the frame (region 0) below SP. -/
def entryS : SState := init [(432, true)] (.ptr 0 432)

/-- In the frame: region 0 at SP. -/
def frS : SState := init [(432, true)] (.ptr 0 0)

/-- In the frame, region 1 the output at X19. -/
def frO : SState := init [(432, true), (48, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

/-- In the frame, two elements of the source 16 bytes below X11 and of the target below X12. -/
def frPair : SState :=
  init [(432, true), (32, false), (32, false)] (.ptr 0 0) [(.X11, .ptr 1 16), (.X12, .ptr 2 16)]

/-- In the frame, one element of the source 8 bytes below X11 and of the target below X12. -/
def frOne : SState :=
  init [(432, true), (16, false), (16, false)] (.ptr 0 0) [(.X11, .ptr 1 8), (.X12, .ptr 2 8)]

/-- In the frame, the output at X19, the point's last four slots at X9. -/
def frEnd : SState :=
  init [(432, true), (48, false), (64, false)] (.ptr 0 0) [(.X19, .ptr 1 0), (.X9, .ptr 2 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 frS
sym_block run_b2 := exec b2 frS
sym_block run_b3 := exec b3 frS
sym_block run_b4 := exec b4 frS
sym_block run_b5 := exec b5 frS
sym_block run_b6 := exec b6 frS
sym_block run_b7 := exec b7 frS
sym_block run_b8 := exec b8 frS
sym_block run_b9 := exec b9 frS
sym_block run_b10 := exec b10 frS
sym_block run_b11 := exec b11 frS
sym_block run_b12 := exec b12 frS
sym_block run_b13 := exec b13 frS
sym_block run_b14 := exec b14 frS
sym_block run_b15 := exec b15 frO
sym_block run_b16 := exec b16 frS
sym_block run_b17 := exec b17 frS
sym_block run_b18 := exec b18 frPair
sym_block run_b19 := exec b19 frS
sym_block run_b20 := exec b20 frS
sym_block run_b21 := exec b21 frOne
sym_block run_b22 := exec b22 frEnd

end NativeRustcVmArm.Bus.BytecodeShare
