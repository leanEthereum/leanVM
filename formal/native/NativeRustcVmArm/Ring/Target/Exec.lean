module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.RingTarget
public meta import NativeRustcVmArm.Code.Vm.RingTarget

/-!
# `ring_target`'s blocks, run by the symbolic executor

- `entryS`, at the entry (`b0`): region 0 the 2352-byte frame below SP;
- `psiS`, at the images loop's head (`b1`): region 0 `s`'s element (`X20 + X22`);
- `storeS`, at the loop's end (`b2`): region 0 the image's slot (`X23 + X22`);
- `midT`, after the loop (`b3` to `b30`): region 0 the frame (SP), region 1 `f` (X21);
- `midT2`, after `f`'s last read (`b31` to `b35`): region 0 the frame;
- `exitT`, at the epilogue (`b36`): region 0 the frame.
-/

namespace NativeRustcVmArm.Ring.Target

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.RingTarget

@[expose] public section

/-- At the entry: the frame (region 0). -/
def entryS : SState := init [(2352, true)] (.ptr 0 2352)

/-- At the loop's head: `s`'s element (region 0, `X20 + X22`). -/
def psiS : SState :=
  init [(16, false)] .sp [] [] [] [(.bin .add .W64 (.reg .X20) (.reg .X22), 0, 0)]

/-- At the loop's end: the image's slot (region 0, `X23 + X22`). -/
def storeS : SState :=
  init [(16, false)] .sp [] [] [] [(.bin .add .W64 (.reg .X23) (.reg .X22), 0, 0)]

/-- After the loop: the frame (region 0, SP), `f` (region 1, X21). -/
def midT : SState := init [(2352, true), (128, false)] (.ptr 0 0) [(.X21, .ptr 1 0)]

/-- After `f`'s last read: the frame (region 0, SP). -/
def midT2 : SState := init [(2352, true)] (.ptr 0 0)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 psiS
sym_block run_b2 := exec b2 storeS
sym_block run_b3 := exec b3 midT2
sym_block run_b4 := exec b4 midT
sym_block run_b5 := exec b5 midT
sym_block run_b6 := exec b6 midT
sym_block run_b7 := exec b7 midT
sym_block run_b8 := exec b8 midT
sym_block run_b9 := exec b9 midT
sym_block run_b10 := exec b10 midT
sym_block run_b11 := exec b11 midT
sym_block run_b12 := exec b12 midT
sym_block run_b13 := exec b13 midT
sym_block run_b14 := exec b14 midT
sym_block run_b15 := exec b15 midT
sym_block run_b16 := exec b16 midT
sym_block run_b17 := exec b17 midT
sym_block run_b18 := exec b18 midT
sym_block run_b19 := exec b19 midT
sym_block run_b20 := exec b20 midT
sym_block run_b21 := exec b21 midT
sym_block run_b22 := exec b22 midT
sym_block run_b23 := exec b23 midT
sym_block run_b24 := exec b24 midT
sym_block run_b25 := exec b25 midT
sym_block run_b26 := exec b26 midT
sym_block run_b27 := exec b27 midT
sym_block run_b28 := exec b28 midT
sym_block run_b29 := exec b29 midT
sym_block run_b30 := exec b30 midT
sym_block run_b31 := exec b31 midT2
sym_block run_b32 := exec b32 midT2
sym_block run_b33 := exec b33 midT2
sym_block run_b34 := exec b34 midT2
sym_block run_b35 := exec b35 midT2
sym_block run_b36 := exec b36 midT2

end NativeRustcVmArm.Ring.Target
