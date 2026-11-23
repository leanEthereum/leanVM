module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.GkrStep
public meta import NativeRustcVmArm.Code.Vm.GkrStep

/-!
# `gkr_step`'s blocks, run by the symbolic executor

- `entryS`, at the entry (`b0`): region 0 the 1392-byte frame below SP.
- `frS`, in the frame (SP its base): the blocks touching only the frame.
- `frP`, in the frame with region 1 the `GkrStateW` (1064 bytes) at X19: `b5`, `b24` to `b28`,
  `b34`, `b37`.
- `pairS`, the pair loop's body (`b35`): region 0 the two source elements at X9 less 16, region 1
  the two destination slots at X10 less 24.
- `oneS`, the single loop's body (`b38`): region 0 the source element at X9 less 8, region 1 the
  destination slot at X10 less 8.
-/

namespace NativeRustcVmArm.Bus.GkrStep

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.GkrStep

@[expose] public section

/-- At the entry: the frame (region 0) below SP. -/
def entryS : SState := init [(1392, true)] (.ptr 0 1392)

/-- In the frame: region 0 at SP. -/
def frS : SState := init [(1392, true)] (.ptr 0 0)

/-- In the frame, region 1 the `GkrStateW` at X19. -/
def frP : SState := init [(1392, true), (1064, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

/-- The pair loop's body: the sources at X9 less 16, the slots at X10 less 24. -/
def pairS : SState := init [(32, false), (32, false)] .sp [(.X9, .ptr 0 16), (.X10, .ptr 1 24)]

/-- The single loop's body: the source at X9 less 8, the slot at X10 less 8. -/
def oneS : SState := init [(16, false), (16, false)] .sp [(.X9, .ptr 0 8), (.X10, .ptr 1 8)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 frS
sym_block run_b2 := exec b2 frS
sym_block run_b3 := exec b3 frS
sym_block run_b4 := exec b4 frS
sym_block run_b5 := exec b5 frP
sym_block run_b6 := exec b6 frS
sym_block run_b7 := exec b7 frS
sym_block run_b8 := exec b8 frS
sym_block run_b9 := exec b9 frS
sym_block run_b10 := exec b10 frS
sym_block run_b11 := exec b11 frS
sym_block run_b12 := exec b12 frS
sym_block run_b13 := exec b13 frS
sym_block run_b14 := exec b14 frS
sym_block run_b15 := exec b15 frS
sym_block run_b16 := exec b16 frS
sym_block run_b17 := exec b17 frS
sym_block run_b18 := exec b18 frS
sym_block run_b19 := exec b19 frS
sym_block run_b20 := exec b20 frS
sym_block run_b21 := exec b21 frS
sym_block run_b22 := exec b22 frS
sym_block run_b23 := exec b23 frS
sym_block run_b24 := exec b24 frP
sym_block run_b25 := exec b25 frP
sym_block run_b26 := exec b26 frP
sym_block run_b27 := exec b27 frP
sym_block run_b28 := exec b28 frP
sym_block run_b29 := exec b29 frS
sym_block run_b30 := exec b30 frS
sym_block run_b31 := exec b31 frS
sym_block run_b32 := exec b32 frS
sym_block run_b33 := exec b33 frS
sym_block run_b34 := exec b34 frP
sym_block run_b35 := exec b35 pairS
sym_block run_b36 := exec b36 frS
sym_block run_b37 := exec b37 frP
sym_block run_b38 := exec b38 oneS
sym_block run_b39 := exec b39 frS

end NativeRustcVmArm.Bus.GkrStep
