module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.FirstClaim
public meta import NativeRustcVmArm.Code.Vm.FirstClaim

/-!
# `first_claim`'s blocks, run by the symbolic executor

The prologue (`b0`, up to the call of `eq_kernel`) with the 1408-byte frame below SP as region 0;
the blocks reading or writing the frame with it from SP (`bodyS`), `b2` with the word above it too
(`wS`, the bit weights' address); a lane's load (`b3`) with the element at the address the loop
computes (`laneAddr`) as region 0; a bit weight's store (`b4`) with the element at X27 - 8 as
region 0; the result's stores (`b17`, `b18`) with the 776 bytes at X19 as region 0; the others
from `regsS`.
-/

namespace NativeRustcVmArm.KeccakGkr.FirstClaim

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.FirstClaim

@[expose] public section

/-- The entry: region 0 the frame below SP. -/
def entryS : SState := init [(1408, true)] (.ptr 0 1408)
/-- The body: region 0 the frame from SP. -/
def bodyS : SState := init [(1408, true)] (.ptr 0 0)
/-- `b2`: region 0 the frame from SP and the word above it. -/
def wS : SState := init [(1416, true)] (.ptr 0 0)
/-- No regions. -/
def regsS : SState := init [] .sp
/-- The address of lane `(X20 / 64) % 32` of the lanes at X26. -/
def laneAddr : Sym :=
  .bin .add .W64 (.reg .X26) (.un (.shift .LSL 4) .W64 (.un (.ubfm 6 10) .W64 (.reg .X20)))
/-- A lane's load: region 0 the element at `laneAddr`. -/
def laneS : SState := init [(16, false)] .sp [] [] [] [(laneAddr, (0, 0))]
/-- A bit weight's store: region 0 the element at X27 - 8. -/
def storeS : SState := init [(16, false)] .sp [(.X27, .ptr 0 8)]
/-- The result's stores: region 0 the 776 bytes at X19. -/
def outS : SState := init [(776, false)] .sp [(.X19, .ptr 0 0)]

end

set_option Elab.async false

sym_block e0 := exec b0 entryS
sym_block e1 := exec b1 regsS
sym_block e2 := exec b2 wS
sym_block e3 := exec b3 laneS
sym_block e4 := exec b4 storeS
sym_block e5 := exec b5 bodyS
sym_block e6 := exec b6 regsS
sym_block e7 := exec b7 bodyS
sym_block e8 := exec b8 regsS
sym_block e9 := exec b9 bodyS
sym_block e10 := exec b10 regsS
sym_block e11 := exec b11 bodyS
sym_block e12 := exec b12 regsS
sym_block e13 := exec b13 bodyS
sym_block e14 := exec b14 regsS
sym_block e15 := exec b15 bodyS
sym_block e16 := exec b16 bodyS
sym_block e17 := exec b17 outS
sym_block e18 := exec b18 outS
sym_block e19 := exec b19 bodyS

end NativeRustcVmArm.KeccakGkr.FirstClaim
