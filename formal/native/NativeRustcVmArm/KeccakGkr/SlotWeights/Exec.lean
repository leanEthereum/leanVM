module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.SlotWeights
public meta import NativeRustcVmArm.Code.Vm.SlotWeights

/-!
# `slot_weights`' blocks, run by the symbolic executor

The prologue (`b0`, up to the call of `eq_kernel`) with the 176-byte frame below SP as region 0;
the blocks reading or writing the frame with it from SP (`bodyS`); the zeroing loop (`b3`) with a
row (1024 bytes at X9) as region 0; the loads of a bit weight (`b7`, `b14`) with the element at
X28 - 8 (X21 - 8) as region 0; the stores of a product (`b8`, `b15`) with the element at the row
and position the loop computes (`storeAddr`) as region 0; the others from `regsS`.
-/

namespace NativeRustcVmArm.KeccakGkr.SlotWeights

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SlotWeights

@[expose] public section

/-- The entry: region 0 the frame below SP. -/
def entryS : SState := init [(176, true)] (.ptr 0 176)
/-- The body: region 0 the frame from SP. -/
def bodyS : SState := init [(176, true)] (.ptr 0 0)
/-- No regions. -/
def regsS : SState := init [] .sp
/-- The zeroing loop: region 0 the row at X9. -/
def zeroS : SState := init [(1024, false)] .sp [(.X9, .ptr 0 0)]
/-- A bit weight's load: region 0 the element at `r - 8`. -/
def loadS (r : XReg) : SState := init [(16, false)] .sp [(r, .ptr 0 8)]
/-- The address a product is stored at: row X`row` (from X19), position X`j` & 63. -/
def storeAddr (row j : XReg) : Sym :=
  .bin .add .W64 (.bin .add .W64 (.reg .X19) (.un (.shift .LSL 10) .W64 (.reg row)))
    (.un (.shift .LSL 4) .W64 (.bin .and .W64 (.reg j) (.lit 63)))
/-- A product's store: region 0 the element at `storeAddr`. -/
def storeS (row j : XReg) : SState := init [(16, false)] .sp [] [] [] [(storeAddr row j, (0, 0))]

end

set_option Elab.async false

sym_block e0 := exec b0 entryS
sym_block e1 := exec b1 regsS
sym_block e2 := exec b2 bodyS
sym_block e3 := exec b3 zeroS
sym_block e4 := exec b4 bodyS
sym_block e5 := exec b5 regsS
sym_block e6 := exec b6 regsS
sym_block e7 := exec b7 (loadS .X28)
sym_block e8 := exec b8 (storeS .X23 .X26)
sym_block e9 := exec b9 bodyS
sym_block e10 := exec b10 bodyS
sym_block e11 := exec b11 bodyS
sym_block e12 := exec b12 regsS
sym_block e13 := exec b13 regsS
sym_block e14 := exec b14 (loadS .X21)
sym_block e15 := exec b15 (storeS .X27 .X24)

end NativeRustcVmArm.KeccakGkr.SlotWeights
