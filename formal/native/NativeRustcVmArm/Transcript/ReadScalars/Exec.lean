module

public import NativeRustcVmArm.Transcript.FrameRun
public import NativeRustcVmArm.Code.Vm.TStateReadScalars
public meta import NativeRustcVmArm.Code.Vm.TStateReadScalars
public meta import NativeRustcVmArm.Transcript.FrameRun

/-!
# `TState::read_scalars`'s blocks, run by the symbolic executor

`entryS` at the entry (`b0`: `n = 0` returns `1` at once, `b6`, from `oneS`). Otherwise region 0
the 64-byte frame (X30, X21, X20, X19 at `32` to `64`; `read_scalar`'s output at `8`): `proS` at
`b1` (the prologue, the output's end in X21, its cursor in X19); `callS` at `b2`, the loop's head
(`bl read_scalar`); `tagS` at `b3` (its tag tested); `storeS` at `b4` (the element stored at the
cursor, region 1, the cursor advanced and compared with the end); `doneS` at `b5` (`1`, the
epilogue); `failS` at `b7` (`0`, the epilogue).
-/

namespace NativeRustcVmArm.Transcript.ReadScalars

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TStateReadScalars

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(32, .X30), (40, .X21), (48, .X20), (56, .X19)]

def entryS : SState := init [] .sp
def oneS : SState := init [] .sp
def proS : SState := init [(64, true)] (.ptr 0 64)
def callS : SState := init [(64, true)] (.ptr 0 0)
def tagS : SState := init [(64, true)] (.ptr 0 0)
def storeS : SState := init [(64, true), (16, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]
def doneS : SState := init [(64, true)] (.ptr 0 0)
def failS : SState := init [(64, true)] (.ptr 0 0)

/-- The output's end, `out + 16 n`, as `b1` computes it. -/
def endSym : Sym := .bin .add .W64 (.reg .X1) (.un (.shift .LSL 4) .W64 (.reg .X2))

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 proS
sym_block run_b2 := exec b2 callS
sym_block run_b3 := exec b3 tagS
sym_block run_b4 := exec b4 storeS
sym_block run_b5 := exec b5 doneS
sym_block run_b6 := exec b6 oneS
sym_block run_b7 := exec b7 failS

public theorem ok_b0 : (after b0 entryS).mem = [] ∧ keeps entryS (after b0 entryS) = true := by
  decide +kernel
public theorem ok_b6 : (after b6 oneS).mem = [] ∧ keeps oneS (after b6 oneS) = true ∧
    (after b6 oneS).reg .X30 = some (.reg .X30) ∧ (after b6 oneS).reg .X0 = some (.lit 1) := by
  decide +kernel
public theorem ok_b1 : ProOk slots (after b1 proS) = true ∧
    (∀ w ∈ (after b1 proS).mem, w.r = 0 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 64) ∧
    (after b1 proS).reg .X19 = some (.reg .X1) ∧ (after b1 proS).reg .X20 = some (.reg .X0) ∧
    (after b1 proS).reg .X21 = some endSym := by
  decide +kernel
public theorem ok_b2 : MidOk slots (after b2 callS) = true ∧ (after b2 callS).mem = [] ∧
    (after b2 callS).reg .X0 = some (.ptr 0 8) ∧ (after b2 callS).reg .X1 = some (.reg .X20) ∧
    (after b2 callS).reg .X19 = some (.reg .X19) ∧ (after b2 callS).reg .X20 = some (.reg .X20) ∧
    (after b2 callS).reg .X21 = some (.reg .X21) := by
  decide +kernel
public theorem ok_b3 : MidOk slots (after b3 tagS) = true ∧ (after b3 tagS).mem = [] ∧
    (after b3 tagS).reg .X19 = some (.reg .X19) ∧ (after b3 tagS).reg .X20 = some (.reg .X20) ∧
    (after b3 tagS).reg .X21 = some (.reg .X21) := by
  decide +kernel
public theorem ok_b4 : MidOk slots (after b4 storeS) = true ∧
    (∀ t < 8, findWrite 1 (0 + t) (after b4 storeS).mem = some (.load 0 16 8, t)) ∧
    (∀ t < 8, findWrite 1 (8 + t) (after b4 storeS).mem = some (.load 0 24 8, t)) ∧
    (∀ w ∈ (after b4 storeS).mem, w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 16) ∧
    (after b4 storeS).reg .X19 = some (.ptr 1 16) ∧ (after b4 storeS).reg .X20 = some (.reg .X20) ∧
    (after b4 storeS).reg .X21 = some (.reg .X21) := by
  decide +kernel
public theorem ok_b5 : EpiOk 64 slots (after b5 doneS) = true ∧ (after b5 doneS).mem = [] ∧
    (after b5 doneS).reg .X0 = some (.lit 1) := by
  decide +kernel
public theorem ok_b7 : EpiOk 64 slots (after b7 failS) = true ∧ (after b7 failS).mem = [] ∧
    (after b7 failS).reg .X0 = some (.lit 0) := by
  decide +kernel


end NativeRustcVmArm.Transcript.ReadScalars
