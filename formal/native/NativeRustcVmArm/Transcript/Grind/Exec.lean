module

public import NativeRustcVmArm.Transcript.FrameRun
public import NativeRustcVmArm.Code.Vm.TStateGrind
public meta import NativeRustcVmArm.Code.Vm.TStateGrind
public meta import NativeRustcVmArm.Transcript.FrameRun

/-!
# `TState::grind`'s blocks, run by the symbolic executor

`entryS` at the entry (`b0`: `bits = 0` returns `1` at once, `b5`, from `oneS`). Otherwise region 0
the 64-byte frame (X30 at `32`, X20, X19 at `48`, `56`; `next_scalar`'s output at `8`): `proS` at
`b1` (the prologue, the bits in W19, `bl next_scalar`); `tagS` at `b2` (its tag's bit `0`);
`callS` at `b3` (the nonce into X1, X2, `bl absorb_nonce`); `maskS` at `b4` (the lane's low `bits`
bits tested, the epilogue); `failS` at `b6` (`0`, the epilogue).
-/

namespace NativeRustcVmArm.Transcript.Grind

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TStateGrind

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(32, .X30), (48, .X20), (56, .X19)]

def entryS : SState := init [] .sp
def oneS : SState := init [] .sp
def proS : SState := init [(64, true)] (.ptr 0 64)
def tagS : SState := init [(64, true)] (.ptr 0 0)
def callS : SState := init [(64, true)] (.ptr 0 0)
def maskS : SState := init [(64, true)] (.ptr 0 0)
def failS : SState := init [(64, true)] (.ptr 0 0)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 proS
sym_block run_b2 := exec b2 tagS
sym_block run_b3 := exec b3 callS
sym_block run_b4 := exec b4 maskS
sym_block run_b5 := exec b5 oneS
sym_block run_b6 := exec b6 failS

/-- The proof of work's test, `pow & !(-1 << bits) == 0`, in X0 after `b4`. -/
@[expose] public def okSym : Sym :=
  .ite (.not (.cmp .eq .W64 (.bin .bic .W64 (.reg .X0)
    (.bin .lslv .W64 (.lit 18446744073709551615) (.reg .X19))) (.lit 0))) (.lit 0) (.lit 1)

public theorem ok_b0 : (after b0 entryS).mem = [] ∧ keeps entryS (after b0 entryS) = true := by
  decide +kernel
public theorem ok_b5 : (after b5 oneS).mem = [] ∧ keeps oneS (after b5 oneS) = true ∧
    (after b5 oneS).reg .X30 = some (.reg .X30) ∧ (after b5 oneS).reg .X0 = some (.lit 1) := by
  decide +kernel
public theorem ok_b1 : ProOk slots (after b1 proS) = true ∧
    (∀ w ∈ (after b1 proS).mem, w.r = 0 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 64) ∧
    (after b1 proS).reg .X0 = some (.ptr 0 8) ∧ (after b1 proS).reg .X1 = some (.reg .X0) ∧
    (after b1 proS).reg .X19 = some (.un .trunc .W32 (.reg .X1)) ∧
    (after b1 proS).reg .X20 = some (.reg .X0) := by
  decide +kernel
public theorem ok_b2 : MidOk slots (after b2 tagS) = true ∧ (after b2 tagS).mem = [] ∧
    (after b2 tagS).reg .X19 = some (.reg .X19) ∧ (after b2 tagS).reg .X20 = some (.reg .X20) := by
  decide +kernel
public theorem ok_b3 : MidOk slots (after b3 callS) = true ∧ (after b3 callS).mem = [] ∧
    (after b3 callS).reg .X0 = some (.reg .X20) ∧ (after b3 callS).reg .X1 = some (.load 0 16 8) ∧
    (after b3 callS).reg .X2 = some (.load 0 24 8) ∧ (after b3 callS).reg .X19 = some (.reg .X19) := by
  decide +kernel
public theorem ok_b4 : EpiOk 64 slots (after b4 maskS) = true ∧ (after b4 maskS).mem = [] ∧
    (after b4 maskS).reg .X0 = some okSym := by
  decide +kernel
public theorem ok_b6 : EpiOk 64 slots (after b6 failS) = true ∧ (after b6 failS).mem = [] ∧
    (after b6 failS).reg .X0 = some (.lit 0) := by
  decide +kernel

end NativeRustcVmArm.Transcript.Grind
