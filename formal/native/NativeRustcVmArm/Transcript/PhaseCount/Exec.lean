module

public import NativeRustcVmArm.Transcript.Glue
public import NativeRustcVmArm.Code.Vm.DecodedPhaseCount
public meta import NativeRustcVmArm.Code.Vm.DecodedPhaseCount
public meta import NativeRustcVmArm.Transcript.Glue

/-!
# `Decoded::phase_count`'s blocks, run by the symbolic executor

`entryS`, at the entry (`b0`): region 0 the `Decoded` (X0); it compares `streamEnd l` (X8) with the
slice's length. `wordS`, at `b1`: region 0 the `Decoded`, region 1 the word at `words + 8 X8`
(`wordAddr`, the address `b1` loads from). `zeroS`, at `b2`: no region.
-/

namespace NativeRustcVmArm.Transcript.PhaseCount

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.DecodedPhaseCount

@[expose] public section

/-- At the entry: the `Decoded` (region 0, X0). -/
def entryS : SState := init [(24, false)] .sp [(.X0, .ptr 0 0)]

/-- The address `[x9, x8, lsl #3]`, `x9` the slice's address. -/
def wordAddr : Sym := .bin .add .W64 (.load 0 0 8) (.un (.memExtend ⟨.UXTX, .E3⟩) .W64 (.reg .X8))

/-- At `b1`: the `Decoded` (region 0, X0) and the phase count's word (region 1). -/
def wordS : SState := init [(24, false), (8, false)] .sp [(.X0, .ptr 0 0)] (aliases := [(wordAddr, (1, 0))])

/-- At `b2`: no region. -/
def zeroS : SState := init [] .sp

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 wordS
sym_block run_b2 := exec b2 zeroS

public theorem keeps_b0 : keeps entryS (after b0 entryS) = true := by decide +kernel
public theorem keeps_b1 : keeps wordS (after b1 wordS) = true := by decide +kernel
public theorem keeps_b2 : keeps zeroS (after b2 zeroS) = true := by decide +kernel

end NativeRustcVmArm.Transcript.PhaseCount
