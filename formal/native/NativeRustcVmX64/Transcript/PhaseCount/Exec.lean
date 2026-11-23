module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.DecodedPhaseCount
public meta import NativeRustcVmX64.Code.Vm.DecodedPhaseCount
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `Decoded::phase_count`'s blocks, run by the symbolic executor (x86-64)

`entryS`, at the entry (`b0`): region 0 the `Decoded` (RDI); it compares `streamEnd l` (RAX) with
the slice's length. `wordS`, at `b1` but its `ret`: region 0 the `Decoded`, region 1 the word at
`words + 8 RAX` (`wordAddr`, the address `b1` loads from). `retS`, at a `ret` (`b1`'s, `b2`):
region 0 the return address at RSP.
-/

namespace NativeRustcVmX64.Transcript.PhaseCount

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.DecodedPhaseCount

@[expose] public section

/-- At the entry: the `Decoded` (region 0, RDI). -/
def entryS : SState := init [24] [(.rdi, .ptr 0 0)]

/-- The address `(%rcx,%rax,8)`, `rcx` the slice's address. -/
def wordAddr : Sym := .bin .add .W64 (.load 0 0 8) (.bin .mul .W64 (.reg .rax) (.lit 8))

/-- At `b1`: the `Decoded` (region 0, RDI) and the phase count's word (region 1). -/
def wordS : SState := init [24, 8] [(.rdi, .ptr 0 0)] (aliases := [(wordAddr, (1, 0))])

/-- At a `ret`: the return address (region 0, RSP). -/
def retS : SState := init [8] [(.rsp, .ptr 0 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec (b1.take 2) wordS
sym_block run_b1r := exec (b1.drop 2) retS
sym_block run_b2 := exec b2 retS

public theorem ok_b0 : keeps entryS (after b0 entryS) = true ∧ (after b0 entryS).mem = [] ∧
    (after b0 entryS).reg .rdi = some (.ptr 0 0) ∧ (after b0 entryS).reg .rsp = some (.reg .rsp) ∧
    (after b0 entryS).reg .rax = some (.bin .or .W64 (.bin .shr .W64 (.load 0 16 8) (.lit 3))
      (.lit 1)) := by
  decide +kernel
public theorem ok_b1 : keeps wordS (after (b1.take 2) wordS) = true ∧
    (after (b1.take 2) wordS).mem = [] ∧
    (after (b1.take 2) wordS).reg .rsp = some (.reg .rsp) ∧
    (after (b1.take 2) wordS).reg .rax = some (.load 1 0 8) := by
  decide +kernel
public theorem ok_b1r : EpiOk 0 [] (after (b1.drop 2) retS) = true ∧
    (after (b1.drop 2) retS).mem = [] ∧ (after (b1.drop 2) retS).reg .rax = some (.reg .rax) := by
  decide +kernel
public theorem ok_b2 : EpiOk 0 [] (after b2 retS) = true ∧ (after b2 retS).mem = [] := by
  decide +kernel

end NativeRustcVmX64.Transcript.PhaseCount
