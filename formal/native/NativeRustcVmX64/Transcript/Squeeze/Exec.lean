module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze
public meta import NativeRustcVmX64.Code.Vm.SpongeWSqueeze
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `SpongeW::squeeze`'s blocks, run by the symbolic executor (x86-64)

Region 0 the 16-byte frame (RBX pushed at offset `8` by `b1`, `duplex`'s return address at `0`)
and the return address, region 1 the sponge. `entryS` at the entry (`b0`: the ground challenge
loaded into RAX, RDX, its tag zeroed, branching on the tag's bit `0`); `retS` at `b3` from it (the
`ret` of a ground challenge); `callS` at `b1` (RBX pushed, `call duplex`); `loadS` at `b2` (the
first two lanes into RAX, RDX, RBX popped), then `b3`.
-/

namespace NativeRustcVmX64.Transcript.Squeeze

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SpongeWSqueeze

@[expose] public section

/-- The frame's slot. -/
def slots : Slots := [(8, .rbx)]

def entryS : SState := init [24, 328] [(.rsp, .ptr 0 16), (.rdi, .ptr 1 0)]
def retS : SState := init [24] [(.rsp, .ptr 0 16)]
def callS : SState := init [24] [(.rsp, .ptr 0 16)]
def loadS : SState := init [24, 328] [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 callS
sym_block run_b2 := exec b2 loadS
sym_block run_b3 := exec b3 retS
sym_block run_b3' := exec b3 (after b2 loadS)

public theorem ok_b0 : MidOk 16 16 [] (after b0 entryS) = true ∧
    (after b0 entryS).reg .rax = some (.load 1 312 8) ∧
    (after b0 entryS).reg .rdx = some (.load 1 320 8) ∧
    (after b0 entryS).reg .rdi = some (.ptr 1 0) ∧
    (∀ t < 8, findWrite 1 (304 + t) (after b0 entryS).mem = some (.lit 0, t)) ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 1 ∧ 304 ≤ w.off ∧ w.off + w.n ≤ 312) := by
  decide +kernel
public theorem ok_b1 : ProOk 16 0 slots (after b1 callS) = true ∧
    (∀ w ∈ (after b1 callS).mem, w.r = 0 ∧ w.off + w.n ≤ 16) ∧
    (after b1 callS).reg .rdi = some (.reg .rdi) ∧ (after b1 callS).reg .rbx = some (.reg .rdi) := by
  decide +kernel
public theorem ok_b3 : EpiOk 16 [] (after b3 retS) = true ∧ (after b3 retS).mem = [] ∧
    (after b3 retS).reg .rax = some (.reg .rax) ∧ (after b3 retS).reg .rdx = some (.reg .rdx) := by
  decide +kernel
public theorem ok_b23 : EpiOk 16 slots (after b3 (after b2 loadS)) = true ∧
    (after b3 (after b2 loadS)).mem = [] ∧
    (after b3 (after b2 loadS)).reg .rax = some (.load 1 0 8) ∧
    (after b3 (after b2 loadS)).reg .rdx = some (.load 1 8 8) := by
  decide +kernel


end NativeRustcVmX64.Transcript.Squeeze
