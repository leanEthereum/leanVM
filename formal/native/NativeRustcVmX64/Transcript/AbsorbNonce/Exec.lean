module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.SpongeWAbsorbNonce
public meta import NativeRustcVmX64.Code.Vm.SpongeWAbsorbNonce
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `SpongeW::absorb_nonce`'s blocks, run by the symbolic executor (x86-64)

Region 0 the 16-byte frame (RBX pushed at offset `8`, the calls' return addresses at `0`) and
the return address, region 1 the sponge. `entryS` at the entry (`b0`: RBX pushed, `call absorb`
with the tag `4`); `callS` at `b1` (`call duplex`); `exitS` at `b2` (the third lane into RAX, the
first two stored as the ground challenge with tag `1`, RBX popped, `ret`).
-/

namespace NativeRustcVmX64.Transcript.AbsorbNonce

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SpongeWAbsorbNonce

@[expose] public section

/-- The frame's slot. -/
def slots : Slots := [(8, .rbx)]

def entryS : SState := init [24, 328] [(.rsp, .ptr 0 16), (.rdi, .ptr 1 0)]
def callS : SState := init [24] [(.rsp, .ptr 0 8)]
def exitS : SState := init [24, 328] [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 callS
sym_block run_b2 := exec b2 exitS

public theorem ok_b0 : ProOk 16 0 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 16) ∧
    (after b0 entryS).reg .rdi = some (.ptr 1 0) ∧ (after b0 entryS).reg .rsi = some (.reg .rsi) ∧
    (after b0 entryS).reg .rdx = some (.reg .rdx) ∧ (after b0 entryS).reg .rcx = some (.lit 4) ∧
    (after b0 entryS).reg .rbx = some (.ptr 1 0) := by
  decide +kernel
public theorem ok_b1 : MidOk 16 0 slots (after b1 callS) = true ∧
    (∀ w ∈ (after b1 callS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b1 callS).reg .rdi = some (.reg .rbx) ∧ (after b1 callS).reg .rbx = some (.reg .rbx) := by
  decide +kernel
public theorem ok_b2 : EpiOk 16 slots (after b2 exitS) = true ∧
    (after b2 exitS).reg .rax = some (.load 1 16 8) ∧
    (∀ t < 8, findWrite 1 (304 + t) (after b2 exitS).mem = some (.lit 1, t)) ∧
    (∀ t < 8, findWrite 1 (312 + t) (after b2 exitS).mem = some (.load 1 0 8, t)) ∧
    (∀ t < 8, findWrite 1 (320 + t) (after b2 exitS).mem = some (.load 1 8 8, t)) ∧
    (∀ w ∈ (after b2 exitS).mem, w.r = 1 ∧ 304 ≤ w.off ∧ w.off + w.n ≤ 328) := by
  decide +kernel

end NativeRustcVmX64.Transcript.AbsorbNonce
