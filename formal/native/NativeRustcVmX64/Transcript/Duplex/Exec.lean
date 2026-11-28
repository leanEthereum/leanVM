module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.SpongeWDuplex
public meta import NativeRustcVmX64.Code.Vm.SpongeWDuplex
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `SpongeW::duplex`'s blocks, run by the symbolic executor (x86-64)

Region 0 the 16-byte frame (`rbx` pushed at offset `8`, the calls' return addresses at `0`) and
the return address, region 1 the sponge: `entryS` at the entry (`b0`, ending in
`call duplex_input`), `midS` after it (`b1`, ending in `call keccak_f`; no region but the frame),
`exitS` after `keccak_f` (`b2`: the queue's count zeroed, the epilogue).
-/

namespace NativeRustcVmX64.Transcript.Duplex

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SpongeWDuplex

@[expose] public section

/-- The frame's slot. -/
def slots : Slots := [(8, .rbx)]

/-- At the entry: the frame (region 0), the sponge (region 1, RDI). -/
def entryS : SState := init [24, 328] [(.rsp, .ptr 0 16), (.rdi, .ptr 1 0)]
/-- After `duplex_input`: the frame. -/
def midS : SState := init [24] [(.rsp, .ptr 0 8)]
/-- After `keccak_f`: the frame, the sponge (region 1, RBX). -/
def exitS : SState := init [24, 328] [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 midS
sym_block run_b2 := exec b2 exitS

public theorem ok_b0 : ProOk 16 0 slots (after b0 entryS) = true ∧
    (after b0 entryS).reg .rdi = some (.ptr 1 0) ∧ (after b0 entryS).reg .rbx = some (.ptr 1 0) ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 16) := by
  decide +kernel
public theorem ok_b1 : MidOk 16 0 slots (after b1 midS) = true ∧
    (∀ w ∈ (after b1 midS).mem, w.r = 0 ∧ w.off + w.n ≤ 16) ∧
    (after b1 midS).reg .rdi = some (.reg .rbx) ∧ (after b1 midS).reg .rbx = some (.reg .rbx) := by
  decide +kernel
public theorem ok_b2 : EpiOk 16 slots (after b2 exitS) = true ∧
    (∀ t < 8, findWrite 1 (296 + t) (after b2 exitS).mem = some (.lit 0, t)) ∧
    (∀ w ∈ (after b2 exitS).mem, w.r = 1 ∧ 296 ≤ w.off ∧ w.off + w.n ≤ 304) := by
  decide +kernel

end NativeRustcVmX64.Transcript.Duplex
