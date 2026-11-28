module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.SpongeWDuplexInput
public meta import NativeRustcVmX64.Code.Vm.SpongeWDuplexInput
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `SpongeW::duplex_input`'s blocks, run by the symbolic executor (x86-64)

From `entryS` (region 0 the return address at RSP, region 1 the sponge, RDI): `b0` branches on
the queue's count (`load 1 296 8`) being `0`; then `b1`, `b2`, `b3` store the waiting scalars' lanes
one slot each, branching out at `1`, `≤ 2`, `3`; `b4` loads the fourth. The zero lanes are stored
by `b5` to `b8` (falling through), the last slot's by `b9`, which returns. Each path ends with the
lanes `16` words at offset `0` of the sponge (`laneSym n i`, `n` the count, at most `4`).
-/

namespace NativeRustcVmX64.Transcript.DuplexInput

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SpongeWDuplexInput

@[expose] public section

/-- At the entry: the return address (region 0, RSP), the sponge (region 1, RDI). -/
def entryS : SState := init [8, 328] [(.rsp, .ptr 0 0), (.rdi, .ptr 1 0)]

/-- Lane `i < 16` after `duplex_input` with `n` waiting scalars, symbolically. -/
def laneSym (n i : Nat) : Sym :=
  if i < 4 * n then
    if i % 4 = 0 then .load 1 (200 + 24 * (i / 4)) 8
    else if i % 4 = 1 then .load 1 (208 + 24 * (i / 4)) 8
    else if i % 4 = 2 then .lit 0
    else .load 1 (216 + 24 * (i / 4)) 8
  else .lit 0

/-- The states after the stores of the first slots. -/
def S0 : SState := after b0 entryS
def S1 : SState := after b1 S0
def S2 : SState := after b2 S1
def S3 : SState := after b3 S2
def S4 : SState := after b4 S3
/-- Count `0`: `b5` to `b9`. -/
def E0 : SState := after b9 (after b8 (after b7 (after b6 (after b5 S0))))
/-- Count `1`: `b6` to `b9`. -/
def E1 : SState := after b9 (after b8 (after b7 (after b6 S1)))
/-- Count `2`: `b7` to `b9`. -/
def E2 : SState := after b9 (after b8 (after b7 S2))
/-- Count `3`: `b8`, `b9`. -/
def E3 : SState := after b9 (after b8 S3)
/-- Count `4`: `b9`. -/
def E4 : SState := after b9 S4

/-- A path's end: the lanes, nothing else written, RSP above the return address, the
callee-saved registers kept (`EpiOk`). -/
def EndOk (n : Nat) (E : SState) : Prop :=
  (∀ i < 16, ∀ t < 8, findWrite 1 (8 * i + t) E.mem = some (laneSym n i, t)) ∧
    (∀ w ∈ E.mem, w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 128) ∧ EpiOk 0 [] E = true

instance (n : Nat) (E : SState) : Decidable (EndOk n E) := by unfold EndOk; infer_instance

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 S0
sym_block run_b2 := exec b2 S1
sym_block run_b3 := exec b3 S2
sym_block run_b4 := exec b4 S3
sym_block run_b5_0 := exec b5 S0
sym_block run_b6_0 := exec b6 (after b5 S0)
sym_block run_b7_0 := exec b7 (after b6 (after b5 S0))
sym_block run_b8_0 := exec b8 (after b7 (after b6 (after b5 S0)))
sym_block run_b9_0 := exec b9 (after b8 (after b7 (after b6 (after b5 S0))))
sym_block run_b6_1 := exec b6 S1
sym_block run_b7_1 := exec b7 (after b6 S1)
sym_block run_b8_1 := exec b8 (after b7 (after b6 S1))
sym_block run_b9_1 := exec b9 (after b8 (after b7 (after b6 S1)))
sym_block run_b7_2 := exec b7 S2
sym_block run_b8_2 := exec b8 (after b7 S2)
sym_block run_b9_2 := exec b9 (after b8 (after b7 S2))
sym_block run_b8_3 := exec b8 S3
sym_block run_b9_3 := exec b9 (after b8 S3)
sym_block run_b9_4 := exec b9 S4

public theorem end0 : EndOk 0 E0 := by decide +kernel
public theorem end1 : EndOk 1 E1 := by decide +kernel
public theorem end2 : EndOk 2 E2 := by decide +kernel
public theorem end3 : EndOk 3 E3 := by decide +kernel
public theorem end4 : EndOk 4 E4 := by decide +kernel

end NativeRustcVmX64.Transcript.DuplexInput
