module

public import NativeRustcVmArm.Transcript.Glue
public import NativeRustcVmArm.Code.Vm.SpongeWDuplexInput
public meta import NativeRustcVmArm.Code.Vm.SpongeWDuplexInput
public meta import NativeRustcVmArm.Transcript.Glue

/-!
# `SpongeW::duplex_input`'s blocks, run by the symbolic executor

From `entryS` (region 0 the sponge, X0): `b0` branches on the queue's count (`load 0 296 8`) being
`0`; then `b1`, `b2`, `b3` store the waiting scalars' lanes one slot each, branching out at `1`,
`≤ 2`, `3`; `b4` loads the fourth. Each path ends with the lanes `16` words at offset `0`
(`laneSym n i`, `n` the count, at most `4`), the zero lanes stored by `b6`, `b7`, `b8`.
-/

namespace NativeRustcVmArm.Transcript.DuplexInput

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SpongeWDuplexInput

@[expose] public section

/-- At the entry: the sponge (region 0, X0). -/
def entryS : SState := init [(328, false)] .sp [(.X0, .ptr 0 0)]

/-- Lane `i < 16` after `duplex_input` with `n` waiting scalars, symbolically. -/
def laneSym (n i : Nat) : Sym :=
  if i < 4 * n then
    if i % 4 = 0 then .load 0 (200 + 24 * (i / 4)) 8
    else if i % 4 = 1 then .load 0 (208 + 24 * (i / 4)) 8
    else if i % 4 = 2 then .lit 0
    else .load 0 (216 + 24 * (i / 4)) 8
  else .lit 0

/-- The state at the end of the path for `n` waiting scalars. -/
def S1 : SState := after b1 (after b0 entryS)
def S2 : SState := after b2 S1
def S3 : SState := after b3 S2
def S4 : SState := after b4 S3
/-- Count `0`: `b6`, `b7`, `b8`. -/
def E0 : SState := after b8 (after b7 (after b6 (after b0 entryS)))
/-- Count `1`: `b7`, `b8`. -/
def E1 : SState := after b8 (after b7 S1)
/-- Count `2`: `b8`. -/
def E2 : SState := after b8 S2
/-- Count `3`: `b5`. -/
def E3 : SState := after b5 S3
/-- Count `4`: `b4`, `b5`. -/
def E4 : SState := after b5 S4

/-- A path's end: the lanes, nothing else written, X30 kept. -/
def EndOk (n : Nat) (E : SState) : Prop :=
  (∀ i < 16, ∀ t < 8, findWrite 0 (8 * i + t) E.mem = some (laneSym n i, t)) ∧
    (∀ w ∈ E.mem, w.r = 0 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 128) ∧ E.reg .X30 = some (.reg .X30) ∧
    keeps entryS E = true

instance (n : Nat) (E : SState) : Decidable (EndOk n E) := by unfold EndOk; infer_instance

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b2 := exec b2 S1
sym_block run_b3 := exec b3 S2
sym_block run_b4 := exec b4 S3
sym_block run_b6 := exec b6 (after b0 entryS)
sym_block run_b7_0 := exec b7 (after b6 (after b0 entryS))
sym_block run_b8_0 := exec b8 (after b7 (after b6 (after b0 entryS)))
sym_block run_b7_1 := exec b7 S1
sym_block run_b8_1 := exec b8 (after b7 S1)
sym_block run_b8_2 := exec b8 S2
sym_block run_b5_3 := exec b5 S3
sym_block run_b5_4 := exec b5 S4

public theorem end0 : EndOk 0 E0 := by decide +kernel
public theorem end1 : EndOk 1 E1 := by decide +kernel
public theorem end2 : EndOk 2 E2 := by decide +kernel
public theorem end3 : EndOk 3 E3 := by decide +kernel
public theorem end4 : EndOk 4 E4 := by decide +kernel

end NativeRustcVmArm.Transcript.DuplexInput
