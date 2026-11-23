module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.ColumnWeight
public import NativeRustcVmX64.Code.Vm.ColumnWeight.Names
public meta import NativeRustcVmX64.Code.Vm.ColumnWeight
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `column_weight`'s blocks, run by the symbolic executor (x86-64)

Region 0 the 1088-byte frame (R15, R14, RBX pushed at offsets `1080` to `1064`, the stack point's
66 slots from `8`, a callee's return address at `0`) and the return address, region 1 the two
argument words `x` above it (reached as `1096(%rsp)`, `1088(%rsp)`: the frame offsets `1104`,
`1096` are aliases of region 1's), region 2 the `Option<EW>` output. From `entryS`: `b0` (the
prologue, `x` loaded), the zeroing loop `b1` run 22 times (`L i` after `i` turns, every address a
literal), `b2` (`call stack_point` into the slots). From `midS` after it: `b3` (its tag), then `b4`
(`call eq_eval` on the stack point and `x`) or `b6`, `b7` (`None`); after `eq_eval`, `b5`, `b7`
(the value and the tag `1` stored).
-/

namespace NativeRustcVmX64.Ring.Column

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.ColumnWeight NativeRustcVmX64.Transcript

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(1080, .r15), (1072, .r14), (1064, .rbx)]

/-- At the entry. -/
def entryS : SState :=
  init [1096, 16, 24] [(.rsp, .ptr 0 1088), (.rdi, .ptr 2 0)] [] []
    [(.ptr 0 1104, 1, 8), (.ptr 0 1096, 1, 0)]

/-- After `b0` and `i` turns of the zeroing loop. -/
def L : Nat → SState
  | 0 => after b0 entryS
  | n + 1 => after b1 (L n)

/-- After `stack_point` (and after `eq_eval`): RSP at offset `8`, the output in RBX. -/
def midS : SState := init [1096, 16, 24] [(.rsp, .ptr 0 8), (.rbx, .ptr 2 0)]

def M3 : SState := after b3 midS

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b2 := exec b2 (L 22)
sym_block run_b3 := exec b3 midS
sym_block run_b4 := exec b4 M3
sym_block run_b6 := exec b6 M3
sym_block run_b7n := exec b7 (after b6 M3)
sym_block run_b5 := exec b5 midS
sym_block run_b7s := exec b7 (after b5 midS)

public theorem exit_b0 : exec b0 entryS = some (L 0, .fall) :=
  run_b0.trans (by rw [show L 0 = _ from after_eq run_b0])

/-- **The zeroing loop's turns.** -/
public theorem loop_step : ∀ i < 22,
    exec b1 (L i) = some (L (i + 1), .cond (.lit (decide (i < 21))) NativeRustcVmX64.Vm.ColumnWeight.label_1) := by
  decide +kernel

end NativeRustcVmX64.Ring.Column
