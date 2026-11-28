module

public import NativeRustcArm.Sym
public import NativeRustcArm.Code.Common.Update
public meta import NativeRustcArm.Code.Common.Update

/-!
# `Hasher::update`'s blocks, run by the symbolic executor

The symbolic states its proof starts blocks from and the executor's results (`run_b<k>`):
- `entryS`, at the entry (`b0`): region 0 the 64-byte frame below SP, region 1 the hasher (X0);
- `headS`, at the loop head `.LUpdate_2` (`b2`, `b3`, `b4`, ending in `bl memcpy`), after
  `memcpy` (`b5`), at the absorption (`b6`, ending in `bl keccak_f`; its writes `lanesMem`, the
  buffer's 17 lanes XORed into the state's, `findWrite_lanes`) and after `keccak_f` (`b7`):
  region 0 the hasher (X20), X23 its buffer, X24 `136`;
- `regsS`, at `.LUpdate_1` (`b1`): no region;
- `exitS`, at `.LUpdate_6` (`b8`): region 0 the frame (SP).

`after ds S` is the state `exec ds S` ends in; `exec_after` reads a run from it as one from the
literal state.
-/

namespace NativeRustcArm.Hasher.Update

open NativeRustcArm.Sym NativeRustcArm.Common.Update

@[expose] public section

/-- The state `exec ds S` ends in (`S` where it fails). -/
def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

theorem after_eq {ds : List Directive} {S S₁ : SState} {x : Exit} (h : exec ds S = some (S₁, x)) :
    after ds S = S₁ := by
  rw [after, h]

theorem exec_after {ds ds' : List Directive} {S S₁ : SState} {x : Exit}
    (h : exec ds S = some (S₁, x)) {r : Option (SState × Exit)} (h' : exec ds' (after ds S) = r) :
    exec ds' S₁ = r := by
  rw [after, h] at h'
  exact h'

/-- At the entry: the frame (region 0) and the hasher (region 1, X0). -/
def entryS : SState := init [(64, true), (344, false)] (.ptr 0 64) [(.X0, .ptr 1 0)]

/-- In the loop: the hasher (region 0, X20), its buffer (X23) and `136` (X24). -/
def headS : SState :=
  init [(344, false)] .sp [(.X20, .ptr 0 0), (.X23, .ptr 0 200), (.X24, .lit 136)]

/-- The absorption's writes, newest first: lane `i` of the state XOR lane `i` of the buffer. -/
def lanesMem : List Write :=
  (List.range 17).reverse.map fun i =>
    ⟨0, 8 * i, 8, .bin .eor .W64 (.load 0 (8 * i) 8) (.load 0 (200 + 8 * i) 8)⟩

/-- At `.LUpdate_1`: registers only. -/
def regsS : SState := init [] .sp

/-- At `.LUpdate_6`: the frame (region 0, SP). -/
def exitS : SState := init [(64, true)] (.ptr 0 0)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
/-- The prologue's slots in the frame: the callee-saved registers and X29, X30. -/
@[expose] public def slots : List (Nat × XReg) :=
  [(56, .X19), (48, .X20), (40, .X21), (32, .X22), (24, .X23), (16, .X24), (8, .X30), (0, .X29)]

public theorem b0_slots : ∀ p ∈ slots, ∀ i < 8,
    findWrite 0 (p.1 + i) (after b0 entryS).mem = some (.reg p.2, i) := by
  decide +kernel

public theorem b0_mem : ∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 64 := by
  decide +kernel

sym_block run_b2 := exec b2 headS
sym_block run_b3 := exec b3 (after b2 headS)
sym_block run_b4 := exec b4 (after b3 (after b2 headS))
sym_block run_b5 := exec b5 headS
sym_block run_b6 := exec b6 headS

public theorem b6_mem : (after b6 headS).mem = lanesMem := by decide +kernel

/-- The write covering byte `j` of the hasher after the absorption. -/
public theorem findWrite_lanes : ∀ j < 344, findWrite 0 j lanesMem =
    if j < 136 then
      some (.bin .eor .W64 (.load 0 (8 * (j / 8)) 8) (.load 0 (200 + 8 * (j / 8)) 8), j % 8)
    else none := by
  decide +kernel
sym_block run_b7 := exec b7 headS
sym_block run_b1 := exec b1 regsS
sym_block run_b8 := exec b8 exitS

end NativeRustcArm.Hasher.Update
