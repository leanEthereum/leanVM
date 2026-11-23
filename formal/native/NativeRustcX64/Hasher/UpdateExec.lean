module

public import NativeRustcX64.Sym
public import NativeRustcX64.Code.Common.Update
public meta import NativeRustcX64.Code.Common.Update

/-!
# `Hasher::update`'s blocks, run by the symbolic executor (x86-64)

The frame: the 120 bytes from 112 below the entry's RSP (`frm`): the return-address slot of its
calls (offset 0), its locals (8 to 63), the pushed registers (64 to 111) and its return address
(112). In the loop RSP is the frame's offset 8.

The symbolic states its proof starts blocks from and the executor's results (`run_b<k>`):
- `entryS`, at the entry (`b0`): region 0 the frame (RSP at 112), region 1 the hasher (RDI),
  region 2 the loader's `memcpy` slot;
- `headS`, at the loop head `.LUpdate_1` (`b3`, `b4`, `b5`, ending in `callq *%rbp`), after
  `memcpy` (`b6`), at the absorption (`b7`, ending in `callq keccak_f`) and after `keccak_f`
  (`b8`): region 0 the hasher (R14, R13 its buffer), region 1 the frame (RSP at 8), region 2
  the `memcpy` slot. RBP holds its resolved target, reloaded during absorption;
- `regsS`, at `.LUpdate_5` (`b2`): no region;
- `exitS`, at `.LUpdate_6` (`b9`): region 0 the frame (RSP at 8).
-/

namespace NativeRustcX64.Hasher.Update

open NativeRustcX64.Sym NativeRustcX64.Common.Update

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

/-- At the entry. -/
def entryS : SState :=
  (init [120, 344, 8] [(.rsp, .ptr 0 112), (.rdi, .ptr 1 0)]
    (aliases := [(.gotSlot "memcpy", 2, 0)])).withKnownBytes 2 0 8 (.label "memcpy")

/-- In the loop, RBP keeps the resolved `memcpy` target; absorption reloads it from the GOT. -/
def headS : SState :=
  (init [344, 120, 8]
    [(.r14, .ptr 0 0), (.r13, .ptr 0 200), (.rsp, .ptr 1 8), (.rbp, .label "memcpy")]
    (aliases := [(.gotSlot "memcpy", 2, 0)])).withKnownBytes 2 0 8 (.label "memcpy")

/-- At `.LUpdate_5`: registers only. -/
def regsS : SState := init []

/-- At `.LUpdate_6`. -/
def exitS : SState := init [120] [(.rsp, .ptr 0 8)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS

/-- The prologue writes the pushed registers into the frame's bytes 64 to 111. -/
public theorem b0_mem : ∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ 64 ≤ w.off ∧ w.off + w.n ≤ 112 := by
  decide +kernel

sym_block run_b3 := exec b3 headS
sym_block run_b4 := exec b4 (after b3 headS)
sym_block run_b5 := exec b5 (after b4 (after b3 headS))

/-- `b5` writes only the return address, at the frame's offset 0. -/
public theorem b5_mem : ∀ w ∈ (after b5 (after b4 (after b3 headS))).mem, w.r = 1 ∧ w.off + w.n ≤ 8 := by
  decide +kernel

sym_block run_b6 := exec b6 headS
sym_block run_b7 := exec b7 headS

/-- The write covering byte `j` of the hasher after the absorption: lane `j / 8` of the state XOR
lane `j / 8` of the buffer, in the rate. -/
public theorem findWrite_b7 : ∀ j < 344, findWrite 0 j (after b7 headS).mem =
    if j < 136 then
      some (.bin .xor .W64 (.load 0 (8 * (j / 8)) 8) (.load 0 (200 + 8 * (j / 8)) 8), j % 8)
    else none := by
  decide +kernel

/-- `b7` writes the rate of the hasher and the frame's first 64 bytes. -/
public theorem b7_mem : ∀ w ∈ (after b7 headS).mem,
    (w.r = 0 ∧ w.off + w.n ≤ 136) ∨ (w.r = 1 ∧ w.off + w.n ≤ 64) := by
  decide +kernel
sym_block run_b8 := exec b8 headS
sym_block run_b2 := exec b2 regsS
sym_block run_b9 := exec b9 exitS

end NativeRustcX64.Hasher.Update
