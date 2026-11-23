module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.ReaderDigest
public meta import NativeRustcVmArm.Code.Vm.ReaderDigest

/-!
# `Reader::digest`'s blocks, run by the symbolic executor

- `entryS`: region 0 the 48-byte frame below SP; the prologue and the first call (`b0`).
- `callS`: after a call, region 0 the frame, region 1 the `Option<Digest>` (X19): the check
  (`b1`, `b3`, `b5`, `b7`, the same block), then the next call (`b2`, `b4`, `b6`), the stores and
  the epilogue (`b8`), or `None` and the epilogue (`b9`).
-/

namespace NativeRustcVmArm.Wire.ReaderDigest

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.ReaderDigest

@[expose] public section

/-- The state `exec ds S` ends in (`S` where it fails). -/
def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

/-- At the entry: the frame (region 0), SP at its end. -/
def entryS : SState := init [(48, true)] (.ptr 0 48)

/-- After a call: the frame (region 0, SP) and the output (region 1, X19). -/
def callS : SState := init [(48, true), (40, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 callS
sym_block run_b2 := exec b2 callS
sym_block run_b3 := exec b3 callS
sym_block run_b4 := exec b4 callS
sym_block run_b5 := exec b5 callS
sym_block run_b6 := exec b6 callS
sym_block run_b7 := exec b7 callS
sym_block run_b9 := exec b9 (after b1 callS)

sym_block run_b8c := exec b8 callS

/-- `b8`'s writes: the tag `1`, then X22, X23, X21, X1 at offsets `8` to `32` of the output. -/
public theorem b8_writes : ∀ i < 8,
    findWrite 1 (0 + i) (after b8 callS).mem = some (.lit 1, i) ∧
    findWrite 1 (8 + i) (after b8 callS).mem = some (.reg .X22, i) ∧
    findWrite 1 (16 + i) (after b8 callS).mem = some (.reg .X23, i) ∧
    findWrite 1 (24 + i) (after b8 callS).mem = some (.reg .X21, i) ∧
    findWrite 1 (32 + i) (after b8 callS).mem = some (.reg .X1, i) := by
  decide +kernel

public theorem b8_mem : ∀ w ∈ (after b8 callS).mem, w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 0 + 40 := by
  decide +kernel

/-- `b9`'s write: the tag `0`. -/
public theorem b9_writes : ∀ i < 8, findWrite 1 (0 + i) (after b9 (after b1 callS)).mem = some (.lit 0, i) := by
  decide +kernel

public theorem b9_mem : ∀ w ∈ (after b9 (after b1 callS)).mem, w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 0 + 40 := by
  decide +kernel

end NativeRustcVmArm.Wire.ReaderDigest
