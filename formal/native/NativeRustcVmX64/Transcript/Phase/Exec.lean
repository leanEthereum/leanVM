module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.DecodedPhase
public import NativeRustcVmX64.Code.Vm.DecodedPhase.Names
public meta import NativeRustcVmX64.Code.Vm.DecodedPhase
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `Decoded::phase`'s blocks, run by the symbolic executor (x86-64)

Region 0 the 32-byte frame (R14, RBX pushed at offsets `24`, `16`, RAX at `8`, `phase_count`'s
return address at `0`) and the return address, region 1 the `Decoded` struct. `entryS` at the
entry (`b0`: the prologue, `call phase_count`); from `cmpS` after it, one environment runs the
rest: `b1` (`k` against `7`), `b2` (`k` against the count), `b3` (phase `k`'s end against the
length), `b5` (`None`, the epilogue) after `b1` or `b2`, `b6` (the base's address, the epilogue)
after `b3`. `b4` (`None` after `b3`) is never reached.
-/

namespace NativeRustcVmX64.Transcript.Phase

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.DecodedPhase

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(24, .r14), (16, .rbx)]

def entryS : SState := init [40] [(.rsp, .ptr 0 32)]
def cmpS : SState := init [40, 24] [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0)]
def S1 : SState := after b1 cmpS
def S2 : SState := after b2 S1

/-- `streamEnd l + k · phaseWords`, as `b3` computes it. -/
def baseSym : Sym :=
  .bin .add .W64 (.bin .mul .W64 (.reg .r14) (.lit 49411))
    (.bin .or .W64 (.bin .shr .W64 (.load 1 16 8) (.lit 3)) (.lit 1))

/-- The phase's end, as `b3` computes it. -/
def endSym : Sym := .bin .add .W64 (.lit 49412) baseSym

def S3 : SState := after b3 S2

/-- What a `ret` path leaves: the registers restored, nothing written, RAX's value. -/
def EndOk (S : SState) (v : Sym) : Prop :=
  EpiOk 32 slots S = true ∧ S.mem = [] ∧ S.reg .rax = some v

instance (S : SState) (v : Sym) : Decidable (EndOk S v) := by unfold EndOk; infer_instance

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 cmpS
sym_block run_b2 := exec b2 S1
sym_block run_b3 := exec b3 S2
sym_block run_b5_1 := exec b5 S1
sym_block run_b5_2 := exec b5 S2
sym_block run_b6 := exec b6 S3

public theorem ok_b0 : ProOk 32 0 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 32) ∧
    (after b0 entryS).reg .rdi = some (.reg .rdi) ∧ (after b0 entryS).reg .rbx = some (.reg .rdi) ∧
    (after b0 entryS).reg .r14 = some (.reg .rsi) := by
  decide +kernel
public theorem exit_b1 : exec b1 cmpS = some (S1, .cond
    ((SBool.cmp .ult .W64 (.reg .r14) (.lit 7)).not.and (SBool.cmp .eq .W64 (.reg .r14) (.lit 7)).not)
    NativeRustcVmX64.Vm.DecodedPhase.label_5) :=
  run_b1.trans (by rw [show S1 = _ from after_eq run_b1])
public theorem exit_b2 : exec b2 S1 = some (S2, .cond
    (SBool.cmp .ult .W64 (.reg .r14) (.reg .rax)).not NativeRustcVmX64.Vm.DecodedPhase.label_5) :=
  run_b2.trans (by rw [show S2 = _ from after_eq run_b2])
public theorem exit_b3 : exec b3 S2 = some (S3, .cond
    ((SBool.cmp .ult .W64 endSym (.load 1 8 8)).or (SBool.cmp .eq .W64 endSym (.load 1 8 8)))
    NativeRustcVmX64.Vm.DecodedPhase.label_4) :=
  run_b3.trans (by rw [show S3 = _ from after_eq run_b3]; rfl)
public theorem ok_b1 : S1.mem = [] ∧ S2.mem = [] ∧ S3.mem = [] ∧ S3.reg .rbx = some (.ptr 1 0) := by
  decide +kernel
public theorem end_b5_1 : EndOk (after b5 S1) (.lit 0) := by decide +kernel
public theorem end_b5_2 : EndOk (after b5 S2) (.lit 0) := by decide +kernel
public theorem end_b6 : EndOk (after b6 S3) (.bin .add .W64 (.load 1 0 8)
    (.bin .shl .W64 (.bin .add .W64 baseSym (.lit 1)) (.lit 3))) := by decide +kernel

end NativeRustcVmX64.Transcript.Phase
