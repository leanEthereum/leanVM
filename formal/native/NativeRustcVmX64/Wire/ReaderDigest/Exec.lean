module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.ReaderDigest
public import NativeRustcVmX64.Code.Vm.ReaderDigest.Names
public meta import NativeRustcVmX64.Code.Vm.ReaderDigest
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `Reader::digest`'s blocks, run by the symbolic executor (x86-64)

Region 0 the 48-byte frame (R15 to RBX pushed at offsets `40` to `8`, `Reader::le`'s return address
at `0`) and the return address. `entryS` at the entry (`b0`: the prologue, the first
`call Reader::le`); `midS` after a call: `b1`, `b3`, `b5`, `b7` test its tag, `b2`, `b4`, `b6` keep
its word (in R12, R13, R15) and call it again (each from `midS`, the flags aside); `outS`, region 1 the output (RBX): `b8` stores the
words and `b10` the tag `1`, or `b9`, `b10` the tag `0`, and the epilogue.
-/

namespace NativeRustcVmX64.Wire.ReaderDigest

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.ReaderDigest
open NativeRustcVmX64.Transcript (Slots after after_eq ProOk MidOk EpiOk)

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(40, .r15), (32, .r14), (24, .r13), (16, .r12), (8, .rbx)]

def entryS : SState := init [56] [(.rsp, .ptr 0 48)]
def midS : SState := init [56] [(.rsp, .ptr 0 8)]
def outS : SState := init [56, 40] [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 midS
sym_block run_b2 := exec b2 midS
sym_block run_b4 := exec b4 midS
sym_block run_b6 := exec b6 midS
sym_block run_b8 := exec b8 outS
sym_block run_b9 := exec b9 outS
sym_block run_b10s := exec b10 (after b8 outS)
sym_block run_b10n := exec b10 (after b9 outS)

public theorem b3_eq : b3 = b1 := rfl
public theorem b5_eq : b5 = b1 := rfl
public theorem b7_eq : b7 = b1 := rfl

public theorem ok_b0 : ProOk 48 0 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 48) ∧
    (after b0 entryS).reg .rdi = some (.reg .rsi) ∧ (after b0 entryS).reg .rsi = some (.lit 8) ∧
    (after b0 entryS).reg .r14 = some (.reg .rsi) ∧ (after b0 entryS).reg .rbx = some (.reg .rdi) := by
  decide +kernel

public theorem ok_b1 : MidOk 48 8 slots (after b1 midS) = true ∧
    (after b1 midS).regs = midS.regs ∧ (after b1 midS).mem = [] ∧ (∀ r, (midS.reg r).isSome) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, fun r ↦ ?_⟩
  cases r <;> decide +kernel

public theorem exit_b1 : exec b1 midS = some (after b1 midS,
    .cond (SBool.cmp .eq .W64 (.reg .rax) (.lit 1)).not NativeRustcVmX64.Vm.ReaderDigest.label_8) :=
  run_b1.trans (by rw [after_eq run_b1])

/-- A call block keeping RDX's word in `x`. -/
@[expose] public def CallOk (S : SState) (x : Reg64) : Bool :=
  MidOk 48 0 slots S && S.mem.all (fun w ↦ w.r == 0 && decide (w.off + w.n ≤ 8)) &&
    S.reg .rdi == some (.reg .r14) && S.reg .rsi == some (.lit 8) && S.reg x == some (.reg .rdx) &&
    ([Reg64.rbx, .r12, .r13, .r14, .r15].filter (· != x)).all fun y ↦ S.reg y == some (.reg y)

public theorem ok_b2 : CallOk (after b2 midS) .r12 = true := by decide +kernel
public theorem ok_b4 : CallOk (after b4 midS) .r13 = true := by decide +kernel
public theorem ok_b6 : CallOk (after b6 midS) .r15 = true := by decide +kernel

public theorem ok_b10s : EpiOk 48 slots (after b10 (after b8 outS)) = true ∧
    (∀ t < 8, findWrite 1 t (after b10 (after b8 outS)).mem = some (.lit 1, t)) ∧
    (∀ t < 8, findWrite 1 (8 + t) (after b10 (after b8 outS)).mem = some (.reg .r12, t)) ∧
    (∀ t < 8, findWrite 1 (16 + t) (after b10 (after b8 outS)).mem = some (.reg .r13, t)) ∧
    (∀ t < 8, findWrite 1 (24 + t) (after b10 (after b8 outS)).mem = some (.reg .r15, t)) ∧
    (∀ t < 8, findWrite 1 (32 + t) (after b10 (after b8 outS)).mem = some (.reg .rdx, t)) ∧
    (∀ w ∈ (after b10 (after b8 outS)).mem, w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 40) := by
  decide +kernel

public theorem ok_b10n : EpiOk 48 slots (after b10 (after b9 outS)) = true ∧
    (∀ t < 8, findWrite 1 t (after b10 (after b9 outS)).mem = some (.lit 0, t)) ∧
    (∀ w ∈ (after b10 (after b9 outS)).mem, w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 40) := by
  decide +kernel

end NativeRustcVmX64.Wire.ReaderDigest
