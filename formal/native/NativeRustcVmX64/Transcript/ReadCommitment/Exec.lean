module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.TStateReadCommitment
public import NativeRustcVmX64.Code.Vm.TStateReadCommitment.Names
public meta import NativeRustcVmX64.Code.Vm.TStateReadCommitment
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `TState::read_commitment`'s blocks, run by the symbolic executor (x86-64)

Region 0 the 80-byte frame (R15 to RBX pushed at offsets `72` to `40`, `read_scalar`'s output at
`16`, its return address at `0`) and the return address. `entryS` at the entry (`b0`: the prologue,
`call read_scalar`); `doneS` after each call: `b1` (the first tag), then `b2` (the first element
kept in R12, R13, `call read_scalar`), or `b6`, `b7` (`0`, the epilogue); `b3` (the second tag),
then `b6`, `b7` on `None`. `countS` at `b4` (region 1 the `TState`: the roots' count against `8`).
`pushS` at `b5` (region 1 the new root, region 2 the count, through R14 = the count's address
minus `752` and the alias `rootAddr` of `R14 + 48 · count`): the root stored, the count advanced,
AL = `1`; then `b7`.
-/

namespace NativeRustcVmX64.Transcript.ReadCommitment

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.TStateReadCommitment

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(72, .r15), (64, .r14), (56, .r13), (48, .r12), (40, .rbx)]

def entryS : SState := init [88] [(.rsp, .ptr 0 80)]
def doneS : SState := init [88] [(.rsp, .ptr 0 8)]
def D1 : SState := after b1 doneS
def D3 : SState := after b3 doneS
def countS : SState := init [88, 760] [(.rsp, .ptr 0 8), (.r14, .ptr 1 0)]

/-- `48 · count`, as `b5` computes it from RAX = the count. -/
def offSym : Sym :=
  .bin .shl .W64 (.bin .add .W64 (.reg .rax) (.bin .mul .W64 (.reg .rax) (.lit 2))) (.lit 4)

/-- The root's address minus `368`: `R14 + 48 · count`. -/
def rootAddr : Sym := .bin .add .W64 (.ptr 2 (-752)) offSym

def pushS : SState :=
  init [88, 48, 8] [(.rsp, .ptr 0 8), (.r14, .ptr 2 (-752))] (aliases := [(rootAddr, (1, -368))])

/-- A failure's end (`b6`, `b7`): `0`, the epilogue. -/
def FailOk (S : SState) : Prop :=
  EpiOk 80 slots S = true ∧ S.mem = [] ∧ S.reg .rax = some (.lit 0)

/-- What `b5`, `b7` leave: the root and the count stored, AL = `1`, the epilogue. -/
def PushOk (S : SState) : Prop :=
  EpiOk 80 slots S = true ∧ S.reg .rax = some (.bin .merge .W8 offSym (.lit 1)) ∧
    (∀ t < 8, findWrite 1 t S.mem = some (.reg .r12, t)) ∧
    (∀ t < 8, findWrite 1 (8 + t) S.mem = some (.reg .r13, t)) ∧
    (∀ t < 8, findWrite 1 (16 + t) S.mem = some (.load 0 24 8, t)) ∧
    (∀ t < 8, findWrite 1 (24 + t) S.mem = some (.load 0 32 8, t)) ∧
    (∀ t < 8, findWrite 1 (32 + t) S.mem = some (.reg .r15, t)) ∧
    (∀ t < 8, findWrite 1 (40 + t) S.mem = some (.reg .rbx, t)) ∧
    (∀ t < 8, findWrite 2 t S.mem = some (.bin .add .W64 (.load 2 0 8) (.lit 1), t)) ∧
    (∀ w ∈ S.mem, (w.r = 1 ∧ w.off + w.n ≤ 48) ∨ (w.r = 2 ∧ w.off + w.n ≤ 8))

instance (S : SState) : Decidable (FailOk S) := by unfold FailOk; infer_instance
instance (S : SState) : Decidable (PushOk S) := by unfold PushOk; infer_instance

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 doneS
sym_block run_b2 := exec b2 D1
sym_block run_b6a := exec b6 D1
sym_block run_b7a := exec b7 (after b6 D1)
sym_block run_b3 := exec b3 doneS
sym_block run_b6b := exec b6 D3
sym_block run_b7b := exec b7 (after b6 D3)
sym_block run_b4 := exec b4 countS
sym_block run_b5 := exec b5 pushS
sym_block run_b7c := exec b7 (after b5 pushS)

public theorem ok_b0 : ProOk 80 0 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 80) ∧
    (after b0 entryS).reg .rdi = some (.ptr 0 16) ∧ (after b0 entryS).reg .rsi = some (.reg .rdi) ∧
    (after b0 entryS).reg .rbx = some (.reg .rdx) ∧ (after b0 entryS).reg .r14 = some (.reg .rdi) ∧
    (after b0 entryS).reg .r15 = some (.reg .rsi) := by
  decide +kernel
public theorem exit_b1 : exec b1 doneS = some (D1, .cond
    (SBool.cmp .eq .W32 (.load 0 16 4) (.lit 1)).not NativeRustcVmX64.Vm.TStateReadCommitment.label_5) :=
  run_b1.trans (by rw [show D1 = _ from after_eq run_b1])
public theorem ok_b1 : MidOk 80 8 slots D1 = true ∧ D1.mem = [] ∧
    (∀ r ∈ allRegs, calleeSaved r = true → D1.reg r = some (.reg r)) := by
  decide +kernel
public theorem ok_b2 : MidOk 80 0 slots (after b2 D1) = true ∧
    (∀ w ∈ (after b2 D1).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b2 D1).reg .rdi = some (.ptr 0 16) ∧ (after b2 D1).reg .rsi = some (.reg .r14) ∧
    (after b2 D1).reg .r12 = some (.load 0 24 8) ∧ (after b2 D1).reg .r13 = some (.load 0 32 8) ∧
    (∀ r ∈ allRegs, calleeSaved r = true → r ≠ .r12 → r ≠ .r13 →
      (after b2 D1).reg r = some (.reg r)) := by
  decide +kernel
public theorem exit_b6a : exec b6 D1 = some (after b6 D1, .fall) :=
  run_b6a.trans (by rw [after_eq run_b6a])
public theorem exit_b7a : exec b7 (after b6 D1) = some (after b7 (after b6 D1), .ret (.load 0 80 8)) :=
  run_b7a.trans (by rw [after_eq run_b7a])
public theorem fail_a : FailOk (after b7 (after b6 D1)) := by decide +kernel
public theorem exit_b3 : exec b3 doneS = some (D3, .cond
    (SBool.cmp .eq .W8 (.load 0 16 1) (.lit 0)) NativeRustcVmX64.Vm.TStateReadCommitment.label_5) :=
  run_b3.trans (by rw [show D3 = _ from after_eq run_b3])
public theorem ok_b3 : MidOk 80 8 slots D3 = true ∧ D3.mem = [] ∧
    (∀ r ∈ allRegs, calleeSaved r = true → D3.reg r = some (.reg r)) := by
  decide +kernel
public theorem exit_b6b : exec b6 D3 = some (after b6 D3, .fall) :=
  run_b6b.trans (by rw [after_eq run_b6b])
public theorem exit_b7b : exec b7 (after b6 D3) = some (after b7 (after b6 D3), .ret (.load 0 80 8)) :=
  run_b7b.trans (by rw [after_eq run_b7b])
public theorem fail_b : FailOk (after b7 (after b6 D3)) := by decide +kernel
public theorem exit_b4 : exec b4 countS = some (after b4 countS, .cond
    (SBool.cmp .ult .W64 (.load 1 752 8) (.lit 8)).not NativeRustcVmX64.Vm.TStateReadCommitment.label_5) :=
  run_b4.trans (by rw [after_eq run_b4])
public theorem ok_b4 : MidOk 80 8 slots (after b4 countS) = true ∧ (after b4 countS).mem = [] ∧
    (after b4 countS).reg .rax = some (.load 1 752 8) ∧
    (after b4 countS).reg .r14 = some (.ptr 1 0) ∧
    (∀ r ∈ allRegs, calleeSaved r = true → r ≠ .r14 → (after b4 countS).reg r = some (.reg r)) := by
  decide +kernel
public theorem exit_b5 : exec b5 pushS = some (after b5 pushS, .jump NativeRustcVmX64.Vm.TStateReadCommitment.label_6) :=
  run_b5.trans (by rw [after_eq run_b5])
public theorem exit_b7c : exec b7 (after b5 pushS) =
    some (after b7 (after b5 pushS), .ret (.load 0 80 8)) :=
  run_b7c.trans (by rw [after_eq run_b7c])
public theorem push_c : PushOk (after b7 (after b5 pushS)) := by decide +kernel

end NativeRustcVmX64.Transcript.ReadCommitment
