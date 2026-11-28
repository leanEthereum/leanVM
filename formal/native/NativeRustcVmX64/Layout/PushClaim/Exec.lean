module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Layout.Stack.Common
public import NativeRustcVmX64.Code.Vm.PushClaim
public import NativeRustcVmX64.Code.Vm.BufEW36Extend.Names
public import NativeRustcVmX64.Code.Vm.PushClaim.Names
public meta import NativeRustcVmX64.Code.Vm.PushClaim
public meta import NativeRustcVmX64.Layout.Stack.Common

/-!
# `push_claim`'s blocks, run by the symbolic executor (x86-64)

Full (`fullS`: region 0 the return address at RSP, region 1 the claims' count word at RDI): `b0`
branches to `b4`, which returns AL = `0`.

Room (`entryS`): region 0 the 48-byte frame and the return address (R15, R14, R12, RBX pushed at
`40` to `16`, RAX at `8`, the call's return address at `0`), region 1 the count word, region 2
the next claim's 608 bytes (`slotX`, the address `b1` computes, is its base less `8`). `b0` falls
through; `b1` pushes, writes the column and the point's count `0`, and calls `Buf::extend` on
the point.

After the call (`retS`): R15 the count word, `8 + R15 + R12` (`retX`) the claim's base. `b2`
branches on AL: `b5` AL = `0`; `b3` writes the value and the count plus one, AL = `1`; `b6` the
epilogue.
-/

namespace NativeRustcVmX64.Layout.PushClaim

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.PushClaim NativeRustcVmX64.Transcript
open NativeRustcVmX64.Layout.Stack (WritesW)

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(40, .r15), (32, .r14), (24, .r12), (16, .rbx)]

/-- `rdi + count · 608`, as `b1` computes it: the next claim's address less `8`. -/
def slotX : Sym := .bin .add .W64 (.ptr 1 0) (.bin .mul .W64 (.load 1 0 8) (.lit 608))

/-- `8 + (r15 + r12)`, as `b3` computes it: the claim's address. -/
def retX : Sym := .bin .add .W64 (.lit 8) (.bin .add .W64 (.ptr 1 0) (.reg .r12))

/-- The count's test in `b0`: more than `159` claims. -/
def fullSym : SBool :=
  (SBool.cmp .ult .W64 (.load 1 0 8) (.lit 159)).not.and
    (SBool.cmp .eq .W64 (.load 1 0 8) (.lit 159)).not

/-- `Buf::extend`'s result's test in `b2`: AL is `0`. -/
def failSym : SBool := .cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)

def fullS : SState := init [8, 8] [(.rsp, .ptr 0 0), (.rdi, .ptr 1 0)]
def entryS : SState :=
  init [56, 8, 608] [(.rsp, .ptr 0 48), (.rdi, .ptr 1 0)] [] [] [(slotX, (2, -8))]
def retS : SState :=
  init [56, 8, 608] [(.rsp, .ptr 0 8), (.r15, .ptr 1 0)] [] [] [(retX, (2, 0))]
def F0 : SState := after b0 fullS
def E0 : SState := after b0 entryS
def R2 : SState := after b2 retS
def R3 : SState := after b3 R2
def R5 : SState := after b5 R2

end

set_option Elab.async false

sym_block run_full := exec b0 fullS
sym_block run_b4 := exec b4 F0
sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 E0
sym_block run_b2 := exec b2 retS
sym_block run_b3 := exec b3 R2
sym_block run_b5 := exec b5 R2
sym_block run_b6a := exec b6 R3
sym_block run_b6b := exec b6 R5

public theorem exit_full : exec b0 fullS = some (F0, .cond fullSym NativeRustcVmX64.Vm.PushClaim.label_1) :=
  run_full.trans (by rw [show F0 = _ from after_eq run_full]; rfl)
public theorem exit_b4 : exec b4 F0 = some (after b4 F0, .ret (.load 0 0 8)) :=
  run_b4.trans (by rw [after_eq run_b4])
public theorem ok_b4 : EpiOk 0 [] (after b4 F0) = true ∧ (after b4 F0).mem = [] ∧
    (after b4 F0).reg .rax = some (.lit 0) := by
  decide +kernel
public theorem exit_b0 : exec b0 entryS = some (E0, .cond fullSym NativeRustcVmX64.Vm.PushClaim.label_1) :=
  run_b0.trans (by rw [show E0 = _ from after_eq run_b0]; rfl)
public theorem ok_b0 : E0.mem = [] ∧ E0.reg .rsp = some (.ptr 0 48) := by decide +kernel
public theorem exit_b1 : exec b1 E0 = some (after b1 E0,
    .call NativeRustcVmX64.Vm.BufEW36Extend.entryLabel) :=
  run_b1.trans (by rw [after_eq run_b1])
public theorem ok_b1 : ProOk 48 0 slots (after b1 E0) = true ∧
    (∀ w ∈ (after b1 E0).mem, (w.r = 0 ∧ w.off + w.n ≤ 48) ∨ (w.r = 2 ∧ w.off + w.n ≤ 16)) ∧
    WritesW 2 [(0, .reg .rsi), (8, .lit 0)] (after b1 E0) = true ∧
    (after b1 E0).reg .rdi = some (.bin .add .W64 (.lit 16)
      (.bin .add .W64 (.bin .mul .W64 (.load 1 0 8) (.lit 608)) (.ptr 1 0))) ∧
    (after b1 E0).reg .rsi = some (.reg .rdx) ∧ (after b1 E0).reg .rdx = some (.reg .rcx) ∧
    (after b1 E0).reg .r15 = some (.ptr 1 0) ∧
    (after b1 E0).reg .r12 = some (.bin .mul .W64 (.load 1 0 8) (.lit 608)) ∧
    (after b1 E0).reg .r14 = some (.reg .r8) ∧ (after b1 E0).reg .rbx = some (.reg .r9) := by
  decide +kernel
public theorem exit_b2 : exec b2 retS = some (R2, .cond failSym NativeRustcVmX64.Vm.PushClaim.label_4) :=
  run_b2.trans (by rw [show R2 = _ from after_eq run_b2]; rfl)
public theorem ok_b2 : MidOk 48 8 slots R2 = true ∧ R2.mem = [] := by decide +kernel
public theorem exit_b3 : exec b3 R2 = some (R3, .jump NativeRustcVmX64.Vm.PushClaim.label_6) :=
  run_b3.trans (by rw [show R3 = _ from after_eq run_b3])
public theorem exit_b5 : exec b5 R2 = some (R5, .fall) :=
  run_b5.trans (by rw [show R5 = _ from after_eq run_b5])
public theorem ok_b5 : MidOk 48 8 slots R5 = true ∧ R5.mem = [] := by decide +kernel
public theorem exit_b6a : exec b6 R3 = some (after b6 R3, .ret (.load 0 48 8)) :=
  run_b6a.trans (by rw [after_eq run_b6a])
public theorem end_b6a : EpiOk 48 slots (after b6 R3) = true ∧
    (∀ w ∈ (after b6 R3).mem,
      (w.r = 1 ∧ w.off + w.n ≤ 8) ∨ (w.r = 2 ∧ 592 ≤ w.off ∧ w.off + w.n ≤ 608)) ∧
    WritesW 1 [(0, .bin .add .W64 (.load 1 0 8) (.lit 1))] (after b6 R3) = true ∧
    WritesW 2 [(592, .reg .r14), (600, .reg .rbx)] (after b6 R3) = true ∧
    (after b6 R3).reg .rax = some (.bin .merge .W8 retX (.lit 1)) := by
  decide +kernel
public theorem exit_b6b : exec b6 R5 = some (after b6 R5, .ret (.load 0 48 8)) :=
  run_b6b.trans (by rw [after_eq run_b6b])
public theorem end_b6b : EpiOk 48 slots (after b6 R5) = true ∧ (after b6 R5).mem = [] ∧
    (after b6 R5).reg .rax = some (.lit 0) := by
  decide +kernel

end NativeRustcVmX64.Layout.PushClaim
