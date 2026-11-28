module

public import NativeRustcVmX64.Tables.TableTerms.Body
public import NativeRustcVmX64.Field.Frame
public import NativeRustcVmX64.Code.Vm.ReadAnnouncedSizes
public import NativeRustcVmX64.Code.Vm.BuildLayout.Names
public import NativeRustcVmX64.Code.Vm.ReadAnnouncedSizes.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names
public meta import NativeRustcVmX64.Code.Vm.ReadAnnouncedSizes
public meta import NativeRustcVmX64.Tables.TableTerms.Body
public meta import NativeRustcVmX64.Field.Frame

/-!
# `read_announced_sizes`' blocks, run by the symbolic executor (x86-64)

Region 0 is the 208-byte frame below the entry's RSP and the return address (`Frame`, `F = 208`:
RSP at offset `8` in the body, a callee's return address at `0`): `announced` (eight elements) at
`8`, the rows `b10` copies at `136`, the pushed registers from `184`.

- `entryS` (`b0`: the prologue, `announced` zeroed, the call of `read_scalars`);
- `frS` (`b1`-`b12`, `b14`, `b15`): the frame;
- `b15d`: `b15` from its second label;
- `layS` (`b13`): region 1 the layout's first 24 bytes (RBX), its `stack_log` at `16`.
-/

namespace NativeRustcVmX64.Layout.ReadAnnouncedSizes

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.ReadAnnouncedSizes
open NativeRustcVmX64.Transcript NativeRustcVmX64.Tables.Body

@[expose] public section

/-- The pushed registers' slots. -/
def slots : Slots := [(200, .r15), (192, .r14), (184, .rbx)]
/-- At the entry. -/
abbrev entryS : SState := NativeRustcVmX64.Field.frameS 208
/-- In the body. -/
abbrev frS : SState := NativeRustcVmX64.Field.midS 208
/-- `b13`: the layout's first 24 bytes. -/
def layS : SState := init [216, 24] [(.rsp, .ptr 0 8)] [] [] [(.reg .rbx, 1, 0)]

/-- `b1`'s test: `read_scalars`' `bool` zero. -/
def c1 : SBool :=
  .cmp .eq .W8 (.bin .and .W8 (.un .trunc .W32 (.reg .rax)) (.un .trunc .W32 (.reg .rax))) (.lit 0)
/-- A high limb's test: the frame's word at `o` nonzero. -/
def cnz (o : Nat) : SBool := (SBool.cmp .eq .W64 (.load 0 o 8) (.lit 0)).not
/-- `rate - 1`. -/
def r10S : Sym := .bin .add .W64 (.load 0 120 8) (.lit 18446744073709551615)
/-- `b10`'s test: `rate - 1 > 3`. -/
def c10 : SBool := (SBool.cmp .ult .W64 r10S (.lit 3)).not.and (SBool.cmp .eq .W64 r10S (.lit 3)).not
/-- `b12`'s test: `build_layout`'s `bool` zero. -/
def c12 : SBool := .cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)
/-- `b15` from its second label, `NativeRustcVmX64.Vm.ReadAnnouncedSizes.label_22`. -/
def b15d : List Directive := b15.drop 1
/-- The high limbs' checks keep RAX, RBX, R14 and write nothing. -/
abbrev OkC (S : SState) : Prop :=
  MidOk 208 8 slots S = true ∧ S.mem = [] ∧ Keeps S [.rax, .rbx, .r14] = true
/-- `b13`'s RAX: `stack_log - 16 < 15`. -/
def ax13 : Sym := .bin .merge .W8 (.lit 0)
  (.ite (.cmp .ult .W64 (.bin .add .W64 (.lit 18446744073709551600) (.load 1 16 8)) (.lit 15))
    (.lit 1) (.lit 0))

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 frS
sym_block run_b2 := exec b2 frS
sym_block run_b3 := exec b3 frS
sym_block run_b4 := exec b4 frS
sym_block run_b5 := exec b5 frS
sym_block run_b6 := exec b6 frS
sym_block run_b7 := exec b7 frS
sym_block run_b8 := exec b8 frS
sym_block run_b9 := exec b9 frS
sym_block run_b10 := exec b10 frS
sym_block run_b11 := exec b11 frS
sym_block run_b12 := exec b12 frS
sym_block run_b13 := exec b13 layS
sym_block run_b14 := exec b14 frS
sym_block run_b15 := exec b15 frS
sym_block run_b15d := exec b15d frS

public theorem exit_b0 : exec b0 entryS = some (after b0 entryS,
    .call NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) :=
  run_b0.trans (by rw [after_eq run_b0])
public theorem ok_b0 : ProOk 208 0 slots (after b0 entryS) = true ∧
    WrOk (after b0 entryS) [] = true ∧
    (after b0 entryS).reg .rsi = some (.ptr 0 8) ∧ (after b0 entryS).reg .rdx = some (.lit 8) ∧
    (after b0 entryS).reg .rdi = some (.reg .rdi) ∧ (after b0 entryS).reg .rbx = some (.reg .rdx) ∧
    (after b0 entryS).reg .r14 = some (.reg .rsi) := by
  decide +kernel

public theorem exit_b1 : exec b1 frS = some (after b1 frS, .cond c1 NativeRustcVmX64.Vm.ReadAnnouncedSizes.label_21) :=
  run_b1.trans (by rw [after_eq run_b1]; rfl)
public theorem ok_b1 : MidOk 208 8 slots (after b1 frS) = true ∧ (after b1 frS).mem = [] ∧
    (after b1 frS).reg .rax = some (.lit 0) ∧ Keeps (after b1 frS) [.rbx, .r14] = true := by
  decide +kernel


public theorem exit_b2 : exec b2 frS = some (after b2 frS, .cond (cnz 16) NativeRustcVmX64.Vm.ReadAnnouncedSizes.label_21) :=
  run_b2.trans (by rw [after_eq run_b2]; rfl)
public theorem exit_b3 : exec b3 frS = some (after b3 frS, .cond (cnz 32) NativeRustcVmX64.Vm.ReadAnnouncedSizes.label_21) :=
  run_b3.trans (by rw [after_eq run_b3]; rfl)
public theorem exit_b4 : exec b4 frS = some (after b4 frS, .cond (cnz 48) NativeRustcVmX64.Vm.ReadAnnouncedSizes.label_21) :=
  run_b4.trans (by rw [after_eq run_b4]; rfl)
public theorem exit_b5 : exec b5 frS = some (after b5 frS, .cond (cnz 64) NativeRustcVmX64.Vm.ReadAnnouncedSizes.label_21) :=
  run_b5.trans (by rw [after_eq run_b5]; rfl)
public theorem exit_b6 : exec b6 frS = some (after b6 frS, .cond (cnz 80) NativeRustcVmX64.Vm.ReadAnnouncedSizes.label_21) :=
  run_b6.trans (by rw [after_eq run_b6]; rfl)
public theorem exit_b7 : exec b7 frS = some (after b7 frS, .cond (cnz 96) NativeRustcVmX64.Vm.ReadAnnouncedSizes.label_21) :=
  run_b7.trans (by rw [after_eq run_b7]; rfl)
public theorem exit_b8 : exec b8 frS = some (after b8 frS, .cond (cnz 112) NativeRustcVmX64.Vm.ReadAnnouncedSizes.label_21) :=
  run_b8.trans (by rw [after_eq run_b8]; rfl)
public theorem exit_b9 : exec b9 frS = some (after b9 frS, .cond (cnz 128) NativeRustcVmX64.Vm.ReadAnnouncedSizes.label_22) :=
  run_b9.trans (by rw [after_eq run_b9]; rfl)
public theorem ok_b2_b9 : OkC (after b2 frS) ∧ OkC (after b3 frS) ∧ OkC (after b4 frS) ∧
    OkC (after b5 frS) ∧ OkC (after b6 frS) ∧ OkC (after b7 frS) ∧ OkC (after b8 frS) ∧
    OkC (after b9 frS) := by
  decide +kernel

public theorem exit_b10 : exec b10 frS = some (after b10 frS, .cond c10 NativeRustcVmX64.Vm.ReadAnnouncedSizes.label_13) :=
  run_b10.trans (by rw [after_eq run_b10]; rfl)
public theorem ok_b10 : MidOk 208 8 slots (after b10 frS) = true ∧ WrOk (after b10 frS) [] = true ∧
    (∀ w ∈ (after b10 frS).mem, w.r = 0 ∧ 136 ≤ w.off ∧ w.off + w.n ≤ 184) ∧
    (∀ t < 6, ∀ i < 8, findWrite 0 (136 + 8 * t + i) (after b10 frS).mem =
      some (.load 0 (24 + 16 * t) 8, i)) ∧
    (after b10 frS).reg .r15 = some (.load 0 120 8) ∧ (after b10 frS).reg .rsi = some (.load 0 8 8) ∧
    Keeps (after b10 frS) [.rbx, .r14] = true := by
  decide +kernel

public theorem exit_b11 : exec b11 frS = some (after b11 frS,
    .call NativeRustcVmX64.Vm.BuildLayout.entryLabel) :=
  run_b11.trans (by rw [after_eq run_b11])
public theorem ok_b11 : MidOk 208 0 slots (after b11 frS) = true ∧ WrOk (after b11 frS) [] = true ∧
    (∀ w ∈ (after b11 frS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b11 frS).reg .rdx = some (.ptr 0 136) ∧ (after b11 frS).reg .rdi = some (.reg .r14) ∧
    (after b11 frS).reg .rcx = some (.reg .rbx) ∧
    Keeps (after b11 frS) [.rsi, .rbx, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b12 : exec b12 frS = some (after b12 frS, .cond c12 NativeRustcVmX64.Vm.ReadAnnouncedSizes.label_13) :=
  run_b12.trans (by rw [after_eq run_b12]; rfl)
public theorem ok_b12 : MidOk 208 8 slots (after b12 frS) = true ∧ (after b12 frS).mem = [] ∧
    Keeps (after b12 frS) [.rbx, .r15] = true := by
  decide +kernel

public theorem exit_b13 : exec b13 layS = some (after b13 layS, .jump NativeRustcVmX64.Vm.ReadAnnouncedSizes.label_22) :=
  run_b13.trans (by rw [after_eq run_b13])
public theorem ok_b13 : MidOk 208 8 slots (after b13 layS) = true ∧ (after b13 layS).mem = [] ∧
    (after b13 layS).reg .rax = some ax13 ∧ Keeps (after b13 layS) [.r15] = true := by
  decide +kernel

public theorem exit_b14 : exec b14 frS = some (after b14 frS, .jump NativeRustcVmX64.Vm.ReadAnnouncedSizes.label_22) :=
  run_b14.trans (by rw [after_eq run_b14])
public theorem ok_b14 : MidOk 208 8 slots (after b14 frS) = true ∧ (after b14 frS).mem = [] ∧
    (after b14 frS).reg .rax = some (.lit 0) := by
  decide +kernel

public theorem exit_b15 : exec b15 frS = some (after b15 frS, .ret (.load 0 208 8)) :=
  run_b15.trans (by rw [after_eq run_b15])
public theorem ok_b15 : EpiOk 208 slots (after b15 frS) = true ∧ (after b15 frS).mem = [] ∧
    (after b15 frS).reg .rax = some (.reg .rax) ∧ (after b15 frS).reg .rdx = some (.reg .r15) := by
  decide +kernel

public theorem exit_b15d : exec b15d frS = some (after b15d frS, .ret (.load 0 208 8)) :=
  run_b15d.trans (by rw [after_eq run_b15d])
public theorem ok_b15d : EpiOk 208 slots (after b15d frS) = true ∧ (after b15d frS).mem = [] ∧
    (after b15d frS).reg .rax = some (.reg .rax) ∧ (after b15d frS).reg .rdx = some (.reg .r15) := by
  decide +kernel

public theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 208 := by decide
public theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide

end NativeRustcVmX64.Layout.ReadAnnouncedSizes
