module

public import NativeRustcVmX64.Sumcheck.Common
public import NativeRustcVmX64.Code.Vm.Climb
public import NativeRustcVmX64.Code.Vm.Climb.Names
public import NativeRustcVmX64.Code.Vm.HashPair.Names
public meta import NativeRustcVmX64.Code.Vm.Climb
public meta import NativeRustcVmX64.Sumcheck.Common

/-!
# `climb`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the 160-byte frame below the entry's RSP and the return address (`Frame`, `F = 160`:
RSP at offset `8` in the body, `hash_pair`'s return address at `0`): the accumulator at `8`, the
sibling at `40`, the output's address at `72`, `hash_pair`'s output at `80`, the six pushed
registers from `112`.

- `entryS` at the entry (`b0`, the prologue, the node (region 1, RSI) copied to the accumulator;
  then `b1`, the loop's registers): region 1 the node;
- `headS` at the loop head `NativeRustcVmX64.Vm.Climb.label_2` (`b6`, then `b7` and `b3` or `b8`, `b11`, then `b4`, the
  call): region 1 the level's sibling, at `R15 + 8 R13` (`sibS`);
- `retS` after `hash_pair` (`b5`, the new accumulator, then the head or `NativeRustcVmX64.Vm.Climb.label_9`);
- `exitS` at `NativeRustcVmX64.Vm.Climb.label_9` (`b12`): region 1 the output, its address the word at `72`.
-/

namespace NativeRustcVmX64.Sumcheck.Climb

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.Climb NativeRustcVmX64.Transcript
open NativeRustcVmX64.Sumcheck

@[expose] public section

/-- The frame's slots: the pushed registers. -/
def slots : Slots := [(152, .rbp), (144, .r15), (136, .r14), (128, .r13), (120, .r12), (112, .rbx)]

/-- The level's sibling: `R15 + 8 R13`. -/
def sibS : Sym := .bin .add .W64 (.reg .r15) (.bin .mul .W64 (.reg .r13) (.lit 8))

/-- At the entry: the frame (region 0) and the node (region 1, RSI). -/
def entryS : SState := init [168, 32] [(.rsp, .ptr 0 160), (.rsi, .ptr 1 0)]

/-- At the loop head: the frame (region 0), RBP and RBX the accumulator and the sibling, and the
level's sibling (region 1, `sibS`). -/
def headS : SState :=
  init [168, 32] [(.rsp, .ptr 0 8), (.rbp, .ptr 0 8), (.rbx, .ptr 0 40)] (aliases := [(sibS, (1, 0))])

/-- After `hash_pair`: the frame (region 0). -/
def retS : SState := init [168] [(.rsp, .ptr 0 8)]

/-- At the exit: the frame (region 0) and the output (region 1), its address the word at `72`. -/
def exitS : SState := init [168, 32] [(.rsp, .ptr 0 8)] (aliases := [(.load 0 72 8, (1, 0))])

/-- `b0`'s exit: no level. -/
def c0 : SBool := .cmp .eq .W64 (.bin .and .W64 (.reg .r8) (.reg .r8)) (.lit 0)
/-- `b6`'s exit: past the path's slice (`4 l > 124`). -/
def c6 : SBool :=
  .and (.not (.cmp .ult .W64 (.reg .r13) (.lit 124))) (.not (.cmp .eq .W64 (.reg .r13) (.lit 124)))
/-- `b7`'s exit: the position even. -/
def c7 : SBool := .cmp .eq .W8 (.bin .and .W8 (.reg .r12) (.lit 1)) (.lit 0)
/-- `b5`'s exit: the last level. -/
def c5 : SBool := .cmp .eq .W64 (.bin .sub .W64 (.reg .r14) (.lit 1)) (.lit 0)

/-- What the entry leaves: the frame set up, the node at `8`, the output's address at `72`. -/
def EntryOk (S : SState) : Prop :=
  ProOk 160 8 slots S = true ∧ WordsW 0 8 (fun i ↦ .load 1 (8 * i) 8) S ∧
    (∀ t < 8, findWrite 0 (72 + t) S.mem = some (.reg .rdi, t)) ∧
    (∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 160)

instance (S : SState) : Decidable (EntryOk S) := by unfold EntryOk; infer_instance

/-- What a level leaves at the call: the sibling at `40`, `hash_pair`'s output at `80`, the
loop's registers kept. -/
def CallOk (S : SState) : Prop :=
  MidOk 160 0 slots S = true ∧ S.reg .rdi = some (.ptr 0 80) ∧
    WordsW 0 40 (fun i ↦ .load 1 (8 * i) 8) S ∧
    (∀ w ∈ S.mem, w.r = 0 ∧ (w.off + w.n ≤ 8 ∨ 40 ≤ w.off ∧ w.off + w.n ≤ 72)) ∧
    S.reg .r12 = some (.reg .r12) ∧ S.reg .r13 = some (.reg .r13) ∧
    S.reg .r14 = some (.reg .r14) ∧ S.reg .r15 = some (.reg .r15) ∧
    S.reg .rbp = some (.ptr 0 8) ∧ S.reg .rbx = some (.ptr 0 40)

instance (S : SState) : Decidable (CallOk S) := by unfold CallOk; infer_instance

/-- The even level's state at the call. -/
abbrev evenS : SState := after b4 (after b3 (after b7 (after b6 headS)))
/-- The odd level's state at the call. -/
abbrev oddS : SState := after b4 (after b11 (after b8 (after b7 (after b6 headS))))

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b6 := exec b6 headS
sym_block run_b7 := exec b7 (after b6 headS)
sym_block run_b3 := exec b3 (after b7 (after b6 headS))
sym_block run_b4l := exec b4 (after b3 (after b7 (after b6 headS)))
sym_block run_b8 := exec b8 (after b7 (after b6 headS))
sym_block run_b11 := exec b11 (after b8 (after b7 (after b6 headS)))
sym_block run_b4r := exec b4 (after b11 (after b8 (after b7 (after b6 headS))))
sym_block run_b5 := exec b5 retS
sym_block run_b12 := exec b12 exitS

end NativeRustcVmX64.Sumcheck.Climb

namespace NativeRustcVmX64.Sumcheck.Climb

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.Climb NativeRustcVmX64.Transcript
open NativeRustcVmX64.Sumcheck

public theorem exit_b0 : exec b0 entryS = some (after b0 entryS, .cond c0 NativeRustcVmX64.Vm.Climb.label_9) :=
  run_b0.trans (by rw [after_eq run_b0]; rfl)
public theorem ok_b0 : EntryOk (after b0 entryS) := by decide +kernel
public theorem exit_b1 :
    exec b1 (after b0 entryS) = some (after b1 (after b0 entryS), .jump NativeRustcVmX64.Vm.Climb.label_2) :=
  run_b1.trans (by rw [after_eq run_b1])
public theorem ok_b1 : EntryOk (after b1 (after b0 entryS)) ∧
    (after b1 (after b0 entryS)).reg .r12 = some (.reg .rdx) ∧
    (after b1 (after b0 entryS)).reg .r13 = some (.lit 0) ∧
    (after b1 (after b0 entryS)).reg .r14 = some (.reg .r8) ∧
    (after b1 (after b0 entryS)).reg .r15 = some (.reg .rcx) ∧
    (after b1 (after b0 entryS)).reg .rbp = some (.ptr 0 8) ∧
    (after b1 (after b0 entryS)).reg .rbx = some (.ptr 0 40) := by
  decide +kernel

public theorem exit_b6 : exec b6 headS = some (after b6 headS, .cond c6 NativeRustcVmX64.Vm.Climb.label_4) :=
  run_b6.trans (by rw [after_eq run_b6]; rfl)
public theorem exit_b7 :
    exec b7 (after b6 headS) = some (after b7 (after b6 headS), .cond c7 NativeRustcVmX64.Vm.Climb.label_6) :=
  run_b7.trans (by rw [after_eq run_b7]; rfl)
public theorem exit_b3 : exec b3 (after b7 (after b6 headS)) =
    some (after b3 (after b7 (after b6 headS)), .fall) :=
  run_b3.trans (by rw [after_eq run_b3])
public theorem exit_b4l : exec b4 (after b3 (after b7 (after b6 headS))) =
    some (evenS, .call NativeRustcVmX64.Vm.HashPair.entryLabel) :=
  run_b4l.trans (by
    rw [show evenS = after b4 (after b3 (after b7 (after b6 headS))) from rfl, after_eq run_b4l])
public theorem exit_b8 : exec b8 (after b7 (after b6 headS)) =
    some (after b8 (after b7 (after b6 headS)), .jump NativeRustcVmX64.Vm.Climb.label_7) :=
  run_b8.trans (by rw [after_eq run_b8])
public theorem exit_b11 : exec b11 (after b8 (after b7 (after b6 headS))) =
    some (after b11 (after b8 (after b7 (after b6 headS))), .jump NativeRustcVmX64.Vm.Climb.label_8) :=
  run_b11.trans (by rw [after_eq run_b11])
public theorem exit_b4r : exec b4 (after b11 (after b8 (after b7 (after b6 headS)))) =
    some (oddS, .call NativeRustcVmX64.Vm.HashPair.entryLabel) :=
  run_b4r.trans (by
    rw [show oddS = after b4 (after b11 (after b8 (after b7 (after b6 headS)))) from rfl,
      after_eq run_b4r])
public theorem ok_even : CallOk evenS ∧ evenS.reg .rsi = some (.ptr 0 8) ∧
    evenS.reg .rdx = some (.ptr 0 40) := by
  decide +kernel
public theorem ok_odd : CallOk oddS ∧ oddS.reg .rsi = some (.ptr 0 40) ∧
    oddS.reg .rdx = some (.ptr 0 8) := by
  decide +kernel

public theorem exit_b5 : exec b5 retS = some (after b5 retS, .cond c5 NativeRustcVmX64.Vm.Climb.label_9) :=
  run_b5.trans (by rw [after_eq run_b5]; rfl)
public theorem ok_b5 : MidOk 160 8 slots (after b5 retS) = true ∧
    WordsW 0 8 (fun i ↦ .load 0 (80 + 8 * i) 8) (after b5 retS) ∧
    (∀ w ∈ (after b5 retS).mem, w.r = 0 ∧ 8 ≤ w.off ∧ w.off + w.n ≤ 40) ∧
    (after b5 retS).reg .r12 = some (.bin .shr .W64 (.reg .r12) (.lit 1)) ∧
    (after b5 retS).reg .r13 = some (.bin .add .W64 (.lit 4) (.reg .r13)) ∧
    (after b5 retS).reg .r14 = some (.bin .sub .W64 (.reg .r14) (.lit 1)) ∧
    (after b5 retS).reg .r15 = some (.reg .r15) ∧ (after b5 retS).reg .rbp = some (.reg .rbp) ∧
    (after b5 retS).reg .rbx = some (.reg .rbx) := by
  decide +kernel

public theorem exit_b12 : exec b12 exitS = some (after b12 exitS, .ret (.load 0 160 8)) :=
  run_b12.trans (by rw [after_eq run_b12])
public theorem ok_b12 : EpiOk 160 slots (after b12 exitS) = true ∧
    WordsW 1 0 (fun i ↦ .load 0 (8 + 8 * i) 8) (after b12 exitS) ∧
    (∀ w ∈ (after b12 exitS).mem, w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 32) := by
  decide +kernel

end NativeRustcVmX64.Sumcheck.Climb
