module

public import NativeRustcX64.Code.Common.Finalize.Names
public import NativeRustcX64.Code.Common.Memcpy.Names
public import NativeRustcX64.Code.Common.Update.Names
public import NativeRustcX64.Code.Xmss.XmssVerify.Names

public import NativeRustcX64.XmssVerify.Turn
public import NativeRustcX64.XmssVerify.Bottom

/-!
# `xmss_verify`: a turn of the loop over the bottom layer's path (x86-64)

Block 9 (the head, `.LXmssVerify_4`): the children of the current node at `592` and the path
node at `R12` stored at `88` in the order bit `z` of the key index says, the address at `24`,
`RBP` to `z + 1`, `memset` of the hasher at `184`. Blocks 10 to 14: the node's hash
(`hashNode`). Block 15: its first 16 bytes to the current node, `R12` to the next path node, back
to block 9 until `RBP = 16` (`turn0`).
-/

namespace NativeRustcX64.Xmss.XmssVerify

open NativeRustcX64.Sym LeanVM.Protocol.KeccakHash NativeRustc NativeRustc.Xmss

set_option Elab.async false

@[expose] public section

/-- `RBP + 1`. -/
def rbp1 : Sym := .bin .add .W64 (.reg .rbp) (.lit 1)

end

public section

theorem st9_regs : (after b9 st9).reg .rdi = some (.ptr 0 184) ∧
    (after b9 st9).reg .rsi = some (.lit 0) ∧ (after b9 st9).reg .rdx = some (.lit 344) ∧
    (after b9 st9).reg .rsp = some (.ptr 0 16) ∧ (after b9 st9).reg .rbp = some rbp1 ∧
    (after b9 st9).reg .r14 = some (.ptr 0 592) ∧ (after b9 st9).reg .r12 = some (.ptr 1 0) ∧
    (after b9 st9).reg .r15 = some (.ptr 0 184) ∧ (after b9 st9).reg .rbx = some (.reg .rbx) ∧
    writesBelow (after b9 st9) [(0, 136)] = true ∧
    (∀ w ∈ (after b9 st9).mem, w.r = 0 ∧ (w.off + w.n ≤ 40 ∨ 88 ≤ w.off)) := by
  decide +kernel

theorem st9_children :
    (∀ t < 8, findWrite 0 (88 + t) (after b9 st9).mem =
      some (.ite (bitC (.reg .rbp)) (.load 0 592 8) (.load 1 0 8), t)) ∧
    (∀ t < 8, findWrite 0 (96 + t) (after b9 st9).mem =
      some (.ite (bitC (.reg .rbp)) (.load 0 600 8) (.load 1 8 8), t)) ∧
    (∀ t < 8, findWrite 0 (104 + t) (after b9 st9).mem =
      some (.ite (bitC (.reg .rbp)) (.load 1 0 8) (.load 0 592 8), t)) ∧
    (∀ t < 8, findWrite 0 (112 + t) (after b9 st9).mem =
      some (.ite (bitC (.reg .rbp)) (.load 1 8 8) (.load 0 600 8), t)) := by
  decide +kernel

theorem st9_addr :
    (∀ t < 4, findWrite 0 (24 + t) (after b9 st9).mem = some (loW rbp1, t)) ∧
    (∀ t < 2, findWrite 0 (28 + t) (after b9 st9).mem = some (.un .trunc .W16 rbp1, t)) ∧
    (∀ t < 1, findWrite 0 (30 + t) (after b9 st9).mem =
      some (.un .trunc .W8 (.bin .shr .W32 (.un .trunc .W32 rbp1) (.lit 16)), t)) ∧
    (∀ t < 1, findWrite 0 (31 + t) (after b9 st9).mem = some (.lit 3, t)) ∧
    (∀ t < 8, findWrite 0 (32 + t) (after b9 st9).mem = some (.lit 0, t)) := by
  decide +kernel

theorem run_b10' : exec b10 stH = some (after b10 stH, .call NativeRustcX64.Common.Update.entryLabel) := by
  rw [after_eq run_b10]; exact run_b10

theorem run_b11' : exec b11 stH = some (after b11 stH, .call NativeRustcX64.Common.Update.entryLabel) := by
  rw [after_eq run_b11]; exact run_b11

theorem run_b12' : exec b12 stH = some (after b12 stH, .call NativeRustcX64.Common.Memcpy.entryLabel) := by
  rw [after_eq run_b12]; exact run_b12

theorem run_b13' : exec b13 stH1 = some (after b13 stH1, .call NativeRustcX64.Common.Update.entryLabel) := by
  rw [after_eq run_b13]; exact run_b13

theorem run_b14' : exec b14 stH1 = some (after b14 stH1, .call NativeRustcX64.Common.Finalize.entryLabel) := by
  rw [after_eq run_b14]; exact run_b14

theorem f10 : (writesBelow (after b10 stH) [(0, 24)] = true ∧ keepsBut .r13 stH (after b10 stH) = true ∧
      (after b10 stH).reg .rsp = some (.ptr 0 16)) ∧ (after b10 stH).reg .rdi = some (.ptr 0 184) ∧
    (after b10 stH).reg .rsi = some (.ptr 0 56) ∧ (after b10 stH).reg .rdx = some (.lit 16) := by
  decide +kernel

theorem f11 : (writesBelow (after b11 stH) [(0, 24)] = true ∧ keepsBut .r13 stH (after b11 stH) = true ∧
      (after b11 stH).reg .rsp = some (.ptr 0 16)) ∧ (after b11 stH).reg .rdi = some (.ptr 0 184) ∧
    (after b11 stH).reg .rsi = some (.ptr 0 24) ∧ (after b11 stH).reg .rdx = some (.lit 16) := by
  decide +kernel

theorem f12 : (writesBelow (after b12 stH) [(0, 24)] = true ∧ keepsBut .r13 stH (after b12 stH) = true ∧
      (after b12 stH).reg .rsp = some (.ptr 0 16)) ∧ (after b12 stH).reg .rdi = some (.ptr 0 608) ∧
    (after b12 stH).reg .rsi = some (.ptr 0 184) ∧ (after b12 stH).reg .rdx = some (.lit 344) ∧
    (after b12 stH).reg .r15 = some (.ptr 0 184) ∧ (after b12 stH).reg .r13 = some (.ptr 0 608) := by
  decide +kernel

theorem f13 : (writesBelow (after b13 stH1) [(0, 24)] = true ∧
      keepsBut .r13 stH1 (after b13 stH1) = true ∧ (after b13 stH1).reg .rsp = some (.ptr 0 16)) ∧
    (after b13 stH1).reg .rdi = some (.ptr 0 608) ∧ (after b13 stH1).reg .rsi = some (.ptr 0 88) ∧
    (after b13 stH1).reg .rdx = some (.lit 32) ∧ (after b13 stH1).reg .r13 = some (.ptr 0 608) := by
  decide +kernel

theorem f14 : (writesBelow (after b14 stH1) [(0, 24)] = true ∧
      keepsBut .r13 stH1 (after b14 stH1) = true ∧ (after b14 stH1).reg .rsp = some (.ptr 0 16)) ∧
    (after b14 stH1).reg .rdi = some (.ptr 0 184) ∧ (after b14 stH1).reg .rsi = some (.ptr 0 608) := by
  decide +kernel

/-- Another turn: `RBP ≠ 16`. -/
theorem run_b15' : exec b15 st15 = some (after b15 st15,
    .cond (.not (.cmp .eq .W64 (.reg .rbp) (.lit 16))) NativeRustcX64.Xmss.XmssVerify.label_4) := by
  rw [after_eq run_b15]; exact run_b15

theorem st15_facts : (after b15 st15).reg .rsp = some (.ptr 0 24) ∧
    (after b15 st15).reg .r12 = some (.ptr 1 16) ∧
    (∀ r ∈ [Reg64.rbx, .rbp, .r15], (after b15 st15).reg r = some (.reg r)) ∧
    writesBelow (after b15 st15) [(0, 608)] = true ∧
    (∀ w ∈ (after b15 st15).mem, w.r = 0 ∧ (w.off + w.n ≤ 24 ∨ 592 ≤ w.off)) ∧
    (∀ t < 8, findWrite 0 (592 + t) (after b15 st15).mem = some (.load 0 184 8, t)) ∧
    (∀ t < 8, findWrite 0 (600 + t) (after b15 st15).mem = some (.load 0 192 8, t)) := by
  decide +kernel

end

end NativeRustcX64.Xmss.XmssVerify
