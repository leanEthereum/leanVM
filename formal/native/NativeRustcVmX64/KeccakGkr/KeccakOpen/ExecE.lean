module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.States
public import NativeRustcVmX64.Code.Vm.KeccakOpen
public import NativeRustcVmX64.Code.Vm.KeccakOpen.Names
public import NativeRustcVmX64.Code.Vm.SlotWeights.Names
public import NativeRustcVmX64.Code.Vm.SumcheckOfSumcheckPlain.Names
public meta import NativeRustcVmX64.KeccakGkr.KeccakOpen.States
public meta import NativeRustcVmX64.Code.Vm.KeccakOpen

/-!
# `keccak_open`'s blocks, run by the symbolic executor (x86-64): the entry and the exit

`b0` the prologue and `sumcheck`'s call, `b1` its test, `b2` the value saved and `slot_weights`'
call, `b3` its test, `b4` the result's address saved and round 0's start; `b93` the result's
value, `b94` `None`, `b95` the tag and the epilogue.
-/

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.KeccakOpen NativeRustcVmX64.Transcript

set_option Elab.async false

sym_block e0 := exec b0 e0S
sym_block e1 := exec b1 (pS [])
sym_block e2 := exec b2 (pS [])
sym_block e3 := exec b3 (pS [])
sym_block e4 := exec b4 (pS [(.r15, P)])
sym_block e93 := exec b93 outS
sym_block e94 := exec b94 (pS [])
sym_block e95 := exec b95 resS

public section

theorem f0 : b0.length = 20 ∧ ProOk 2208 0 slots (after b0 e0S) = true ∧
    (∀ w ∈ (after b0 e0S).mem, w.r = 0 ∧ (w.off + w.n ≤ 16 ∨ 2160 ≤ w.off ∧ w.off + w.n ≤ 2208)) ∧
    (∀ i < 8, findWrite 0 (8 + i) (after b0 e0S).mem = some (.lit 6, i)) ∧
    (after b0 e0S).reg .rdi = some (.ptr 0 88) ∧ (after b0 e0S).reg .rsi = some (.reg .rsi) ∧
    (after b0 e0S).reg .rdx = some (.load 3 16 8) ∧ (after b0 e0S).reg .rcx = some (.load 3 24 8) ∧
    (after b0 e0S).reg .r8 = some (.lit 3) ∧ (after b0 e0S).reg .r9 = some (.load 3 32 8) ∧
    (after b0 e0S).reg .rbx = some (.reg .rdi) ∧ (after b0 e0S).reg .rbp = some (.reg .rdx) ∧
    (after b0 e0S).reg .r12 = some (.reg .r8) ∧ (after b0 e0S).reg .r13 = some (.reg .rcx) ∧
    (after b0 e0S).reg .r14 = some (.reg .r9) := by
  rw [after_eq e0]; decide +kernel

theorem x0 : exec b0 e0S = some (after b0 e0S, .call
    NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.entryLabel) :=
  e0.trans (by rw [after_eq e0])

theorem f1 : b1.length = 2 ∧ MidOk 2208 8 slots (after b1 (pS [])) = true ∧
    (after b1 (pS [])).mem = [] ∧
    atoms (after b1 (pS [])) [.rbx, .rbp, .r12, .r13, .r14] = true := by
  rw [after_eq e1]; decide +kernel

theorem x1 : exec b1 (pS []) = some (after b1 (pS []),
    .cond (.not (.cmp .eq .W32 (.load 0 88 4) (.lit 1))) NativeRustcVmX64.Vm.KeccakOpen.label_2) :=
  e1.trans (by rw [after_eq e1])

theorem f2 : b2.length = 13 ∧ MidOk 2208 0 slots (after b2 (pS [])) = true ∧
    (∀ w ∈ (after b2 (pS [])).mem, w.r = 0 ∧ w.off + w.n ≤ 88) ∧
    (∀ i < 8, findWrite 0 (8 + i) (after b2 (pS [])).mem = some (.load 3 40 8, i)) ∧
    (∀ i < 8, findWrite 0 (72 + i) (after b2 (pS [])).mem = some (.load 0 104 8, i)) ∧
    (∀ i < 8, findWrite 0 (80 + i) (after b2 (pS [])).mem = some (.load 0 96 8, i)) ∧
    (after b2 (pS [])).reg .rdi = some (.reg .rbp) ∧ (after b2 (pS [])).reg .rsi = some (.reg .r13) ∧
    (after b2 (pS [])).reg .rdx = some (.reg .r12) ∧ (after b2 (pS [])).reg .rcx = some (.reg .r14) ∧
    (after b2 (pS [])).reg .r8 = some (.load 3 0 8) ∧ (after b2 (pS [])).reg .r9 = some (.load 3 8 8) ∧
    (after b2 (pS [])).reg .r15 = some (.load 3 40 8) ∧ atoms (after b2 (pS [])) [.rbx] = true := by
  rw [after_eq e2]; decide +kernel

theorem x2 : exec b2 (pS []) = some (after b2 (pS []),
    .call NativeRustcVmX64.Vm.SlotWeights.entryLabel) :=
  e2.trans (by rw [after_eq e2])

theorem f3 : b3.length = 2 ∧ MidOk 2208 8 slots (after b3 (pS [])) = true ∧
    (after b3 (pS [])).mem = [] ∧ atoms (after b3 (pS [])) [.rbx, .r15] = true := by
  rw [after_eq e3]; decide +kernel

theorem x3 : exec b3 (pS []) = some (after b3 (pS []),
    .cond (.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)) NativeRustcVmX64.Vm.KeccakOpen.label_2) :=
  e3.trans (by rw [after_eq e3])

theorem f4 : b4.length = 7 ∧ MidOk 2208 8 slots (after b4 (pS [(.r15, P)])) = true ∧
    (after b4 (pS [(.r15, P)])).mem = [⟨0, 64, 8, .reg .rbx⟩] ∧
    regsOk (klOf 0 []) (after b4 (pS [(.r15, P)]))
      [(.r12, V0), (.r13, V1), (.rbx, .lit 0), (.r14, P)] = true := by
  rw [after_eq e4]; decide +kernel

theorem x4 : exec b4 (pS [(.r15, P)]) = some (after b4 (pS [(.r15, P)]), .fall) :=
  e4.trans (by rw [after_eq e4])

theorem f93 : b93.length = 7 ∧ MidOk 2208 8 slots (after b93 outS) = true ∧
    (after b93 outS).mem = [⟨1, 16, 8, .load 0 72 8⟩, ⟨1, 8, 8, .load 0 80 8⟩] ∧
    (after b93 outS).reg .rbx = some (.load 0 64 8) ∧ (after b93 outS).reg .rax = some (.lit 1) := by
  rw [after_eq e93]; decide +kernel

theorem x93 : exec b93 outS = some (after b93 outS, .jump NativeRustcVmX64.Vm.KeccakOpen.label_3) :=
  e93.trans (by rw [after_eq e93])

theorem f94 : b94.length = 2 ∧ MidOk 2208 8 slots (after b94 (pS [])) = true ∧
    (after b94 (pS [])).mem = [] ∧ (after b94 (pS [])).reg .rax = some (.lit 0) ∧
    atoms (after b94 (pS [])) [.rbx] = true := by
  rw [after_eq e94]; decide +kernel

theorem x94 : exec b94 (pS []) = some (after b94 (pS []), .fall) :=
  e94.trans (by rw [after_eq e94])

theorem f95 : b95.length = 10 ∧ EpiOk 2208 slots (after b95 resS) = true ∧
    (after b95 resS).mem = [⟨1, 0, 8, .reg .rax⟩] := by
  rw [after_eq e95]; decide +kernel

theorem x95 : exec b95 resS = some (after b95 resS, .ret (.load 0 2208 8)) :=
  e95.trans (by rw [after_eq e95])

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
