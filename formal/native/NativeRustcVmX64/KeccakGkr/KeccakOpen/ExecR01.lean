module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.States
public import NativeRustcVmX64.Code.Vm.KeccakOpen
public import NativeRustcVmX64.Code.Vm.KeccakOpen.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public meta import NativeRustcVmX64.KeccakGkr.KeccakOpen.States
public meta import NativeRustcVmX64.Code.Vm.KeccakOpen

/-!
# `keccak_open`'s blocks, run by the symbolic executor (x86-64): rounds 0 and 1, the rows' copies and loop tests
-/

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.KeccakOpen NativeRustcVmX64.Transcript

set_option Elab.async false

sym_block e5 := exec b5 (pS kR0)
sym_block e6 := exec b6 (pS k5)
sym_block e7 := exec b7 (pS k5)
sym_block e10 := exec b10 (pS kI0)
sym_block e11 := exec b11 (pS [])
sym_block e12 := exec b12 (pS kR1)
sym_block e13 := exec b13 (pS k12)
sym_block e14 := exec b14 (pS k12)
sym_block e17 := exec b17 (pS kI1)

public section

theorem f5 : b5.length = 9 ∧ mOk 112 (srcA0) 0 [] (after b5 (pS kR0)) k5 w5 = true := by
  rw [after_eq e5]; decide +kernel

theorem x5 : exec b5 (pS kR0) = some ((after b5 (pS kR0)), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e5.trans (by rw [after_eq e5])

theorem f6 : b6.length = 5 ∧ mOk 1136 (srcB0) 0 w5 (after b6 (pS k5)) k5 w5 = true := by
  rw [after_eq e6]; decide +kernel

theorem x6 : exec b6 (pS k5) = some ((after b6 (pS k5)), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e6.trans (by rw [after_eq e6])

theorem f7 : b7.length = 2 ∧ blkOk 8 0 w5 (after b7 (pS k5)) k7 w5 = true := by
  rw [after_eq e7]; decide +kernel

theorem x7 : exec b7 (pS k5) = some ((after b7 (pS k5)), .fall) :=
  e7.trans (by rw [after_eq e7])

theorem f10 : b10.length = 5 ∧ blkOk 8 0 w5 (after b10 (pS kI0)) k10 [] = true := by
  rw [after_eq e10]; decide +kernel

theorem x10 : exec b10 (pS kI0) = some ((after b10 (pS kI0)), .cond (.not (.cmp .eq .W64 (.bin .add .W64 (.load 0 16 8) (.lit 1)) (.lit 32))) NativeRustcVmX64.Vm.KeccakOpen.label_41) :=
  e10.trans (by rw [after_eq e10])

theorem f11 : b11.length = 6 ∧ blkOk 8 1 [] (after b11 (pS [])) k11 [] = true := by
  rw [after_eq e11]; decide +kernel

theorem x11 : exec b11 (pS []) = some ((after b11 (pS [])), .fall) :=
  e11.trans (by rw [after_eq e11])

theorem f12 : b12.length = 9 ∧ mOk 112 (srcA0) 1 [] (after b12 (pS kR1)) k12 w5 = true := by
  rw [after_eq e12]; decide +kernel

theorem x12 : exec b12 (pS kR1) = some ((after b12 (pS kR1)), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e12.trans (by rw [after_eq e12])

theorem f13 : b13.length = 5 ∧ mOk 1136 (srcB0) 1 w5 (after b13 (pS k12)) k12 w5 = true := by
  rw [after_eq e13]; decide +kernel

theorem x13 : exec b13 (pS k12) = some ((after b13 (pS k12)), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e13.trans (by rw [after_eq e13])

theorem f14 : b14.length = 2 ∧ blkOk 8 1 w5 (after b14 (pS k12)) k14 w5 = true := by
  rw [after_eq e14]; decide +kernel

theorem x14 : exec b14 (pS k12) = some ((after b14 (pS k12)), .fall) :=
  e14.trans (by rw [after_eq e14])

theorem f17 : b17.length = 5 ∧ blkOk 8 1 w5 (after b17 (pS kI1)) k17 [] = true := by
  rw [after_eq e17]; decide +kernel

theorem x17 : exec b17 (pS kI1) = some ((after b17 (pS kI1)), .cond (.not (.cmp .eq .W64 (.bin .add .W64 (.load 0 16 8) (.lit 1)) (.lit 16))) NativeRustcVmX64.Vm.KeccakOpen.label_5) :=
  e17.trans (by rw [after_eq e17])

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
