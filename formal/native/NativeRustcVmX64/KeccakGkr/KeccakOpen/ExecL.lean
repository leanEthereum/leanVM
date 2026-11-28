module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.States
public import NativeRustcVmX64.Code.Vm.KeccakOpen
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public meta import NativeRustcVmX64.KeccakGkr.KeccakOpen.States
public meta import NativeRustcVmX64.Code.Vm.KeccakOpen

/-!
# `keccak_open`'s blocks, run by the symbolic executor (x86-64): the inner loops' loads
-/

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.KeccakOpen NativeRustcVmX64.Transcript

set_option Elab.async false

sym_block e8 := exec b8 (loS .rbx 8)
sym_block e15 := exec b15 (loS .rbp 8)
sym_block e21 := exec b21 (loS .rbx 8)
sym_block e26 := exec b26 (loS .rbx 1032)
sym_block e31 := exec b31 (loS .rbx 2048)
sym_block e36 := exec b36 (loS .rbx 3072)
sym_block e41 := exec b41 (loS .rbx 4096)
sym_block e46 := exec b46 (loS .rbx 5128)
sym_block e51 := exec b51 (loS .rbx 6152)
sym_block e56 := exec b56 (loS .rbx 7168)
sym_block e61 := exec b61 (loS .rbx 8)
sym_block e66 := exec b66 (loS .rbx 1032)
sym_block e71 := exec b71 (loS .rbx 2048)
sym_block e76 := exec b76 (loS .rbx 3072)
sym_block e81 := exec b81 (loS .rbx 8)
sym_block e86 := exec b86 (loS .rbx 1032)
sym_block e91 := exec b91 (loS .rbx 0)

public section

theorem f8 : b8.length = 10 ∧ lOk .r12 .r13 .rbp .r15 [.rbx, .r12, .r13, .r14] (after b8 (loS .rbx 8)) = true := by
  rw [after_eq e8]; decide +kernel

theorem x8 : exec b8 (loS .rbx 8) = some ((after b8 (loS .rbx 8)), .call NativeRustcVmX64.Vm.EWMul.entryLabel) :=
  e8.trans (by rw [after_eq e8])

theorem f15 : b15.length = 10 ∧ lOk .r12 .r13 .r14 .r15 [.rbp, .r12, .r13, .rbx] (after b15 (loS .rbp 8)) = true := by
  rw [after_eq e15]; decide +kernel

theorem x15 : exec b15 (loS .rbp 8) = some ((after b15 (loS .rbp 8)), .call NativeRustcVmX64.Vm.EWMul.entryLabel) :=
  e15.trans (by rw [after_eq e15])

theorem f21 : b21.length = 10 ∧ lOk .rbp .r12 .r14 .r15 [.rbx, .rbp, .r12, .r13] (after b21 (loS .rbx 8)) = true := by
  rw [after_eq e21]; decide +kernel

theorem x21 : exec b21 (loS .rbx 8) = some ((after b21 (loS .rbx 8)), .call NativeRustcVmX64.Vm.EWMul.entryLabel) :=
  e21.trans (by rw [after_eq e21])

theorem f26 : b26.length = 10 ∧ lOk .rbp .r12 .r14 .r15 [.rbx, .rbp, .r12, .r13] (after b26 (loS .rbx 1032)) = true := by
  rw [after_eq e26]; decide +kernel

theorem x26 : exec b26 (loS .rbx 1032) = some ((after b26 (loS .rbx 1032)), .call NativeRustcVmX64.Vm.EWMul.entryLabel) :=
  e26.trans (by rw [after_eq e26])

theorem f31 : b31.length = 10 ∧ lOk .rbp .r12 .r14 .r15 [.rbx, .rbp, .r12, .r13] (after b31 (loS .rbx 2048)) = true := by
  rw [after_eq e31]; decide +kernel

theorem x31 : exec b31 (loS .rbx 2048) = some ((after b31 (loS .rbx 2048)), .call NativeRustcVmX64.Vm.EWMul.entryLabel) :=
  e31.trans (by rw [after_eq e31])

theorem f36 : b36.length = 10 ∧ lOk .rbp .r12 .r14 .r15 [.rbx, .rbp, .r12, .r13] (after b36 (loS .rbx 3072)) = true := by
  rw [after_eq e36]; decide +kernel

theorem x36 : exec b36 (loS .rbx 3072) = some ((after b36 (loS .rbx 3072)), .call NativeRustcVmX64.Vm.EWMul.entryLabel) :=
  e36.trans (by rw [after_eq e36])

theorem f41 : b41.length = 10 ∧ lOk .rbp .r12 .r14 .r15 [.rbx, .rbp, .r12, .r13] (after b41 (loS .rbx 4096)) = true := by
  rw [after_eq e41]; decide +kernel

theorem x41 : exec b41 (loS .rbx 4096) = some ((after b41 (loS .rbx 4096)), .call NativeRustcVmX64.Vm.EWMul.entryLabel) :=
  e41.trans (by rw [after_eq e41])

theorem f46 : b46.length = 10 ∧ lOk .rbp .r12 .r14 .r15 [.rbx, .rbp, .r12, .r13] (after b46 (loS .rbx 5128)) = true := by
  rw [after_eq e46]; decide +kernel

theorem x46 : exec b46 (loS .rbx 5128) = some ((after b46 (loS .rbx 5128)), .call NativeRustcVmX64.Vm.EWMul.entryLabel) :=
  e46.trans (by rw [after_eq e46])

theorem f51 : b51.length = 10 ∧ lOk .rbp .r12 .r14 .r15 [.rbx, .rbp, .r12, .r13] (after b51 (loS .rbx 6152)) = true := by
  rw [after_eq e51]; decide +kernel

theorem x51 : exec b51 (loS .rbx 6152) = some ((after b51 (loS .rbx 6152)), .call NativeRustcVmX64.Vm.EWMul.entryLabel) :=
  e51.trans (by rw [after_eq e51])

theorem f56 : b56.length = 10 ∧ lOk .rbp .r12 .r14 .r15 [.rbx, .rbp, .r12, .r13] (after b56 (loS .rbx 7168)) = true := by
  rw [after_eq e56]; decide +kernel

theorem x56 : exec b56 (loS .rbx 7168) = some ((after b56 (loS .rbx 7168)), .call NativeRustcVmX64.Vm.EWMul.entryLabel) :=
  e56.trans (by rw [after_eq e56])

theorem f61 : b61.length = 10 ∧ lOk .r12 .rbp .r14 .r15 [.rbx, .r12, .rbp, .r13] (after b61 (loS .rbx 8)) = true := by
  rw [after_eq e61]; decide +kernel

theorem x61 : exec b61 (loS .rbx 8) = some ((after b61 (loS .rbx 8)), .call NativeRustcVmX64.Vm.EWMul.entryLabel) :=
  e61.trans (by rw [after_eq e61])

theorem f66 : b66.length = 10 ∧ lOk .r12 .rbp .r14 .r15 [.rbx, .r12, .rbp, .r13] (after b66 (loS .rbx 1032)) = true := by
  rw [after_eq e66]; decide +kernel

theorem x66 : exec b66 (loS .rbx 1032) = some ((after b66 (loS .rbx 1032)), .call NativeRustcVmX64.Vm.EWMul.entryLabel) :=
  e66.trans (by rw [after_eq e66])

theorem f71 : b71.length = 10 ∧ lOk .r12 .rbp .r14 .r15 [.rbx, .r12, .rbp, .r13] (after b71 (loS .rbx 2048)) = true := by
  rw [after_eq e71]; decide +kernel

theorem x71 : exec b71 (loS .rbx 2048) = some ((after b71 (loS .rbx 2048)), .call NativeRustcVmX64.Vm.EWMul.entryLabel) :=
  e71.trans (by rw [after_eq e71])

theorem f76 : b76.length = 10 ∧ lOk .r12 .rbp .r14 .r15 [.rbx, .r12, .rbp, .r13] (after b76 (loS .rbx 3072)) = true := by
  rw [after_eq e76]; decide +kernel

theorem x76 : exec b76 (loS .rbx 3072) = some ((after b76 (loS .rbx 3072)), .call NativeRustcVmX64.Vm.EWMul.entryLabel) :=
  e76.trans (by rw [after_eq e76])

theorem f81 : b81.length = 10 ∧ lOk .r12 .r13 .r14 .r15 [.rbx, .r12, .r13, .rbp] (after b81 (loS .rbx 8)) = true := by
  rw [after_eq e81]; decide +kernel

theorem x81 : exec b81 (loS .rbx 8) = some ((after b81 (loS .rbx 8)), .call NativeRustcVmX64.Vm.EWMul.entryLabel) :=
  e81.trans (by rw [after_eq e81])

theorem f86 : b86.length = 10 ∧ lOk .r12 .r13 .r14 .r15 [.rbx, .r12, .r13, .rbp] (after b86 (loS .rbx 1032)) = true := by
  rw [after_eq e86]; decide +kernel

theorem x86 : exec b86 (loS .rbx 1032) = some ((after b86 (loS .rbx 1032)), .call NativeRustcVmX64.Vm.EWMul.entryLabel) :=
  e86.trans (by rw [after_eq e86])

theorem f91 : b91.length = 11 ∧ lOk .r14 .r15 .r13 .rbp [.rbx, .r14, .r15] (after b91 (loS .rbx 0)) = true ∧ (after b91 (loS .rbx 0)).reg .r12 = some (.bin .add .W64 (.reg .rbx) (.lit 16)) := by
  rw [after_eq e91]; decide +kernel

theorem x91 : exec b91 (loS .rbx 0) = some ((after b91 (loS .rbx 0)), .call NativeRustcVmX64.Vm.EWMul.entryLabel) :=
  e91.trans (by rw [after_eq e91])

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
