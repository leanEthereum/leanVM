module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.States
public import NativeRustcVmX64.Code.Vm.KeccakOpen
public import NativeRustcVmX64.Code.Vm.KeccakOpen.Names
public meta import NativeRustcVmX64.KeccakGkr.KeccakOpen.States
public meta import NativeRustcVmX64.Code.Vm.KeccakOpen

/-!
# `keccak_open`'s blocks, run by the symbolic executor (x86-64): the inner loops' stores
-/

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.KeccakOpen NativeRustcVmX64.Transcript

set_option Elab.async false

sym_block e9 := exec b9 (stS .r14 .rbx 8)
sym_block e16 := exec b16 (stS .rbx .rbp 8)
sym_block e22 := exec b22 (stS .r13 .rbx 8)
sym_block e27 := exec b27 (stS .r13 .rbx 8)
sym_block e32 := exec b32 (stS .r13 .rbx 0)
sym_block e37 := exec b37 (stS .r13 .rbx 0)
sym_block e42 := exec b42 (stS .r13 .rbx 0)
sym_block e47 := exec b47 (stS .r13 .rbx 8)
sym_block e52 := exec b52 (stS .r13 .rbx 8)
sym_block e57 := exec b57 (stS .r13 .rbx 0)
sym_block e62 := exec b62 (stS .r13 .rbx 8)
sym_block e67 := exec b67 (stS .r13 .rbx 8)
sym_block e72 := exec b72 (stS .r13 .rbx 0)
sym_block e77 := exec b77 (stS .r13 .rbx 0)
sym_block e82 := exec b82 (stS .rbp .rbx 8)
sym_block e87 := exec b87 (stS .rbp .rbx 8)
sym_block e92 := exec b92 (st5S)

public section

theorem f9 : b9.length = 7 ∧ sOk .rbp .r15 .rbx (.bin .add .W64 (.lit 16) (.reg .rbx)) [.r12, .r13, .r14] (after b9 (stS .r14 .rbx 8)) = true := by
  rw [after_eq e9]; decide +kernel

theorem x9 : exec b9 (stS .r14 .rbx 8) = some ((after b9 (stS .r14 .rbx 8)), .cond (notEnd (.bin .add .W64 (.lit 16) (.reg .rbx)) 1032) NativeRustcVmX64.Vm.KeccakOpen.label_42) :=
  e9.trans (by rw [after_eq e9]; rfl)

theorem f16 : b16.length = 7 ∧ sOk .r14 .r15 .rbp (.bin .add .W64 (.lit 16) (.reg .rbp)) [.r12, .r13, .rbx] (after b16 (stS .rbx .rbp 8)) = true := by
  rw [after_eq e16]; decide +kernel

theorem x16 : exec b16 (stS .rbx .rbp 8) = some ((after b16 (stS .rbx .rbp 8)), .cond (notEnd (.bin .add .W64 (.lit 16) (.reg .rbp)) 1032) NativeRustcVmX64.Vm.KeccakOpen.label_6) :=
  e16.trans (by rw [after_eq e16]; rfl)

theorem f22 : b22.length = 7 ∧ sOk .r14 .r15 .rbx (.bin .add .W64 (.lit 16) (.reg .rbx)) [.rbp, .r12, .r13] (after b22 (stS .r13 .rbx 8)) = true := by
  rw [after_eq e22]; decide +kernel

theorem x22 : exec b22 (stS .r13 .rbx 8) = some ((after b22 (stS .r13 .rbx 8)), .cond (notEnd (.bin .add .W64 (.lit 16) (.reg .rbx)) 1032) NativeRustcVmX64.Vm.KeccakOpen.label_9) :=
  e22.trans (by rw [after_eq e22]; rfl)

theorem f27 : b27.length = 7 ∧ sOk .r14 .r15 .rbx (.bin .add .W64 (.lit 16) (.reg .rbx)) [.rbp, .r12, .r13] (after b27 (stS .r13 .rbx 8)) = true := by
  rw [after_eq e27]; decide +kernel

theorem x27 : exec b27 (stS .r13 .rbx 8) = some ((after b27 (stS .r13 .rbx 8)), .cond (notEnd (.bin .add .W64 (.lit 16) (.reg .rbx)) 2056) NativeRustcVmX64.Vm.KeccakOpen.label_11) :=
  e27.trans (by rw [after_eq e27]; rfl)

theorem f32 : b32.length = 7 ∧ sOk .r14 .r15 .rbx (.bin .add .W64 (.lit 16) (.reg .rbx)) [.rbp, .r12, .r13] (after b32 (stS .r13 .rbx 0)) = true := by
  rw [after_eq e32]; decide +kernel

theorem x32 : exec b32 (stS .r13 .rbx 0) = some ((after b32 (stS .r13 .rbx 0)), .cond (notEnd (.bin .add .W64 (.lit 16) (.reg .rbx)) 3072) NativeRustcVmX64.Vm.KeccakOpen.label_13) :=
  e32.trans (by rw [after_eq e32]; rfl)

theorem f37 : b37.length = 7 ∧ sOk .r14 .r15 .rbx (.bin .add .W64 (.lit 16) (.reg .rbx)) [.rbp, .r12, .r13] (after b37 (stS .r13 .rbx 0)) = true := by
  rw [after_eq e37]; decide +kernel

theorem x37 : exec b37 (stS .r13 .rbx 0) = some ((after b37 (stS .r13 .rbx 0)), .cond (notEnd (.bin .add .W64 (.lit 16) (.reg .rbx)) 4096) NativeRustcVmX64.Vm.KeccakOpen.label_15) :=
  e37.trans (by rw [after_eq e37]; rfl)

theorem f42 : b42.length = 7 ∧ sOk .r14 .r15 .rbx (.bin .add .W64 (.lit 16) (.reg .rbx)) [.rbp, .r12, .r13] (after b42 (stS .r13 .rbx 0)) = true := by
  rw [after_eq e42]; decide +kernel

theorem x42 : exec b42 (stS .r13 .rbx 0) = some ((after b42 (stS .r13 .rbx 0)), .cond (notEnd (.bin .add .W64 (.lit 16) (.reg .rbx)) 5120) NativeRustcVmX64.Vm.KeccakOpen.label_17) :=
  e42.trans (by rw [after_eq e42]; rfl)

theorem f47 : b47.length = 7 ∧ sOk .r14 .r15 .rbx (.bin .add .W64 (.lit 16) (.reg .rbx)) [.rbp, .r12, .r13] (after b47 (stS .r13 .rbx 8)) = true := by
  rw [after_eq e47]; decide +kernel

theorem x47 : exec b47 (stS .r13 .rbx 8) = some ((after b47 (stS .r13 .rbx 8)), .cond (notEnd (.bin .add .W64 (.lit 16) (.reg .rbx)) 6152) NativeRustcVmX64.Vm.KeccakOpen.label_19) :=
  e47.trans (by rw [after_eq e47]; rfl)

theorem f52 : b52.length = 7 ∧ sOk .r14 .r15 .rbx (.bin .add .W64 (.lit 16) (.reg .rbx)) [.rbp, .r12, .r13] (after b52 (stS .r13 .rbx 8)) = true := by
  rw [after_eq e52]; decide +kernel

theorem x52 : exec b52 (stS .r13 .rbx 8) = some ((after b52 (stS .r13 .rbx 8)), .cond (notEnd (.bin .add .W64 (.lit 16) (.reg .rbx)) 7176) NativeRustcVmX64.Vm.KeccakOpen.label_21) :=
  e52.trans (by rw [after_eq e52]; rfl)

theorem f57 : b57.length = 7 ∧ sOk .r14 .r15 .rbx (.bin .add .W64 (.lit 16) (.reg .rbx)) [.rbp, .r12, .r13] (after b57 (stS .r13 .rbx 0)) = true := by
  rw [after_eq e57]; decide +kernel

theorem x57 : exec b57 (stS .r13 .rbx 0) = some ((after b57 (stS .r13 .rbx 0)), .cond (notEnd (.bin .add .W64 (.lit 16) (.reg .rbx)) 8192) NativeRustcVmX64.Vm.KeccakOpen.label_23) :=
  e57.trans (by rw [after_eq e57]; rfl)

theorem f62 : b62.length = 7 ∧ sOk .r14 .r15 .rbx (.bin .add .W64 (.lit 16) (.reg .rbx)) [.r12, .rbp, .r13] (after b62 (stS .r13 .rbx 8)) = true := by
  rw [after_eq e62]; decide +kernel

theorem x62 : exec b62 (stS .r13 .rbx 8) = some ((after b62 (stS .r13 .rbx 8)), .cond (notEnd (.bin .add .W64 (.lit 16) (.reg .rbx)) 1032) NativeRustcVmX64.Vm.KeccakOpen.label_25) :=
  e62.trans (by rw [after_eq e62]; rfl)

theorem f67 : b67.length = 7 ∧ sOk .r14 .r15 .rbx (.bin .add .W64 (.lit 16) (.reg .rbx)) [.r12, .rbp, .r13] (after b67 (stS .r13 .rbx 8)) = true := by
  rw [after_eq e67]; decide +kernel

theorem x67 : exec b67 (stS .r13 .rbx 8) = some ((after b67 (stS .r13 .rbx 8)), .cond (notEnd (.bin .add .W64 (.lit 16) (.reg .rbx)) 2056) NativeRustcVmX64.Vm.KeccakOpen.label_27) :=
  e67.trans (by rw [after_eq e67]; rfl)

theorem f72 : b72.length = 7 ∧ sOk .r14 .r15 .rbx (.bin .add .W64 (.lit 16) (.reg .rbx)) [.r12, .rbp, .r13] (after b72 (stS .r13 .rbx 0)) = true := by
  rw [after_eq e72]; decide +kernel

theorem x72 : exec b72 (stS .r13 .rbx 0) = some ((after b72 (stS .r13 .rbx 0)), .cond (notEnd (.bin .add .W64 (.lit 16) (.reg .rbx)) 3072) NativeRustcVmX64.Vm.KeccakOpen.label_29) :=
  e72.trans (by rw [after_eq e72]; rfl)

theorem f77 : b77.length = 7 ∧ sOk .r14 .r15 .rbx (.bin .add .W64 (.lit 16) (.reg .rbx)) [.r12, .rbp, .r13] (after b77 (stS .r13 .rbx 0)) = true := by
  rw [after_eq e77]; decide +kernel

theorem x77 : exec b77 (stS .r13 .rbx 0) = some ((after b77 (stS .r13 .rbx 0)), .cond (notEnd (.bin .add .W64 (.lit 16) (.reg .rbx)) 4096) NativeRustcVmX64.Vm.KeccakOpen.label_31) :=
  e77.trans (by rw [after_eq e77]; rfl)

theorem f82 : b82.length = 7 ∧ sOk .r14 .r15 .rbx (.bin .add .W64 (.lit 16) (.reg .rbx)) [.r12, .r13, .rbp] (after b82 (stS .rbp .rbx 8)) = true := by
  rw [after_eq e82]; decide +kernel

theorem x82 : exec b82 (stS .rbp .rbx 8) = some ((after b82 (stS .rbp .rbx 8)), .cond (notEnd (.bin .add .W64 (.lit 16) (.reg .rbx)) 1032) NativeRustcVmX64.Vm.KeccakOpen.label_33) :=
  e82.trans (by rw [after_eq e82]; rfl)

theorem f87 : b87.length = 7 ∧ sOk .r14 .r15 .rbx (.bin .add .W64 (.lit 16) (.reg .rbx)) [.r12, .r13, .rbp] (after b87 (stS .rbp .rbx 8)) = true := by
  rw [after_eq e87]; decide +kernel

theorem x87 : exec b87 (stS .rbp .rbx 8) = some ((after b87 (stS .rbp .rbx 8)), .cond (notEnd (.bin .add .W64 (.lit 16) (.reg .rbx)) 2056) NativeRustcVmX64.Vm.KeccakOpen.label_35) :=
  e87.trans (by rw [after_eq e87]; rfl)

theorem f92 : b92.length = 8 ∧ sOk .r13 .rbp .rbx (.reg .r12) [.r14, .r15] (after b92 (st5S)) = true := by
  rw [after_eq e92]; decide +kernel

theorem x92 : exec b92 (st5S) = some ((after b92 (st5S)), .cond (notEnd (.reg .r12) 1024) NativeRustcVmX64.Vm.KeccakOpen.label_37) :=
  e92.trans (by rw [after_eq e92]; rfl)

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
