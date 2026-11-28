module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.States
public import NativeRustcVmX64.Code.Vm.KeccakOpen
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public meta import NativeRustcVmX64.KeccakGkr.KeccakOpen.States
public meta import NativeRustcVmX64.Code.Vm.KeccakOpen

/-!
# `keccak_open`'s blocks, run by the symbolic executor (x86-64): round 2, the rows' copies
-/

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.KeccakOpen NativeRustcVmX64.Transcript

set_option Elab.async false

sym_block e18 := exec b18 (pS [])
sym_block e19 := exec b19 (pS (kCopy k18))
sym_block e20 := exec b20 (pS k18)
sym_block e23 := exec b23 (pS k18)
sym_block e24 := exec b24 (pS (kCopy k18))
sym_block e25 := exec b25 (pS k18)
sym_block e28 := exec b28 (pS k18)
sym_block e29 := exec b29 (pS (kCopy k18))
sym_block e30 := exec b30 (pS k18)
sym_block e33 := exec b33 (pS k18)
sym_block e34 := exec b34 (pS (kCopy k18))
sym_block e35 := exec b35 (pS k18)
sym_block e38 := exec b38 (pS k18)
sym_block e39 := exec b39 (pS (kCopy k18))
sym_block e40 := exec b40 (pS k18)
sym_block e43 := exec b43 (pS k18)
sym_block e44 := exec b44 (pS (kCopy k18))
sym_block e45 := exec b45 (pS k18)
sym_block e48 := exec b48 (pS k18)
sym_block e49 := exec b49 (pS (kCopy k18))
sym_block e50 := exec b50 (pS k18)
sym_block e53 := exec b53 (pS k18)
sym_block e54 := exec b54 (pS (kCopy k18))
sym_block e55 := exec b55 (pS k18)

public section

theorem f18 : b18.length = 9 ∧ mOk 112 (P) 2 [] (after b18 (pS [])) (kCopy k18) [] = true := by
  rw [after_eq e18]; decide +kernel

theorem x18 : exec b18 (pS []) = some ((after b18 (pS [])), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e18.trans (by rw [after_eq e18])

theorem f19 : b19.length = 5 ∧ mOk 1136 (p2 1024) 2 [] (after b19 (pS (kCopy k18))) k18 w19 = true := by
  rw [after_eq e19]; decide +kernel

theorem x19 : exec b19 (pS (kCopy k18)) = some ((after b19 (pS (kCopy k18))), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e19.trans (by rw [after_eq e19])

theorem f20 : b20.length = 2 ∧ blkOk 8 2 w19 (after b20 (pS k18)) (kc k18 8) w19 = true := by
  rw [after_eq e20]; decide +kernel

theorem x20 : exec b20 (pS k18) = some ((after b20 (pS k18)), .fall) :=
  e20.trans (by rw [after_eq e20])

theorem f23 : b23.length = 6 ∧ mOk 112 (p2 2048) 2 w19 (after b23 (pS k18)) (kCopy k18) w23 = true := by
  rw [after_eq e23]; decide +kernel

theorem x23 : exec b23 (pS k18) = some ((after b23 (pS k18)), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e23.trans (by rw [after_eq e23])

theorem f24 : b24.length = 5 ∧ mOk 1136 (p2 3072) 2 w23 (after b24 (pS (kCopy k18))) k18 w24 = true := by
  rw [after_eq e24]; decide +kernel

theorem x24 : exec b24 (pS (kCopy k18)) = some ((after b24 (pS (kCopy k18))), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e24.trans (by rw [after_eq e24])

theorem f25 : b25.length = 2 ∧ blkOk 8 2 w24 (after b25 (pS k18)) (kc k18 1032) w24 = true := by
  rw [after_eq e25]; decide +kernel

theorem x25 : exec b25 (pS k18) = some ((after b25 (pS k18)), .fall) :=
  e25.trans (by rw [after_eq e25])

theorem f28 : b28.length = 6 ∧ mOk 112 (p2 4096) 2 w24 (after b28 (pS k18)) (kCopy k18) w28 = true := by
  rw [after_eq e28]; decide +kernel

theorem x28 : exec b28 (pS k18) = some ((after b28 (pS k18)), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e28.trans (by rw [after_eq e28])

theorem f29 : b29.length = 5 ∧ mOk 1136 (p2 5120) 2 w28 (after b29 (pS (kCopy k18))) k18 w29 = true := by
  rw [after_eq e29]; decide +kernel

theorem x29 : exec b29 (pS (kCopy k18)) = some ((after b29 (pS (kCopy k18))), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e29.trans (by rw [after_eq e29])

theorem f30 : b30.length = 2 ∧ blkOk 8 2 w29 (after b30 (pS k18)) (kc k18 2048) w29 = true := by
  rw [after_eq e30]; decide +kernel

theorem x30 : exec b30 (pS k18) = some ((after b30 (pS k18)), .fall) :=
  e30.trans (by rw [after_eq e30])

theorem f33 : b33.length = 6 ∧ mOk 112 (p2 6144) 2 w29 (after b33 (pS k18)) (kCopy k18) W6 = true := by
  rw [after_eq e33]; decide +kernel

theorem x33 : exec b33 (pS k18) = some ((after b33 (pS k18)), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e33.trans (by rw [after_eq e33])

theorem f34 : b34.length = 4 ∧ mOk 1136 (p2 7168) 2 W6 (after b34 (pS (kCopy k18))) k18 W6 = true := by
  rw [after_eq e34]; decide +kernel

theorem x34 : exec b34 (pS (kCopy k18)) = some ((after b34 (pS (kCopy k18))), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e34.trans (by rw [after_eq e34])

theorem f35 : b35.length = 2 ∧ blkOk 8 2 W6 (after b35 (pS k18)) (kc k18 3072) W6 = true := by
  rw [after_eq e35]; decide +kernel

theorem x35 : exec b35 (pS k18) = some ((after b35 (pS k18)), .fall) :=
  e35.trans (by rw [after_eq e35])

theorem f38 : b38.length = 5 ∧ mOk 112 (p2 8192) 2 W6 (after b38 (pS k18)) (kCopy k18) W6 = true := by
  rw [after_eq e38]; decide +kernel

theorem x38 : exec b38 (pS k18) = some ((after b38 (pS k18)), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e38.trans (by rw [after_eq e38])

theorem f39 : b39.length = 4 ∧ mOk 1136 (p2 9216) 2 W6 (after b39 (pS (kCopy k18))) k18 W6 = true := by
  rw [after_eq e39]; decide +kernel

theorem x39 : exec b39 (pS (kCopy k18)) = some ((after b39 (pS (kCopy k18))), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e39.trans (by rw [after_eq e39])

theorem f40 : b40.length = 2 ∧ blkOk 8 2 W6 (after b40 (pS k18)) (kc k18 4096) W6 = true := by
  rw [after_eq e40]; decide +kernel

theorem x40 : exec b40 (pS k18) = some ((after b40 (pS k18)), .fall) :=
  e40.trans (by rw [after_eq e40])

theorem f43 : b43.length = 5 ∧ mOk 112 (p2 10240) 2 W6 (after b43 (pS k18)) (kCopy k18) W6 = true := by
  rw [after_eq e43]; decide +kernel

theorem x43 : exec b43 (pS k18) = some ((after b43 (pS k18)), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e43.trans (by rw [after_eq e43])

theorem f44 : b44.length = 4 ∧ mOk 1136 (p2 11264) 2 W6 (after b44 (pS (kCopy k18))) k18 W6 = true := by
  rw [after_eq e44]; decide +kernel

theorem x44 : exec b44 (pS (kCopy k18)) = some ((after b44 (pS (kCopy k18))), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e44.trans (by rw [after_eq e44])

theorem f45 : b45.length = 2 ∧ blkOk 8 2 W6 (after b45 (pS k18)) (kc k18 5128) W6 = true := by
  rw [after_eq e45]; decide +kernel

theorem x45 : exec b45 (pS k18) = some ((after b45 (pS k18)), .fall) :=
  e45.trans (by rw [after_eq e45])

theorem f48 : b48.length = 5 ∧ mOk 112 (p2 12288) 2 W6 (after b48 (pS k18)) (kCopy k18) W6 = true := by
  rw [after_eq e48]; decide +kernel

theorem x48 : exec b48 (pS k18) = some ((after b48 (pS k18)), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e48.trans (by rw [after_eq e48])

theorem f49 : b49.length = 4 ∧ mOk 1136 (p2 13312) 2 W6 (after b49 (pS (kCopy k18))) k18 W6 = true := by
  rw [after_eq e49]; decide +kernel

theorem x49 : exec b49 (pS (kCopy k18)) = some ((after b49 (pS (kCopy k18))), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e49.trans (by rw [after_eq e49])

theorem f50 : b50.length = 2 ∧ blkOk 8 2 W6 (after b50 (pS k18)) (kc k18 6152) W6 = true := by
  rw [after_eq e50]; decide +kernel

theorem x50 : exec b50 (pS k18) = some ((after b50 (pS k18)), .fall) :=
  e50.trans (by rw [after_eq e50])

theorem f53 : b53.length = 5 ∧ mOk 112 (p2 14336) 2 W6 (after b53 (pS k18)) (kCopy k18) W6 = true := by
  rw [after_eq e53]; decide +kernel

theorem x53 : exec b53 (pS k18) = some ((after b53 (pS k18)), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e53.trans (by rw [after_eq e53])

theorem f54 : b54.length = 4 ∧ mOk 1136 (p2 15360) 2 W6 (after b54 (pS (kCopy k18))) k18 W6 = true := by
  rw [after_eq e54]; decide +kernel

theorem x54 : exec b54 (pS (kCopy k18)) = some ((after b54 (pS (kCopy k18))), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e54.trans (by rw [after_eq e54])

theorem f55 : b55.length = 2 ∧ blkOk 8 2 W6 (after b55 (pS k18)) (kc k18 7168) W6 = true := by
  rw [after_eq e55]; decide +kernel

theorem x55 : exec b55 (pS k18) = some ((after b55 (pS k18)), .fall) :=
  e55.trans (by rw [after_eq e55])

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
