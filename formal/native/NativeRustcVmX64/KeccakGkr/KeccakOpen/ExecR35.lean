module

public import NativeRustcVmX64.KeccakGkr.KeccakOpen.States
public import NativeRustcVmX64.Code.Vm.KeccakOpen
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public meta import NativeRustcVmX64.KeccakGkr.KeccakOpen.States
public meta import NativeRustcVmX64.Code.Vm.KeccakOpen

/-!
# `keccak_open`'s blocks, run by the symbolic executor (x86-64): rounds 3 to 5, the rows' copies
-/

namespace NativeRustcVmX64.KeccakGkr.KeccakOpen

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.KeccakOpen NativeRustcVmX64.Transcript

set_option Elab.async false

sym_block e58 := exec b58 (pS [(.r13, P)])
sym_block e59 := exec b59 (pS (kCopy k58))
sym_block e60 := exec b60 (pS k58)
sym_block e63 := exec b63 (pS k58)
sym_block e64 := exec b64 (pS (kCopy k58))
sym_block e65 := exec b65 (pS k58)
sym_block e68 := exec b68 (pS k58)
sym_block e69 := exec b69 (pS (kCopy k58))
sym_block e70 := exec b70 (pS k58)
sym_block e73 := exec b73 (pS k58)
sym_block e74 := exec b74 (pS (kCopy k58))
sym_block e75 := exec b75 (pS k58)
sym_block e78 := exec b78 (pS [(.r13, P)])
sym_block e79 := exec b79 (pS (kCopy k78))
sym_block e80 := exec b80 (pS k78)
sym_block e83 := exec b83 (pS k78)
sym_block e84 := exec b84 (pS (kCopy k78))
sym_block e85 := exec b85 (pS k78)
sym_block e88 := exec b88 (pS [(.rbp, P)])
sym_block e89 := exec b89 (pS (kCopy k88))
sym_block e90 := exec b90 (pS k88)

public section

theorem f58 : b58.length = 8 ∧ mOk 112 (P) 3 W6 (after b58 (pS [(.r13, P)])) (kCopy k58) W6 = true := by
  rw [after_eq e58]; decide +kernel

theorem x58 : exec b58 (pS [(.r13, P)]) = some ((after b58 (pS [(.r13, P)])), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e58.trans (by rw [after_eq e58])

theorem f59 : b59.length = 4 ∧ mOk 1136 (p2 1024) 3 W6 (after b59 (pS (kCopy k58))) k58 W6 = true := by
  rw [after_eq e59]; decide +kernel

theorem x59 : exec b59 (pS (kCopy k58)) = some ((after b59 (pS (kCopy k58))), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e59.trans (by rw [after_eq e59])

theorem f60 : b60.length = 2 ∧ blkOk 8 3 W6 (after b60 (pS k58)) (kc k58 8) W6 = true := by
  rw [after_eq e60]; decide +kernel

theorem x60 : exec b60 (pS k58) = some ((after b60 (pS k58)), .fall) :=
  e60.trans (by rw [after_eq e60])

theorem f63 : b63.length = 5 ∧ mOk 112 (p2 2048) 3 W6 (after b63 (pS k58)) (kCopy k58) W6 = true := by
  rw [after_eq e63]; decide +kernel

theorem x63 : exec b63 (pS k58) = some ((after b63 (pS k58)), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e63.trans (by rw [after_eq e63])

theorem f64 : b64.length = 4 ∧ mOk 1136 (p2 3072) 3 W6 (after b64 (pS (kCopy k58))) k58 W6 = true := by
  rw [after_eq e64]; decide +kernel

theorem x64 : exec b64 (pS (kCopy k58)) = some ((after b64 (pS (kCopy k58))), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e64.trans (by rw [after_eq e64])

theorem f65 : b65.length = 2 ∧ blkOk 8 3 W6 (after b65 (pS k58)) (kc k58 1032) W6 = true := by
  rw [after_eq e65]; decide +kernel

theorem x65 : exec b65 (pS k58) = some ((after b65 (pS k58)), .fall) :=
  e65.trans (by rw [after_eq e65])

theorem f68 : b68.length = 5 ∧ mOk 112 (p2 4096) 3 W6 (after b68 (pS k58)) (kCopy k58) W6 = true := by
  rw [after_eq e68]; decide +kernel

theorem x68 : exec b68 (pS k58) = some ((after b68 (pS k58)), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e68.trans (by rw [after_eq e68])

theorem f69 : b69.length = 4 ∧ mOk 1136 (p2 5120) 3 W6 (after b69 (pS (kCopy k58))) k58 W6 = true := by
  rw [after_eq e69]; decide +kernel

theorem x69 : exec b69 (pS (kCopy k58)) = some ((after b69 (pS (kCopy k58))), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e69.trans (by rw [after_eq e69])

theorem f70 : b70.length = 2 ∧ blkOk 8 3 W6 (after b70 (pS k58)) (kc k58 2048) W6 = true := by
  rw [after_eq e70]; decide +kernel

theorem x70 : exec b70 (pS k58) = some ((after b70 (pS k58)), .fall) :=
  e70.trans (by rw [after_eq e70])

theorem f73 : b73.length = 5 ∧ mOk 112 (p2 6144) 3 W6 (after b73 (pS k58)) (kCopy k58) W6 = true := by
  rw [after_eq e73]; decide +kernel

theorem x73 : exec b73 (pS k58) = some ((after b73 (pS k58)), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e73.trans (by rw [after_eq e73])

theorem f74 : b74.length = 4 ∧ mOk 1136 (p2 7168) 3 W6 (after b74 (pS (kCopy k58))) k58 W6 = true := by
  rw [after_eq e74]; decide +kernel

theorem x74 : exec b74 (pS (kCopy k58)) = some ((after b74 (pS (kCopy k58))), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e74.trans (by rw [after_eq e74])

theorem f75 : b75.length = 2 ∧ blkOk 8 3 W6 (after b75 (pS k58)) (kc k58 3072) W6 = true := by
  rw [after_eq e75]; decide +kernel

theorem x75 : exec b75 (pS k58) = some ((after b75 (pS k58)), .fall) :=
  e75.trans (by rw [after_eq e75])

theorem f78 : b78.length = 9 ∧ mOk 112 (P) 4 W6 (after b78 (pS [(.r13, P)])) (kCopy k78) W6 = true := by
  rw [after_eq e78]; decide +kernel

theorem x78 : exec b78 (pS [(.r13, P)]) = some ((after b78 (pS [(.r13, P)])), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e78.trans (by rw [after_eq e78])

theorem f79 : b79.length = 4 ∧ mOk 1136 (p2 1024) 4 W6 (after b79 (pS (kCopy k78))) k78 W6 = true := by
  rw [after_eq e79]; decide +kernel

theorem x79 : exec b79 (pS (kCopy k78)) = some ((after b79 (pS (kCopy k78))), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e79.trans (by rw [after_eq e79])

theorem f80 : b80.length = 2 ∧ blkOk 8 4 W6 (after b80 (pS k78)) (kc k78 8) W6 = true := by
  rw [after_eq e80]; decide +kernel

theorem x80 : exec b80 (pS k78) = some ((after b80 (pS k78)), .fall) :=
  e80.trans (by rw [after_eq e80])

theorem f83 : b83.length = 5 ∧ mOk 112 (p2 2048) 4 W6 (after b83 (pS k78)) (kCopy k78) W6 = true := by
  rw [after_eq e83]; decide +kernel

theorem x83 : exec b83 (pS k78) = some ((after b83 (pS k78)), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e83.trans (by rw [after_eq e83])

theorem f84 : b84.length = 4 ∧ mOk 1136 (p2 3072) 4 W6 (after b84 (pS (kCopy k78))) k78 W6 = true := by
  rw [after_eq e84]; decide +kernel

theorem x84 : exec b84 (pS (kCopy k78)) = some ((after b84 (pS (kCopy k78))), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e84.trans (by rw [after_eq e84])

theorem f85 : b85.length = 2 ∧ blkOk 8 4 W6 (after b85 (pS k78)) (kc k78 1032) W6 = true := by
  rw [after_eq e85]; decide +kernel

theorem x85 : exec b85 (pS k78) = some ((after b85 (pS k78)), .fall) :=
  e85.trans (by rw [after_eq e85])

theorem f88 : b88.length = 8 ∧ mOk 112 (P) 5 W6 (after b88 (pS [(.rbp, P)])) (kCopy k88) W6 = true := by
  rw [after_eq e88]; decide +kernel

theorem x88 : exec b88 (pS [(.rbp, P)]) = some ((after b88 (pS [(.rbp, P)])), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e88.trans (by rw [after_eq e88])

theorem f89 : b89.length = 4 ∧ mOk 1136 (p2 1024) 5 W6 (after b89 (pS (kCopy k88))) k88 W6 = true := by
  rw [after_eq e89]; decide +kernel

theorem x89 : exec b89 (pS (kCopy k88)) = some ((after b89 (pS (kCopy k88))), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e89.trans (by rw [after_eq e89])

theorem f90 : b90.length = 2 ∧ blkOk 8 5 W6 (after b90 (pS k88)) (kc k88 0) W6 = true := by
  rw [after_eq e90]; decide +kernel

theorem x90 : exec b90 (pS k88) = some ((after b90 (pS k88)), .fall) :=
  e90.trans (by rw [after_eq e90])

end

end NativeRustcVmX64.KeccakGkr.KeccakOpen
