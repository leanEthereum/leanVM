module

public import NativeRustcVmArm.Whir.MathFrame
public import NativeRustcVmArm.Code.Vm.LanesOf
public meta import NativeRustcVmArm.Code.Vm.LanesOf
public meta import NativeRustcVmArm.Whir.Common

/-!
# `lanes_of`'s blocks, run by the symbolic executor

No frame. The blocks without memory access from the registers (`regsS`); the loops' bodies with
two regions, region 0 the row's words they read and region 1 the lanes they write:
- `revS` (`b9`, four lanes reversed): the row's 32 bytes from X14 − 16, the lanes' 64 from
  X13 − 32;
- `rev1S` (`b12`, one lane reversed): the row's word at X11, the lane at X8;
- `cpS` (`b17`, two lanes copied): the row's 32 bytes from X10 − 16, the lanes' from X9 − 16;
- `cp1S` (`b21`, one lane copied): the row's 16 bytes from X9 − 8, the lane at X10 − 8.
-/

namespace NativeRustcVmArm.Whir.LanesOf

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.LanesOf

@[expose] public section

def regsS : SState := init [] .sp
def revS : SState := init [(32, false), (64, false)] .sp [(.X14, .ptr 0 16), (.X13, .ptr 1 32)]
def rev1S : SState := init [(8, false), (16, false)] .sp [(.X11, .ptr 0 0), (.X8, .ptr 1 0)]
def cpS : SState := init [(32, false), (32, false)] .sp [(.X10, .ptr 0 16), (.X9, .ptr 1 16)]
def cp1S : SState := init [(16, false), (16, false)] .sp [(.X9, .ptr 0 8), (.X10, .ptr 1 8)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 regsS
sym_block run_b1 := exec b1 regsS
sym_block run_b2 := exec b2 regsS
sym_block run_b3 := exec b3 regsS
sym_block run_b4 := exec b4 regsS
sym_block run_b5 := exec b5 regsS
sym_block run_b6 := exec b6 regsS
sym_block run_b7 := exec b7 regsS
sym_block run_b8 := exec b8 regsS
sym_block run_b9 := exec b9 revS
sym_block run_b10 := exec b10 regsS
sym_block run_b11 := exec b11 regsS
sym_block run_b12 := exec b12 rev1S
sym_block run_b13 := exec b13 regsS
sym_block run_b14 := exec b14 regsS
sym_block run_b15 := exec b15 regsS
sym_block run_b16 := exec b16 regsS
sym_block run_b17 := exec b17 cpS
sym_block run_b18 := exec b18 regsS
sym_block run_b19 := exec b19 regsS
sym_block run_b20 := exec b20 regsS
sym_block run_b21 := exec b21 cp1S
sym_block run_b22 := exec b22 regsS

public theorem b0_keeps : keepsRegs regsS (after b0 regsS) (freeRegs []) = true ∧
    (after b0 regsS).mem = [] := by decide +kernel
public theorem b1_keeps : keepsRegs regsS (after b1 regsS) (freeRegs []) = true ∧
    (after b1 regsS).mem = [] := by decide +kernel
public theorem b2_keeps : keepsRegs regsS (after b2 regsS) (freeRegs []) = true ∧
    (after b2 regsS).mem = [] := by decide +kernel
public theorem b3_keeps : keepsRegs regsS (after b3 regsS) (freeRegs []) = true ∧
    (after b3 regsS).mem = [] := by decide +kernel
public theorem b4_keeps : keepsRegs regsS (after b4 regsS) (freeRegs []) = true ∧
    (after b4 regsS).mem = [] := by decide +kernel
public theorem b5_keeps : keepsRegs regsS (after b5 regsS) (freeRegs []) = true ∧
    (after b5 regsS).mem = [] := by decide +kernel
public theorem b6_keeps : keepsRegs regsS (after b6 regsS) (freeRegs []) = true ∧
    (after b6 regsS).mem = [] := by decide +kernel
public theorem b7_keeps : keepsRegs regsS (after b7 regsS) (freeRegs []) = true ∧
    (after b7 regsS).mem = [] := by decide +kernel
public theorem b8_keeps : keepsRegs regsS (after b8 regsS) (freeRegs []) = true ∧
    (after b8 regsS).mem = [] := by decide +kernel
public theorem b10_keeps : keepsRegs regsS (after b10 regsS) (freeRegs []) = true ∧
    (after b10 regsS).mem = [] := by decide +kernel
public theorem b11_keeps : keepsRegs regsS (after b11 regsS) (freeRegs []) = true ∧
    (after b11 regsS).mem = [] := by decide +kernel
public theorem b13_keeps : keepsRegs regsS (after b13 regsS) (freeRegs []) = true ∧
    (after b13 regsS).mem = [] := by decide +kernel
public theorem b14_keeps : keepsRegs regsS (after b14 regsS) (freeRegs []) = true ∧
    (after b14 regsS).mem = [] := by decide +kernel
public theorem b15_keeps : keepsRegs regsS (after b15 regsS) (freeRegs []) = true ∧
    (after b15 regsS).mem = [] := by decide +kernel
public theorem b16_keeps : keepsRegs regsS (after b16 regsS) (freeRegs []) = true ∧
    (after b16 regsS).mem = [] := by decide +kernel
public theorem b18_keeps : keepsRegs regsS (after b18 regsS) (freeRegs []) = true ∧
    (after b18 regsS).mem = [] := by decide +kernel
public theorem b19_keeps : keepsRegs regsS (after b19 regsS) (freeRegs []) = true ∧
    (after b19 regsS).mem = [] := by decide +kernel
public theorem b20_keeps : keepsRegs regsS (after b20 regsS) (freeRegs []) = true ∧
    (after b20 regsS).mem = [] := by decide +kernel
public theorem b22_keeps : keepsRegs regsS (after b22 regsS) (freeRegs []) = true ∧
    (after b22 regsS).mem = [] := by decide +kernel
public theorem b9_keeps : keepsRegs revS (after b9 revS) (freeRegs []) = true ∧
    ∀ w ∈ (after b9 revS).mem, w.r = 1 ∧ w.off + w.n ≤ 64 := by decide +kernel
public theorem b12_keeps : keepsRegs rev1S (after b12 rev1S) (freeRegs []) = true ∧
    ∀ w ∈ (after b12 rev1S).mem, w.r = 1 ∧ w.off + w.n ≤ 16 := by decide +kernel
public theorem b17_keeps : keepsRegs cpS (after b17 cpS) (freeRegs []) = true ∧
    ∀ w ∈ (after b17 cpS).mem, w.r = 1 ∧ w.off + w.n ≤ 32 := by decide +kernel
public theorem b21_keeps : keepsRegs cp1S (after b21 cp1S) (freeRegs []) = true ∧
    ∀ w ∈ (after b21 cp1S).mem, w.r = 1 ∧ w.off + w.n ≤ 16 := by decide +kernel

end NativeRustcVmArm.Whir.LanesOf
