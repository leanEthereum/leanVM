module

public import NativeRustcVmArm.Code.Vm.TableColumnClaims.Names
public import NativeRustcVmArm.Tables.ColumnClaims.Loop

/-!
# `table_column_claims`: each table's loop blocks

`lb0` to `lb5`: each table's head, body and after-call blocks at their places in the code
(`LB`), with what the executor says of them.
-/

namespace NativeRustcVmArm.Tables.ColumnClaims

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TableColumnClaims

set_option Elab.async false

@[expose] public section

variable [Host] {k : Nat}

/-- Table `0`'s loop: `b1`, `b2`, `b3`; `b4` after it, `b5` the next table's. -/
def lb0 (hp : Placed code k) : LB k R04 where
  H := b1
  B := b2
  A := b3
  jH := 20
  jN := 34
  jF := 33
  lN := NativeRustcVmArm.Vm.TableColumnClaims.label_3
  lH := NativeRustcVmArm.Vm.TableColumnClaims.label_1
  cA := .bit .W32 (.reg .X0) 0
  inH := b1_in_code.trans hp.1 (by simp [b1])
  inB := by rw [NativeRustcVmArm.Vm.TableColumnClaims.b1_length, NativeRustcVmArm.Vm.TableColumnClaims.b1Length]; exact b2_in_code.trans hp.1 (by simp [b2])
  inA := by
    rw [NativeRustcVmArm.Vm.TableColumnClaims.b1_length, NativeRustcVmArm.Vm.TableColumnClaims.b1Length, NativeRustcVmArm.Vm.TableColumnClaims.b2_length, NativeRustcVmArm.Vm.TableColumnClaims.b2Length]
    exact b3_in_code.trans hp.1 (by simp [b3])
  fA := by rw [NativeRustcVmArm.Vm.TableColumnClaims.b1_length, NativeRustcVmArm.Vm.TableColumnClaims.b1Length, NativeRustcVmArm.Vm.TableColumnClaims.b2_length, NativeRustcVmArm.Vm.TableColumnClaims.b2Length,
    NativeRustcVmArm.Vm.TableColumnClaims.b3_length, NativeRustcVmArm.Vm.TableColumnClaims.b3Length]
  runH := by rw [Bus.after_eq run_b1]; exact run_b1
  runB := by
    show exec b2 bodyS = some (Bus.after b2 bodyS, _)
    rw [Bus.after_eq run_b2]; exact run_b2
  runA := by rw [Bus.after_eq run_b3]; exact run_b3
  lblN := hp.label (j := NativeRustcVmArm.Vm.TableColumnClaims.b5Offset) NativeRustcVmArm.Vm.TableColumnClaims.label_3_at
  lblH := hp.label (j := NativeRustcVmArm.Vm.TableColumnClaims.b1Offset) NativeRustcVmArm.Vm.TableColumnClaims.label_1_at
  okH := by rw [Bus.after_eq run_b1]; decide
  okB := by rw [show bodyOf R04.a = bodyS from rfl, Bus.after_eq run_b2]; decide
  okA := by rw [Bus.after_eq run_b3]; decide
  kB := by decide
  saved := by decide
  evalA _ := rfl

/-- Table `1`'s loop: `b6`, `b7`, `b8`; `b9` after it, `b10` the next table's. -/
def lb1 (hp : Placed code k) : LB k R04 where
  H := b6
  B := b7
  A := b8
  jH := 48
  jN := 62
  jF := 61
  lN := NativeRustcVmArm.Vm.TableColumnClaims.label_6
  lH := NativeRustcVmArm.Vm.TableColumnClaims.label_4
  cA := .bit .W32 (.reg .X0) 0
  inH := b6_in_code.trans hp.1 (by simp [b6])
  inB := by rw [NativeRustcVmArm.Vm.TableColumnClaims.b6_length, NativeRustcVmArm.Vm.TableColumnClaims.b6Length]; exact b7_in_code.trans hp.1 (by simp [b7])
  inA := by
    rw [NativeRustcVmArm.Vm.TableColumnClaims.b6_length, NativeRustcVmArm.Vm.TableColumnClaims.b6Length, NativeRustcVmArm.Vm.TableColumnClaims.b7_length, NativeRustcVmArm.Vm.TableColumnClaims.b7Length]
    exact b8_in_code.trans hp.1 (by simp [b8])
  fA := by rw [NativeRustcVmArm.Vm.TableColumnClaims.b6_length, NativeRustcVmArm.Vm.TableColumnClaims.b6Length, NativeRustcVmArm.Vm.TableColumnClaims.b7_length, NativeRustcVmArm.Vm.TableColumnClaims.b7Length,
    NativeRustcVmArm.Vm.TableColumnClaims.b8_length, NativeRustcVmArm.Vm.TableColumnClaims.b8Length]
  runH := by rw [Bus.after_eq run_b6]; exact run_b6
  runB := by
    show exec b7 bodyS = some (Bus.after b7 bodyS, _)
    rw [Bus.after_eq run_b7]; exact run_b7
  runA := by rw [Bus.after_eq run_b8]; exact run_b8
  lblN := hp.label (j := NativeRustcVmArm.Vm.TableColumnClaims.b10Offset) NativeRustcVmArm.Vm.TableColumnClaims.label_6_at
  lblH := hp.label (j := NativeRustcVmArm.Vm.TableColumnClaims.b6Offset) NativeRustcVmArm.Vm.TableColumnClaims.label_4_at
  okH := by rw [Bus.after_eq run_b6]; decide
  okB := by rw [show bodyOf R04.a = bodyS from rfl, Bus.after_eq run_b7]; decide
  okA := by rw [Bus.after_eq run_b8]; decide
  kB := by decide
  saved := by decide
  evalA _ := rfl

/-- Table `2`'s loop: `b11`, `b12`, `b13`; `b14` after it, `b15` the next table's. -/
def lb2 (hp : Placed code k) : LB k R04 where
  H := b11
  B := b12
  A := b13
  jH := 77
  jN := 91
  jF := 90
  lN := NativeRustcVmArm.Vm.TableColumnClaims.label_9
  lH := NativeRustcVmArm.Vm.TableColumnClaims.label_7
  cA := .bit .W32 (.reg .X0) 0
  inH := b11_in_code.trans hp.1 (by simp [b11])
  inB := by rw [NativeRustcVmArm.Vm.TableColumnClaims.b11_length, NativeRustcVmArm.Vm.TableColumnClaims.b11Length]; exact b12_in_code.trans hp.1 (by simp [b12])
  inA := by
    rw [NativeRustcVmArm.Vm.TableColumnClaims.b11_length, NativeRustcVmArm.Vm.TableColumnClaims.b11Length, NativeRustcVmArm.Vm.TableColumnClaims.b12_length, NativeRustcVmArm.Vm.TableColumnClaims.b12Length]
    exact b13_in_code.trans hp.1 (by simp [b13])
  fA := by rw [NativeRustcVmArm.Vm.TableColumnClaims.b11_length, NativeRustcVmArm.Vm.TableColumnClaims.b11Length, NativeRustcVmArm.Vm.TableColumnClaims.b12_length, NativeRustcVmArm.Vm.TableColumnClaims.b12Length,
    NativeRustcVmArm.Vm.TableColumnClaims.b13_length, NativeRustcVmArm.Vm.TableColumnClaims.b13Length]
  runH := by rw [Bus.after_eq run_b11]; exact run_b11
  runB := by
    show exec b12 bodyS = some (Bus.after b12 bodyS, _)
    rw [Bus.after_eq run_b12]; exact run_b12
  runA := by rw [Bus.after_eq run_b13]; exact run_b13
  lblN := hp.label (j := NativeRustcVmArm.Vm.TableColumnClaims.b15Offset) NativeRustcVmArm.Vm.TableColumnClaims.label_9_at
  lblH := hp.label (j := NativeRustcVmArm.Vm.TableColumnClaims.b11Offset) NativeRustcVmArm.Vm.TableColumnClaims.label_7_at
  okH := by rw [Bus.after_eq run_b11]; decide
  okB := by rw [show bodyOf R04.a = bodyS from rfl, Bus.after_eq run_b12]; decide
  okA := by rw [Bus.after_eq run_b13]; decide
  kB := by decide
  saved := by decide
  evalA _ := rfl

/-- Table `3`'s loop: `b16`, `b17`, `b18`; `b19` after it, `b20` the next table's. -/
def lb3 (hp : Placed code k) : LB k R04 where
  H := b16
  B := b17
  A := b18
  jH := 107
  jN := 121
  jF := 120
  lN := NativeRustcVmArm.Vm.TableColumnClaims.label_12
  lH := NativeRustcVmArm.Vm.TableColumnClaims.label_10
  cA := .bit .W32 (.reg .X0) 0
  inH := b16_in_code.trans hp.1 (by simp [b16])
  inB := by rw [NativeRustcVmArm.Vm.TableColumnClaims.b16_length, NativeRustcVmArm.Vm.TableColumnClaims.b16Length]; exact b17_in_code.trans hp.1 (by simp [b17])
  inA := by
    rw [NativeRustcVmArm.Vm.TableColumnClaims.b16_length, NativeRustcVmArm.Vm.TableColumnClaims.b16Length, NativeRustcVmArm.Vm.TableColumnClaims.b17_length, NativeRustcVmArm.Vm.TableColumnClaims.b17Length]
    exact b18_in_code.trans hp.1 (by simp [b18])
  fA := by rw [NativeRustcVmArm.Vm.TableColumnClaims.b16_length, NativeRustcVmArm.Vm.TableColumnClaims.b16Length, NativeRustcVmArm.Vm.TableColumnClaims.b17_length, NativeRustcVmArm.Vm.TableColumnClaims.b17Length,
    NativeRustcVmArm.Vm.TableColumnClaims.b18_length, NativeRustcVmArm.Vm.TableColumnClaims.b18Length]
  runH := by rw [Bus.after_eq run_b16]; exact run_b16
  runB := by
    show exec b17 bodyS = some (Bus.after b17 bodyS, _)
    rw [Bus.after_eq run_b17]; exact run_b17
  runA := by rw [Bus.after_eq run_b18]; exact run_b18
  lblN := hp.label (j := NativeRustcVmArm.Vm.TableColumnClaims.b20Offset) NativeRustcVmArm.Vm.TableColumnClaims.label_12_at
  lblH := hp.label (j := NativeRustcVmArm.Vm.TableColumnClaims.b16Offset) NativeRustcVmArm.Vm.TableColumnClaims.label_10_at
  okH := by rw [Bus.after_eq run_b16]; decide
  okB := by rw [show bodyOf R04.a = bodyS from rfl, Bus.after_eq run_b17]; decide
  okA := by rw [Bus.after_eq run_b18]; decide
  kB := by decide
  saved := by decide
  evalA _ := rfl

/-- Table `4`'s loop: `b21`, `b22`, `b23`; `b24` after it (the failure), `b26` the next
table's. -/
def lb4 (hp : Placed code k) : LB k R04 where
  H := b21
  B := b22
  A := b23
  jH := 137
  jN := 158
  jF := 150
  lN := NativeRustcVmArm.Vm.TableColumnClaims.label_17
  lH := NativeRustcVmArm.Vm.TableColumnClaims.label_13
  cA := .bit .W32 (.reg .X0) 0
  inH := b21_in_code.trans hp.1 (by simp [b21])
  inB := by rw [NativeRustcVmArm.Vm.TableColumnClaims.b21_length, NativeRustcVmArm.Vm.TableColumnClaims.b21Length]; exact b22_in_code.trans hp.1 (by simp [b22])
  inA := by
    rw [NativeRustcVmArm.Vm.TableColumnClaims.b21_length, NativeRustcVmArm.Vm.TableColumnClaims.b21Length, NativeRustcVmArm.Vm.TableColumnClaims.b22_length, NativeRustcVmArm.Vm.TableColumnClaims.b22Length]
    exact b23_in_code.trans hp.1 (by simp [b23])
  fA := by rw [NativeRustcVmArm.Vm.TableColumnClaims.b21_length, NativeRustcVmArm.Vm.TableColumnClaims.b21Length, NativeRustcVmArm.Vm.TableColumnClaims.b22_length, NativeRustcVmArm.Vm.TableColumnClaims.b22Length,
    NativeRustcVmArm.Vm.TableColumnClaims.b23_length, NativeRustcVmArm.Vm.TableColumnClaims.b23Length]
  runH := by rw [Bus.after_eq run_b21]; exact run_b21
  runB := by
    show exec b22 bodyS = some (Bus.after b22 bodyS, _)
    rw [Bus.after_eq run_b22]; exact run_b22
  runA := by rw [Bus.after_eq run_b23]; exact run_b23
  lblN := hp.label (j := NativeRustcVmArm.Vm.TableColumnClaims.b26Offset) NativeRustcVmArm.Vm.TableColumnClaims.label_17_at
  lblH := hp.label (j := NativeRustcVmArm.Vm.TableColumnClaims.b21Offset) NativeRustcVmArm.Vm.TableColumnClaims.label_13_at
  okH := by rw [Bus.after_eq run_b21]; decide
  okB := by rw [show bodyOf R04.a = bodyS from rfl, Bus.after_eq run_b22]; decide
  okA := by rw [Bus.after_eq run_b23]; decide
  kB := by decide
  saved := by decide
  evalA _ := rfl

/-- Table `5`'s loop: `b27`, `b28`, `b29` (X0 zeroed); `b30` after it, `b31` the success. -/
def lb5 (hp : Placed code k) : LB k R5 where
  H := b27
  B := b28
  A := b29
  jH := 174
  jN := 190
  jF := 189
  lN := NativeRustcVmArm.Vm.TableColumnClaims.label_20
  lH := NativeRustcVmArm.Vm.TableColumnClaims.label_18
  cA := .bit .W32 (.un .trunc .W32 (.reg .X0)) 0
  inH := b27_in_code.trans hp.1 (by simp [b27])
  inB := by rw [NativeRustcVmArm.Vm.TableColumnClaims.b27_length, NativeRustcVmArm.Vm.TableColumnClaims.b27Length]; exact b28_in_code.trans hp.1 (by simp [b28])
  inA := by
    rw [NativeRustcVmArm.Vm.TableColumnClaims.b27_length, NativeRustcVmArm.Vm.TableColumnClaims.b27Length, NativeRustcVmArm.Vm.TableColumnClaims.b28_length, NativeRustcVmArm.Vm.TableColumnClaims.b28Length]
    exact b29_in_code.trans hp.1 (by simp [b29])
  fA := by rw [NativeRustcVmArm.Vm.TableColumnClaims.b27_length, NativeRustcVmArm.Vm.TableColumnClaims.b27Length, NativeRustcVmArm.Vm.TableColumnClaims.b28_length, NativeRustcVmArm.Vm.TableColumnClaims.b28Length,
    NativeRustcVmArm.Vm.TableColumnClaims.b29_length, NativeRustcVmArm.Vm.TableColumnClaims.b29Length]
  runH := by rw [Bus.after_eq run_b27]; exact run_b27
  runB := by
    show exec b28 bodyS5 = some (Bus.after b28 bodyS5, _)
    rw [Bus.after_eq run_b28]; exact run_b28
  runA := by rw [Bus.after_eq run_b29]; exact run_b29
  lblN := hp.label (j := NativeRustcVmArm.Vm.TableColumnClaims.b31Offset) NativeRustcVmArm.Vm.TableColumnClaims.label_20_at
  lblH := hp.label (j := NativeRustcVmArm.Vm.TableColumnClaims.b27Offset) NativeRustcVmArm.Vm.TableColumnClaims.label_18_at
  okH := by rw [Bus.after_eq run_b27]; decide
  okB := by rw [show bodyOf R5.a = bodyS5 from rfl, Bus.after_eq run_b28]; decide
  okA := by rw [Bus.after_eq run_b29]; decide
  kB := by decide
  saved := by decide
  evalA env := by
    show (low .W32 (UnOp.apply .trunc .W32 (env.regs .X0))).getLsbD 0 = _
    rw [UnOp.apply, low_ext]

end

end NativeRustcVmArm.Tables.ColumnClaims
