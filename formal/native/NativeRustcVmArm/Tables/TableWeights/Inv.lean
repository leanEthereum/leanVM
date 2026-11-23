module

public import NativeRustcVmArm.Tables.MulCall
public import NativeRustcVmArm.Tables.TableWeights.Exec
public import NativeRustcVmArm.Spec.Tables
public import NativeRustcVm.Tables.Weights

/-!
# `table_weights`'s states

From the entry state `m0` (`out` X0, the heights X1, `equality_point` X2, X3, `point` X4, X5):
the 240-byte frame at `fb m0` (SP inside the function); the words of the frame the loop keeps
(`kslots`: `out`, `|equality_point|`, the point's end, the six heights, the saved registers);
what every state keeps (`Frm`); the weights' places (`lo j`, `hi j`: weight `j`'s limbs in X21/104,
X20/112, X28/120, X19/128, 96/136, 80/88; `WAt`). The states: the loop head with `c` coordinates
done (`It`, weight 5 in X0, X9), `.LTableWeights_3` with coordinate `c`'s factor computed
(`Pre3`), after the `j`th multiplication of coordinate `c` (`Mid`), the exit `.LTableWeights_7`
(`Fin`).
-/

namespace NativeRustcVmArm.Tables.TableWeights

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Tables
open NativeRustcVm (wordOf)

@[expose] public section

variable (m0 : MachineData)

/-- A register's value. -/
abbrev rg (m : MachineData) (r : XReg) : BitVec 64 := (m.regs.getXReg r).toBitVec

/-- The frame's base: SP inside the function. -/
def fb : BitVec 64 := m0.regs.SP.toBitVec - BitVec.ofNat 64 240

/-- The frame's word at `o`. -/
def fw (m : MachineData) (o : Nat) : BitVec 64 :=
  (wordOf m.dmem (fb m0 + BitVec.ofNat 64 o)).toBitVec

/-- Height `j`'s word. -/
def hword (j : Nat) : BitVec 64 :=
  (wordOf m0.dmem (m0.regs.X1.toBitVec + BitVec.ofNat 64 (8 * j))).toBitVec

/-- The heights. -/
def H : Array Nat := heightsOf m0.dmem m0.regs.X1.toBitVec
/-- The equality point. -/
def E : Array EW := slice m0 m0.regs.X2 m0.regs.X3
/-- The point. -/
def P : Array EW := slice m0 m0.regs.X4 m0.regs.X5
/-- The point's length. -/
def n : Nat := m0.regs.X5.toNat

/-- The weights after `c` coordinates. -/
def W (c : Nat) : Array EW := twPrefix (H m0) (E m0) (P m0) c

/-- Coordinate `c`'s challenge. -/
def ch (c : Nat) : EW := (P m0).getD c 0

/-- Coordinate `c`'s factor in a table taller than `c`. -/
def fac (c : Nat) : EW := 1 + (E m0).getD c 0 + ch m0 c

/-- The frame's words the loop keeps, and their values. -/
def kslots : List (Nat × BitVec 64) :=
  [(8, rg m0 .X0), (72, rg m0 .X3), (64, rg m0 .X4 + rg m0 .X5 <<< 4),
    (56, hword m0 0), (48, hword m0 1), (40, hword m0 2), (32, hword m0 3), (24, hword m0 4),
    (16, hword m0 5),
    (144, rg m0 .X29), (152, rg m0 .X30), (160, rg m0 .X28), (168, rg m0 .X27),
    (176, rg m0 .X26), (184, rg m0 .X25), (192, rg m0 .X24), (200, rg m0 .X23),
    (208, rg m0 .X22), (216, rg m0 .X21), (224, rg m0 .X20), (232, rg m0 .X19)]

/-- The kept words' offsets. -/
def koffs : List Nat :=
  [8, 72, 64, 56, 48, 40, 32, 24, 16, 144, 152, 160, 168, 176, 184, 192, 200, 208, 216, 224, 232]

/-- **What every state of the function's body keeps**: SP the frame's base, the kept words,
memory changed only in the frame and `EW::mul`'s stack below it, every mapped byte. -/
structure Frm (m : MachineData) : Prop where
  sp : m.regs.SP.toBitVec = fb m0
  slots : ∀ p ∈ kslots m0, fw m0 m p.1 = p.2
  same : SameOutside m0.dmem m.dmem (StackArea (fb m0) ewMulStack 240)
  kept : Kept m0.dmem m.dmem

/-- The frame's words the exit reads: `out` and the saved registers. -/
def xslots : List (Nat × BitVec 64) :=
  [(8, rg m0 .X0), (144, rg m0 .X29), (152, rg m0 .X30), (160, rg m0 .X28), (168, rg m0 .X27),
    (176, rg m0 .X26), (184, rg m0 .X25), (192, rg m0 .X24), (200, rg m0 .X23),
    (208, rg m0 .X22), (216, rg m0 .X21), (224, rg m0 .X20), (232, rg m0 .X19)]

/-- What the exit needs of the frame: `Frm` with the exit's words only. -/
structure FrmX (m : MachineData) : Prop where
  sp : m.regs.SP.toBitVec = fb m0
  slots : ∀ p ∈ xslots m0, fw m0 m p.1 = p.2
  same : SameOutside m0.dmem m.dmem (StackArea (fb m0) ewMulStack 240)
  kept : Kept m0.dmem m.dmem

/-- A place: a register or a frame word. -/
inductive Pl where
  | reg (r : XReg)
  | slot (o : Nat)
  deriving DecidableEq

/-- A place's value. -/
def Pl.val (m0 m : MachineData) : Pl → BitVec 64
  | .reg r => rg m r
  | .slot o => fw m0 m o

/-- A place's symbolic value in a block's start state. -/
def Pl.sym : Pl → Sym
  | .reg r => .reg r
  | .slot o => .load 0 o 8

/-- A place's symbolic value after a block. -/
def Pl.after (S : SState) : Pl → Option Sym
  | .reg r => S.reg r
  | .slot o => some (loadSym S.mem 0 o 8)

/-- Weight `j`'s low limb's place. -/
def lo : Nat → Pl
  | 0 => .reg .X21
  | 1 => .reg .X20
  | 2 => .reg .X28
  | 3 => .reg .X19
  | 4 => .slot 96
  | _ => .slot 80

/-- Weight `j`'s high limb's place. -/
def hi : Nat → Pl
  | 0 => .slot 104
  | 1 => .slot 112
  | 2 => .slot 120
  | 3 => .slot 128
  | 4 => .slot 136
  | _ => .slot 88

/-- Height `j`'s frame word. -/
def hoff : Nat → Nat
  | 0 => 56
  | 1 => 48
  | 2 => 40
  | 3 => 32
  | 4 => 24
  | _ => 16

variable (m0 : MachineData)

/-- Weight `j` is `w`. -/
def WAt (m : MachineData) (j : Nat) (w : EW) : Prop :=
  (lo j).val m0 m = w.c0.toBitVec ∧ (hi j).val m0 m = w.c1.toBitVec

/-- **The loop head**, `c < n` coordinates done: the coordinate (X22), the equality point's
(X23, past its first word) and the point's (X27) cursors, weights `0` to `4` in place, weight `5`
in X0, X9. -/
structure It (c : Nat) (m : MachineData) : Prop where
  lt : c < n m0
  frm : Frm m0 m
  x22 : rg m .X22 = BitVec.ofNat 64 c
  x23 : rg m .X23 = rg m0 .X2 + BitVec.ofNat 64 (8 + 16 * c)
  x27 : rg m .X27 = rg m0 .X4 + BitVec.ofNat 64 (16 * c)
  w : ∀ j < 5, WAt m0 m j ((W m0 c).getD j 0)
  x0 : rg m .X0 = ((W m0 c).getD 5 0).c0.toBitVec
  x9 : rg m .X9 = ((W m0 c).getD 5 0).c1.toBitVec

/-- **`.LTableWeights_3`**, coordinate `c`'s challenge's high limb (X24) and factor (X25 with the
challenge's low limb, X26) computed, the six weights in place. -/
structure Pre3 (c : Nat) (m : MachineData) : Prop where
  lt : c < n m0
  frm : Frm m0 m
  x22 : rg m .X22 = BitVec.ofNat 64 c
  x23 : rg m .X23 = rg m0 .X2 + BitVec.ofNat 64 (8 + 16 * c)
  x27 : rg m .X27 = rg m0 .X4 + BitVec.ofNat 64 (16 * c)
  x24 : rg m .X24 = (ch m0 c).c1.toBitVec
  x25 : rg m .X25 = ((fac m0 c).c0 ^^^ (ch m0 c).c0).toBitVec
  x26 : rg m .X26 = (fac m0 c).c1.toBitVec
  w : ∀ j < 6, WAt m0 m j ((W m0 c).getD j 0)

/-- **After the `j`th multiplication** of coordinate `c`: the cursors, the challenge (X29, X24),
the factor (X25 with the challenge's low limb, X26), the product in X0, X1, the weights before
`j` updated, after it not. -/
structure Mid (c j : Nat) (m : MachineData) : Prop where
  lt : c < n m0
  frm : Frm m0 m
  x22 : rg m .X22 = BitVec.ofNat 64 c
  x23 : rg m .X23 = rg m0 .X2 + BitVec.ofNat 64 (8 + 16 * c)
  x27 : rg m .X27 = rg m0 .X4 + BitVec.ofNat 64 (16 * (c + 1))
  x29 : rg m .X29 = (ch m0 c).c0.toBitVec
  x24 : rg m .X24 = (ch m0 c).c1.toBitVec
  x25 : rg m .X25 = ((fac m0 c).c0 ^^^ (ch m0 c).c0).toBitVec
  x26 : rg m .X26 = (fac m0 c).c1.toBitVec
  x0 : rg m .X0 = ((W m0 (c + 1)).getD j 0).c0.toBitVec
  x1 : rg m .X1 = ((W m0 (c + 1)).getD j 0).c1.toBitVec
  w : ∀ i < 6, i ≠ j → WAt m0 m i ((W m0 (if i < j then c + 1 else c)).getD i 0)

/-- **The exit** `.LTableWeights_7`: all coordinates done, weights `0` to `4` in place, weight `5`
in X0, X9. -/
structure Fin (m : MachineData) : Prop where
  frm : FrmX m0 m
  w : ∀ j < 5, WAt m0 m j ((W m0 (n m0)).getD j 0)
  x0 : rg m .X0 = ((W m0 (n m0)).getD 5 0).c0.toBitVec
  x9 : rg m .X9 = ((W m0 (n m0)).getD 5 0).c1.toBitVec

end

end NativeRustcVmArm.Tables.TableWeights
