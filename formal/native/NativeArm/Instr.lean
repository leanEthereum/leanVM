module

public import NativeArm.Basic

/-!
# QM instructions and conditions as AArch64 instructions

`QInstr.toArm` and `Cond.toArm` give each QM instruction and each condition's flag-setting code as
a list of Kraken AArch64 instructions; `Cond.armCC` is the condition code that holds after
`Cond.toArm` exactly when the condition does (`NativeArm.Bridge`). An immediate other than a small
addend or comparand goes into a scratch register by `MOVZ` (or `MOVN`) and `MOVK`s first: X4 for
an operand, X5 for an address's displacement, X6 for a stored immediate. An address with an index
is computed into X4 first; a displacement `LDR`/`STR` cannot encode is added from X5.
-/

open Native

namespace NativeArm

@[expose] public section

/-- The register `r` shifted by `n`, as the second operand of a data-processing instruction. -/
def sr (r : XReg) (shift : ShiftType := .LSL) (n : Int64 := 0) : ShiftRegExpr .W64 :=
  { reg := xr r, amount := n, shift := shift }

/-- The 16 bits of `k` from bit `16 * j`. -/
def chunk (k : UInt64) (j : Nat) : Nat := k.toNat / 2 ^ (16 * j) % 2 ^ 16

/-- `MOVK t, #c, LSL #s`. -/
def movk (t : XReg) (c : Nat) (s : MovShift .W64) : Instr :=
  ⟨.W64, .MOVK (xr t) (.int64 (Int64.ofNat c)) s⟩

/-- `MOVK t, #c, LSL #s` setting chunk `j` of `k`, unless that chunk is `fill`. -/
def movkIf (t : XReg) (k : UInt64) (fill j : Nat) (s : MovShift .W64) : List Instr :=
  if chunk k j = fill then [] else [movk t (chunk k j) s]

/-- The `MOVK`s that set the chunks 1 to 3 of `k` that differ from `fill`. -/
def movks (t : XReg) (k : UInt64) (fill : Nat) : List Instr :=
  movkIf t k fill 1 .LSL16 ++ movkIf t k fill 2 .LSL32 ++ movkIf t k fill 3 .LSL48

/-- `t := k`: `MOVZ` the low chunk, or `MOVN` its complement when more upper chunks of `k` are all
ones than zero, then a `MOVK` for each upper chunk that differs. -/
def movImm (t : XReg) (k : UInt64) : List Instr :=
  let ones := ([1, 2, 3].filter fun j => chunk k j = 0xFFFF).length
  let zeros := ([1, 2, 3].filter fun j => chunk k j = 0).length
  if zeros < ones then
    ⟨.W64, .MOVN (xr t) (.int64 (Int64.ofNat (chunk (~~~k) 0))) .LSL0⟩ :: movks t k 0xFFFF
  else ⟨.W64, .MOVZ (xr t) (.int64 (Int64.ofNat (chunk k 0))) .LSL0⟩ :: movks t k 0

/-- Whether an `ADD`/`SUB`/`SUBS` immediate encodes `k`. -/
def imm12 (k : Int64) : Bool := 0 ≤ k.toInt && k.toInt < 4096

/-- `d := b + k`. -/
def addImm (d b : XReg) (k : Int64) : List Instr :=
  if imm12 k then [⟨.W64, .ADD_e (xs d) (xs b) (.imm { imm := .int64 k, shift := .S0 })⟩]
  else if imm12 (-k) then [⟨.W64, .SUB_e (xs d) (xs b) (.imm { imm := .int64 (-k), shift := .S0 })⟩]
  else movImm .X5 k.toUInt64 ++ [⟨.W64, .ADD_s (xr d) (xr b) (sr .X5)⟩]

/-- The shift of an index register's scale. -/
def _root_.Native.Width.lsl : Width → Int64 | .W8 => 0 | .W16 => 1 | .W32 => 2 | .W64 => 3

/-- An address's base: the base register, or X4 holding `base + index · scale`. -/
def _root_.Native.Addr.armBase (a : Addr) : List Instr × XReg :=
  match a.idx with
  | none => ([], a.base.toX)
  | some (r, w) => ([⟨.W64, .ADD_s (xr .X4) (xr a.base.toX) (sr r.toX .LSL w.lsl)⟩], .X4)

/-- Whether `LDR`/`STR` encode a displacement: a signed 9-bit one (the assembler's `LDUR`/`STUR`)
or a multiple of 8 below 32768. -/
def dispFits (k : Int64) : Bool :=
  (-256 ≤ k.toInt && k.toInt ≤ 255) || (0 ≤ k.toInt && k.toInt ≤ 32760 && k.toInt % 8 == 0)

/-- The operand `[b, #k]`. -/
abbrev immOp (b : XReg) (k : Int64) : AddrExpr :=
  { base := xs b, off := .imm { imm := .int64 k, index := none } }

/-- The operand `[b, c]`. -/
abbrev regOp (b c : XReg) : AddrExpr :=
  { base := xs b, off := .reg { reg := ⟨.W64, xr c⟩, ext := ⟨.UXTX, .E0⟩ } }

/-- An address's code and its `LDR`/`STR` operand. -/
def _root_.Native.Addr.toArm (a : Addr) : List Instr × AddrExpr :=
  if dispFits a.disp then (a.armBase.1, immOp a.armBase.2 a.disp)
  else (a.armBase.1 ++ movImm .X5 a.disp.toUInt64, regOp a.armBase.2 .X5)

/-- `d := a op e` for a shifted-register data-processing instruction. -/
abbrev dp (op : RegOrZr .W64 → RegOrZr .W64 → ShiftRegExpr .W64 → Operation .W64)
    (d : XReg) (a : RegOrZr .W64) (e : ShiftRegExpr .W64) : Instr :=
  ⟨.W64, op (xr d) a e⟩

/-- The zero register. -/
abbrev xzr : RegOrZr .W64 := .low .XZR .W64

/-- The AArch64 instructions of a QM instruction. -/
def _root_.Native.QInstr.toArm : QInstr → List Instr
  | .mov d s => [dp .ORR_s d.toX xzr (sr s.toX)]
  | .movi d k => movImm d.toX k.toUInt64
  | .load d a => a.toArm.1 ++ [⟨.W64, .LDR (xr d.toX) (.addr a.toArm.2)⟩]
  | .store a s => a.toArm.1 ++ [⟨.W64, .STR (xr s.toX) a.toArm.2⟩]
  | .storei a k =>
    if k = 0 then a.toArm.1 ++ [⟨.W64, .STR xzr a.toArm.2⟩]
    else movImm .X6 k.toUInt64 ++ a.toArm.1 ++ [⟨.W64, .STR (xr .X6) a.toArm.2⟩]
  | .lea d a => a.armBase.1 ++ addImm d.toX a.armBase.2 a.disp
  | .add d s => [dp .ADD_s d.toX (xr d.toX) (sr s.toX)]
  | .addi d k => addImm d.toX d.toX k
  | .sub d s => [dp .SUB_s d.toX (xr d.toX) (sr s.toX)]
  | .subi d k => addImm d.toX d.toX (-k)
  | .xor d s => [dp .EOR_s d.toX (xr d.toX) (sr s.toX)]
  | .xori d k => movImm .X4 k.toUInt64 ++ [dp .EOR_s d.toX (xr d.toX) (sr .X4)]
  | .and d s => [dp .AND_s d.toX (xr d.toX) (sr s.toX)]
  | .andi d k => movImm .X4 k.toUInt64 ++ [dp .AND_s d.toX (xr d.toX) (sr .X4)]
  | .or d s => [dp .ORR_s d.toX (xr d.toX) (sr s.toX)]
  | .not d => [dp .ORN_s d.toX xzr (sr d.toX)]
  | .neg d => [dp .SUB_s d.toX xzr (sr d.toX)]
  | .shli d n => [dp .ORR_s d.toX xzr (sr d.toX .LSL (Int64.ofNat (n % 64)))]
  | .shri d n => [dp .ORR_s d.toX xzr (sr d.toX .LSR (Int64.ofNat (n % 64)))]
  | .sari d n => [dp .ORR_s d.toX xzr (sr d.toX .ASR (Int64.ofNat (n % 64)))]
  | .roli d n => [dp .ORR_s d.toX xzr (sr d.toX .ROR (Int64.ofNat ((64 - n % 64) % 64)))]
  | .shlcl d => [⟨.W64, .LSLV (xr d.toX) (xr d.toX) (xr Reg64.rcx.toX)⟩]

/-- The flag-setting instructions of a condition. -/
def _root_.Native.Cond.toArm : Cond → List Instr
  | .cmp _ a (.reg b) => [⟨.W64, .SUBS_s xzr (xr a.toX) (sr b.toX)⟩]
  | .cmp _ a (.imm k) =>
    if imm12 k then [⟨.W64, .SUBS_e xzr (xs a.toX) (.imm { imm := .int64 k, shift := .S0 })⟩]
    else movImm .X4 k.toUInt64 ++ [⟨.W64, .SUBS_s xzr (xr a.toX) (sr .X4)⟩]
  | .test _ a (.reg b) => [⟨.W64, .ANDS_s xzr (xr a.toX) (sr b.toX)⟩]
  | .test _ a (.imm k) => movImm .X4 k.toUInt64 ++ [⟨.W64, .ANDS_s xzr (xr a.toX) (sr .X4)⟩]

/-- The condition code that holds, after `Cond.toArm`, exactly when the condition does. -/
def _root_.Native.Cond.armCC : Cond → CondCode
  | .cmp .eq _ _ => .EQ
  | .cmp .ne _ _ => .NE
  | .cmp .ltu _ _ => .CC
  | .cmp .geu _ _ => .CS
  | .test true _ _ => .EQ
  | .test false _ _ => .NE

end

end NativeArm
