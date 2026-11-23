module

public import Kraken.X64.Syntax
meta import Lean.Elab.Deriving.ToExpr

/-!
# Symbolic values

Symbolic 64-bit values `Sym` and booleans `SBool` of the symbolic executor
(`NativeRustcX64.Sym.exec`); their meaning is `NativeRustcX64.Sym.Basic`'s. Their decidable
equality is `NativeRustcX64.Sym.State`'s. An operation of width `w` computes on the low `w` bits of
its operands and zero-extends its result, the way Kraken's instructions of width `w` compute;
each operation's value is Kraken's expression for it.
-/

namespace NativeRustcX64

@[expose] public section

/-- A binary operation of a given width on two 64-bit values. -/
inductive BinOp
  | add | sub | and | or | xor | mul
  /-- The high half of the unsigned product (`MUL`'s RDX). -/
  | mulhi
  /-- Set the bit indexed modulo the operand width (`BTS`). -/
  | bts
  /-- Shifts and rotations; the count is the second operand's low byte, masked to 5 bits (6 bits
  at width 64). -/
  | shl | shr | sar | rol | ror
  /-- The first operand with its low bits of the width replaced by the second's (a write to an
  8- or 16-bit register); 64-bit. -/
  | merge
  deriving DecidableEq, Repr, Lean.ToExpr

/-- A double-precision shift (`SHLD`, `SHRD`): destination, source, count. -/
inductive TernOp
  | shld | shrd
  deriving DecidableEq, Repr, Lean.ToExpr

/-- A unary operation of a given width on a 64-bit value. -/
inductive UnOp
  /-- The low bits of the width, zero-extended. -/
  | trunc
  | not | neg | bswap
  /-- The low bits of width `w'` zero- or sign-extended to the width (`MOVZX`, `MOVSX`). -/
  | zext (w' : Width)
  | sext (w' : Width)
  /-- The `n` bytes of the value from byte `t`; 64-bit. -/
  | bytes (t n : Nat)
  deriving DecidableEq, Repr, Lean.ToExpr

/-- A comparison of a given width. -/
inductive CmpOp
  /-- Equal. -/
  | eq
  /-- Unsigned less than (the carry of a subtraction). -/
  | ult
  /-- Unsigned overflow of the sum (the carry of an addition). -/
  | addC
  /-- Signed overflow of the sum, of the difference. -/
  | addV | subV
  /-- Signed overflow of `INC`, `DEC`, `NEG` of the first operand. -/
  | incV | decV | negV
  /-- The unsigned product overflows the width (`MUL`'s CF and OF). -/
  | mulC
  /-- The bit indexed modulo the operand width (`BT`, `BTS`). -/
  | bit
  /-- The carry and signed overflow of the sum with a carry in `c` (`ADC`). -/
  | adcC (c : Bool) | adcV (c : Bool)
  /-- The borrow and signed overflow of the difference with a borrow in `c` (`SBB`). -/
  | sbbC (c : Bool) | sbbV (c : Bool)
  deriving DecidableEq, Repr, Lean.ToExpr

mutual

/-- A symbolic 64-bit value. -/
inductive Sym
  /-- The literal `n` (modulo `2 ^ 64`). -/
  | lit (n : Nat)
  /-- The register's value in the environment. -/
  | reg (r : Reg64)
  /-- A variable of the environment. -/
  | var (i : Nat)
  /-- The base of region `r` plus `off`. -/
  | ptr (r : Nat) (off : Int)
  /-- A label's address. -/
  | label (l : Label)
  /-- The address of a label's GOT slot, not the contents of that slot. -/
  | gotSlot (l : Label)
  /-- The `n` bytes of the environment's memory at `off` in region `r`, little-endian. -/
  | load (r off n : Nat)
  /-- The `n` bytes of the environment's memory at `off` plus the value of `idx` in region `r`
  (an indexed load). -/
  | loadx (r off : Nat) (idx : Sym) (n : Nat)
  /-- The environment's return address: the address after a block that ends in a `call`. -/
  | retAddr
  | bin (op : BinOp) (w : Width) (a b : Sym)
  | un (op : UnOp) (w : Width) (a : Sym)
  | tern (op : TernOp) (w : Width) (a b c : Sym)
  | ite (c : SBool) (a b : Sym)
  deriving Repr, Lean.ToExpr

/-- A symbolic boolean. -/
inductive SBool
  | lit (b : Bool)
  | not (b : SBool)
  | and (b c : SBool)
  | or (b c : SBool)
  | beq (b c : SBool)
  | ite (c a b : SBool)
  | cmp (op : CmpOp) (w : Width) (a b : Sym)
  /-- The most significant bit of the width. -/
  | msb (w : Width) (a : Sym)
  /-- The environment's flags. -/
  | flagCF | flagZF | flagSF | flagOF
  deriving Repr, Lean.ToExpr

end

end

end NativeRustcX64
