module

public import Kraken.AArch64.Syntax
meta import Lean.Elab.Deriving.ToExpr

/-!
# Symbolic values

Symbolic 64-bit values `Sym` and booleans `SBool` of the symbolic executor
(`NativeRustcArm.Sym.exec`); their meaning is `NativeRustcArm.Sym.Basic`'s. Their decidable
equality is `NativeRustcArm.Sym.State`'s.
-/

namespace NativeRustcArm

@[expose] public section

/-- A binary operation of a given width on two 64-bit values. -/
inductive BinOp
  | add | sub | and | orr | eor | bic | orn | eon | mul | umulh
  /-- Shifts and rotation by a register, modulo the width. -/
  | lslv | lsrv | asrv | rorv
  /-- `BFM dst src immr imms`: the first operand is the destination's old value. -/
  | bfm (immr imms : Nat)
  /-- `EXTR`: the first operand is the high half. -/
  | extr (lsb : Nat)
  deriving DecidableEq, Repr, Lean.ToExpr

/-- A unary operation of a given width on a 64-bit value. -/
inductive UnOp
  /-- The low bits of the width, zero-extended. -/
  | trunc
  | not | neg | inc | rev
  /-- `RBIT`: the bits of the width reversed. -/
  | rbit
  /-- Shift or rotation by a constant (a shifted register operand). -/
  | shift (k : ShiftType) (n : Nat)
  | ubfm (immr imms : Nat)
  | sbfm (immr imms : Nat)
  /-- An extended register operand of `ADD`/`SUB` (`Xm, <extend> #<amount>`). -/
  | extend (e : Extend)
  /-- An index register of an address (`[Xn, Xm, <extend> #<amount>]`); 64-bit. -/
  | memExtend (e : MemExtend)
  /-- The `n` bytes of the value from byte `t`; 64-bit. -/
  | bytes (t n : Nat)
  deriving DecidableEq, Repr, Lean.ToExpr

/-- A comparison of a given width. -/
inductive CmpOp
  /-- Equal. -/
  | eq
  /-- Unsigned less than. -/
  | ult
  /-- Signed overflow of the difference. -/
  | subV
  /-- Unsigned overflow of the sum. -/
  | addC
  /-- Signed overflow of the sum. -/
  | addV
  deriving DecidableEq, Repr, Lean.ToExpr

mutual

/-- A symbolic 64-bit value. -/
inductive Sym
  /-- The literal `n` (modulo `2 ^ 64`). -/
  | lit (n : Nat)
  /-- The register's value in the environment. -/
  | reg (r : XReg)
  /-- SP's value in the environment. -/
  | sp
  /-- A variable of the environment. -/
  | var (i : Nat)
  /-- The base of region `r` plus `off`. -/
  | ptr (r : Nat) (off : Int)
  /-- A label's address. -/
  | label (l : Label)
  /-- The `n` bytes of the environment's memory at `off` in region `r`, little-endian. -/
  | load (r off n : Nat)
  /-- The `n` bytes of the environment's memory at `off` plus `idx`'s value in region `r`. -/
  | loadx (r off : Nat) (idx : Sym) (n : Nat)
  | bin (op : BinOp) (w : RegWidth) (a b : Sym)
  | un (op : UnOp) (w : RegWidth) (a : Sym)
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
  | cmp (op : CmpOp) (w : RegWidth) (a b : Sym)
  /-- The most significant bit of the width. -/
  | msb (w : RegWidth) (a : Sym)
  /-- Bit `n` of the low bits of the width. -/
  | bit (w : RegWidth) (a : Sym) (n : Nat)
  /-- The environment's flags. -/
  | flagN | flagZ | flagC | flagV
  deriving Repr, Lean.ToExpr

end

end

end NativeRustcArm
