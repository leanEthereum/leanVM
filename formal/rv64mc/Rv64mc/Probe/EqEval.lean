/-
  Rv64mc.Probe.EqEval

  `verifier::multilinear::eq_eval` as a relocatable template: a loop over the two slices, a call of
  `<E as Mul>::mul` per element, and `assert_failed` on a length mismatch. `lsym hp stop [28]` steps it from the
  entry to the loop's head (instruction 14) and out; without `stop` it does not see the loop, since with the
  function index a variable it cannot tell that a path came back.
-/

import Rv64mc.Link.Basic
import Rv64mc.Probe.Abi

namespace Rv64mc.Probe.EqEval

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- Where the template's addresses come from: its callees `<E as Mul>::mul` and `assert_failed`, two sites. -/
structure Link where
  name : String
  base : Word
  mul : Callee
  fail : Callee
  s0 : Site
  s1 : Site

/-- The function, its addresses those of `L`. -/
def tmpl (L : Link) : Lfundef (Op Reg) Reg :=
  { name := L.name, addr := L.base, depth := 0, body :=
    [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn
  (Op.set
    (Reg.x2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0xffffffffffffffd0#64))), LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000028#64))
    (Expr.reg (Reg.x1))), LinstrR.Llabel (LabelKind.internal) 2, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000020#64))
    (Expr.reg (Reg.x8))), LinstrR.Llabel (LabelKind.internal) 3, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000018#64))
    (Expr.reg (Reg.x9))), LinstrR.Llabel (LabelKind.internal) 4, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000010#64))
    (Expr.reg (Reg.x18))), LinstrR.Llabel (LabelKind.internal) 5, LinstrR.Lcond
  (LOperand.cmp "ne" (LOperand.reg (Reg.x11)) (LOperand.reg (Reg.x13)))
  35, LinstrR.Llabel (LabelKind.internal) 6, LinstrR.Lopn
  (Op.set
    (Reg.x14)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 7, LinstrR.Lcond (LOperand.cmp "eq" (LOperand.reg (Reg.x11)) (LOperand.imm 0)) 27, LinstrR.Llabel (LabelKind.internal) 8, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.imm 0x0000000000000000#64) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 9, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 10, LinstrR.Lopn
  (Op.set
    (Reg.x9)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 11, LinstrR.Lopn
  (Op.set
    (Reg.x14)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x14)) (Expr.imm 0x0000000000000004#64))), LinstrR.Llabel (LabelKind.internal) 12, LinstrR.Lopn
  (Op.set
    (Reg.x18)
    (Expr.bin
      (BinOp.add)
      (Expr.reg (Reg.x8))
      (Expr.reg (Reg.x14)))), LinstrR.Llabel (LabelKind.internal) 13, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.imm 0x0000000000000000#64) (Expr.imm 0x0000000000000001#64))), LinstrR.Llabel (LabelKind.internal) 14, LinstrR.Lopn
  (Op.load
    (Reg.x12)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0xfffffffffffffff8#64))), LinstrR.Llabel (LabelKind.internal) 15, LinstrR.Lopn
  (Op.load
    (Reg.x13)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x9)) (Expr.imm 0xfffffffffffffff8#64))), LinstrR.Llabel (LabelKind.internal) 16, LinstrR.Lopn
  (Op.load
    (Reg.x14)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x9)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 17, LinstrR.Lopn
  (Op.load
    (Reg.x15)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 18, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 19, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.xor) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000001#64))), LinstrR.Llabel (LabelKind.internal) 20, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x15))
      (Expr.reg (Reg.x14)))), LinstrR.Llabel (LabelKind.internal) 21, LinstrR.Lopn (Op.set (Reg.x1) (Expr.imm L.s0.hi)), LinstrR.Llabel (LabelKind.internal) 22, LinstrR.Lcall (L.base + 0x5c#64) (Target.indirect (Expr.bin (BinOp.and) (Expr.bin (BinOp.add) (Expr.reg (Reg.x1)) (Expr.imm L.s0.lo)) (Expr.imm 0xfffffffffffffffe#64)) [L.mul.idx]), LinstrR.Llabel (LabelKind.internal) 23, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000010#64))), LinstrR.Llabel (LabelKind.internal) 24, LinstrR.Lopn
  (Op.set
    (Reg.x9)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x9)) (Expr.imm 0x0000000000000010#64))), LinstrR.Llabel (LabelKind.internal) 25, LinstrR.Lcond
  (LOperand.cmp "ne" (LOperand.reg (Reg.x8)) (LOperand.reg (Reg.x18)))
  14, LinstrR.Llabel (LabelKind.internal) 26, LinstrR.Lgoto 29, LinstrR.Llabel (LabelKind.internal) 27, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.imm 0x0000000000000000#64) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 28, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.imm 0x0000000000000000#64) (Expr.imm 0x0000000000000001#64))), LinstrR.Llabel (LabelKind.internal) 29, LinstrR.Lopn
  (Op.load
    (Reg.x1)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000028#64))), LinstrR.Llabel (LabelKind.internal) 30, LinstrR.Lopn
  (Op.load
    (Reg.x8)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000020#64))), LinstrR.Llabel (LabelKind.internal) 31, LinstrR.Lopn
  (Op.load
    (Reg.x9)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000018#64))), LinstrR.Llabel (LabelKind.internal) 32, LinstrR.Lopn
  (Op.load
    (Reg.x18)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000010#64))), LinstrR.Llabel (LabelKind.internal) 33, LinstrR.Lopn
  (Op.set
    (Reg.x2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000030#64))), LinstrR.Llabel (LabelKind.internal) 34, LinstrR.Lret, LinstrR.Llabel (LabelKind.internal) 35, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 36, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 37, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin (BinOp.add) (Expr.imm 0x0000000000000000#64) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 38, LinstrR.Lopn (Op.set (Reg.x1) (Expr.imm L.s1.hi)), LinstrR.Llabel (LabelKind.internal) 39, LinstrR.Lcall (L.base + 0xa0#64) (Target.indirect (Expr.bin (BinOp.and) (Expr.bin (BinOp.add) (Expr.reg (Reg.x1)) (Expr.imm L.s1.lo)) (Expr.imm 0xfffffffffffffffe#64)) [L.fail.idx])]
  }

/-- The facts of `L` the proof uses, as equations for `simp`. -/
structure Link.WF (p : Lprog (Op Reg) Reg) (L : Link) : Prop where
  mul : (p[L.mul.idx]?).map (·.addr) = some L.mul.entry
  fail : (p[L.fail.idx]?).map (·.addr) = some L.fail.entry
  s0 : (L.s0.hi + L.s0.lo) &&& 0xfffffffffffffffe#64 = L.mul.entry
  s1 : (L.s1.hi + L.s1.lo) &&& 0xfffffffffffffffe#64 = L.fail.entry

end Rv64mc.Probe.EqEval
