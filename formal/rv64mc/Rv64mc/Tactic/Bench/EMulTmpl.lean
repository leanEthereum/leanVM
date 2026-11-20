/-
  Rv64mc.Tactic.Bench.EMulTmpl

  `<E as Mul>::mul` (Karatsuba over `clmul` and `reduce`) as a relocatable template, and its contract over any
  program that holds the template at some index, with its callees' contracts as hypotheses. A probe of phase 0:
  the template is the lift of the image's function with every address a field of `Link`.
-/

import Rv64mc.Tactic.Bench.Link

namespace Rv64mc.Tactic.Bench.EMul

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- Where the template's addresses come from: its name and entry, its callees, its five call sites. -/
structure Link where
  name : String
  base : Word
  clmul : Callee
  reduce : Callee
  s0 : Site
  s1 : Site
  s2 : Site
  s3 : Site
  s4 : Site

/-- The function, its addresses those of `L`. -/
def tmpl (L : Link) : Lfundef (Op Reg) Reg :=
  { name := L.name, addr := L.base, depth := 0, body :=
    [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lopn
  (Op.set
    (Reg.x2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0xffffffffffffffb0#64))), LinstrR.Llabel (LabelKind.internal) 1, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000048#64))
    (Expr.reg (Reg.x1))), LinstrR.Llabel (LabelKind.internal) 2, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000040#64))
    (Expr.reg (Reg.x8))), LinstrR.Llabel (LabelKind.internal) 3, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000038#64))
    (Expr.reg (Reg.x9))), LinstrR.Llabel (LabelKind.internal) 4, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000030#64))
    (Expr.reg (Reg.x18))), LinstrR.Llabel (LabelKind.internal) 5, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000028#64))
    (Expr.reg (Reg.x19))), LinstrR.Llabel (LabelKind.internal) 6, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000020#64))
    (Expr.reg (Reg.x20))), LinstrR.Llabel (LabelKind.internal) 7, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000018#64))
    (Expr.reg (Reg.x21))), LinstrR.Llabel (LabelKind.internal) 8, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000010#64))
    (Expr.reg (Reg.x22))), LinstrR.Llabel (LabelKind.internal) 9, LinstrR.Lopn
  (Op.store
    (Width.b8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000008#64))
    (Expr.reg (Reg.x23))), LinstrR.Llabel (LabelKind.internal) 10, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x13)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 11, LinstrR.Lopn
  (Op.set
    (Reg.x9)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 12, LinstrR.Lopn
  (Op.set
    (Reg.x18)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 13, LinstrR.Lopn
  (Op.set
    (Reg.x19)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 14, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x12)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 15, LinstrR.Lopn (Op.set (Reg.x1) (Expr.imm L.s0.hi)), LinstrR.Llabel (LabelKind.internal) 16, LinstrR.Lcall (L.base + 0x44#64) (Target.indirect (Expr.bin (BinOp.and) (Expr.bin (BinOp.add) (Expr.reg (Reg.x1)) (Expr.imm L.s0.lo)) (Expr.imm 0xfffffffffffffffe#64)) [L.clmul.idx]), LinstrR.Llabel (LabelKind.internal) 17, LinstrR.Lopn
  (Op.set
    (Reg.x20)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 18, LinstrR.Lopn
  (Op.set
    (Reg.x21)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 19, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x18)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 20, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x8)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 21, LinstrR.Lopn (Op.set (Reg.x1) (Expr.imm L.s1.hi)), LinstrR.Llabel (LabelKind.internal) 22, LinstrR.Lcall (L.base + 0x5c#64) (Target.indirect (Expr.bin (BinOp.and) (Expr.bin (BinOp.add) (Expr.reg (Reg.x1)) (Expr.imm L.s1.lo)) (Expr.imm 0xfffffffffffffffe#64)) [L.clmul.idx]), LinstrR.Llabel (LabelKind.internal) 23, LinstrR.Lopn
  (Op.set
    (Reg.x22)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 24, LinstrR.Lopn
  (Op.set
    (Reg.x23)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 25, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x18))
      (Expr.reg (Reg.x19)))), LinstrR.Llabel (LabelKind.internal) 26, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x8))
      (Expr.reg (Reg.x9)))), LinstrR.Llabel (LabelKind.internal) 27, LinstrR.Lopn (Op.set (Reg.x1) (Expr.imm L.s2.hi)), LinstrR.Llabel (LabelKind.internal) 28, LinstrR.Lcall (L.base + 0x74#64) (Target.indirect (Expr.bin (BinOp.and) (Expr.bin (BinOp.add) (Expr.reg (Reg.x1)) (Expr.imm L.s2.lo)) (Expr.imm 0xfffffffffffffffe#64)) [L.clmul.idx]), LinstrR.Llabel (LabelKind.internal) 29, LinstrR.Lopn
  (Op.set
    (Reg.x8)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 30, LinstrR.Lopn
  (Op.set
    (Reg.x9)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x11)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 31, LinstrR.Lopn
  (Op.set
    (Reg.x18)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x22))
      (Expr.reg (Reg.x20)))), LinstrR.Llabel (LabelKind.internal) 32, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x23))
      (Expr.reg (Reg.x21)))), LinstrR.Llabel (LabelKind.internal) 33, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x18)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 34, LinstrR.Lopn (Op.set (Reg.x1) (Expr.imm L.s3.hi)), LinstrR.Llabel (LabelKind.internal) 35, LinstrR.Lcall (L.base + 0x90#64) (Target.indirect (Expr.bin (BinOp.and) (Expr.bin (BinOp.add) (Expr.reg (Reg.x1)) (Expr.imm L.s3.lo)) (Expr.imm 0xfffffffffffffffe#64)) [L.reduce.idx]), LinstrR.Llabel (LabelKind.internal) 36, LinstrR.Lopn
  (Op.set
    (Reg.x19)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 37, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.lshr)
      (Expr.reg (Reg.x22))
      (Expr.imm 0x000000000000003f#64))), LinstrR.Llabel (LabelKind.internal) 38, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x23)) (Expr.imm 0x0000000000000001#64))), LinstrR.Llabel (LabelKind.internal) 39, LinstrR.Lopn
  (Op.set
    (Reg.x22)
    (Expr.bin (BinOp.shl) (Expr.reg (Reg.x22)) (Expr.imm 0x0000000000000001#64))), LinstrR.Llabel (LabelKind.internal) 40, LinstrR.Lopn
  (Op.set
    (Reg.x12)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x9))
      (Expr.reg (Reg.x21)))), LinstrR.Llabel (LabelKind.internal) 41, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.or)
      (Expr.reg (Reg.x11))
      (Expr.reg (Reg.x10)))), LinstrR.Llabel (LabelKind.internal) 42, LinstrR.Lopn
  (Op.set
    (Reg.x13)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x22))
      (Expr.reg (Reg.x8)))), LinstrR.Llabel (LabelKind.internal) 43, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x12)))), LinstrR.Llabel (LabelKind.internal) 44, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x10))
      (Expr.reg (Reg.x23)))), LinstrR.Llabel (LabelKind.internal) 45, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin
      (BinOp.xor)
      (Expr.reg (Reg.x13))
      (Expr.reg (Reg.x18)))), LinstrR.Llabel (LabelKind.internal) 46, LinstrR.Lopn (Op.set (Reg.x1) (Expr.imm L.s4.hi)), LinstrR.Llabel (LabelKind.internal) 47, LinstrR.Lcall (L.base + 0xc0#64) (Target.indirect (Expr.bin (BinOp.and) (Expr.bin (BinOp.add) (Expr.reg (Reg.x1)) (Expr.imm L.s4.lo)) (Expr.imm 0xfffffffffffffffe#64)) [L.reduce.idx]), LinstrR.Llabel (LabelKind.internal) 48, LinstrR.Lopn
  (Op.set
    (Reg.x11)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x10)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 49, LinstrR.Lopn
  (Op.set
    (Reg.x10)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x19)) (Expr.imm 0x0000000000000000#64))), LinstrR.Llabel (LabelKind.internal) 50, LinstrR.Lopn
  (Op.load
    (Reg.x1)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000048#64))), LinstrR.Llabel (LabelKind.internal) 51, LinstrR.Lopn
  (Op.load
    (Reg.x8)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000040#64))), LinstrR.Llabel (LabelKind.internal) 52, LinstrR.Lopn
  (Op.load
    (Reg.x9)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000038#64))), LinstrR.Llabel (LabelKind.internal) 53, LinstrR.Lopn
  (Op.load
    (Reg.x18)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000030#64))), LinstrR.Llabel (LabelKind.internal) 54, LinstrR.Lopn
  (Op.load
    (Reg.x19)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000028#64))), LinstrR.Llabel (LabelKind.internal) 55, LinstrR.Lopn
  (Op.load
    (Reg.x20)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000020#64))), LinstrR.Llabel (LabelKind.internal) 56, LinstrR.Lopn
  (Op.load
    (Reg.x21)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000018#64))), LinstrR.Llabel (LabelKind.internal) 57, LinstrR.Lopn
  (Op.load
    (Reg.x22)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000010#64))), LinstrR.Llabel (LabelKind.internal) 58, LinstrR.Lopn
  (Op.load
    (Reg.x23)
    (Width.b8)
    false
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000008#64))), LinstrR.Llabel (LabelKind.internal) 59, LinstrR.Lopn
  (Op.set
    (Reg.x2)
    (Expr.bin (BinOp.add) (Expr.reg (Reg.x2)) (Expr.imm 0x0000000000000050#64))), LinstrR.Llabel (LabelKind.internal) 60, LinstrR.Lret]
  }

/-- The facts of `L` the proof uses: each callee is where `L` says (`Callee.WF`), and each site reaches its callee
    (`Site.WF`), as equations for `simp`. -/
structure Link.WF (p : Lprog (Op Reg) Reg) (L : Link) : Prop where
  clmul : (p[L.clmul.idx]?).map (·.addr) = some L.clmul.entry
  reduce : (p[L.reduce.idx]?).map (·.addr) = some L.reduce.entry
  s0 : (L.s0.hi + L.s0.lo) &&& 0xfffffffffffffffe#64 = L.clmul.entry
  s1 : (L.s1.hi + L.s1.lo) &&& 0xfffffffffffffffe#64 = L.clmul.entry
  s2 : (L.s2.hi + L.s2.lo) &&& 0xfffffffffffffffe#64 = L.clmul.entry
  s3 : (L.s3.hi + L.s3.lo) &&& 0xfffffffffffffffe#64 = L.reduce.entry
  s4 : (L.s4.hi + L.s4.lo) &&& 0xfffffffffffffffe#64 = L.reduce.entry

end Rv64mc.Tactic.Bench.EMul
