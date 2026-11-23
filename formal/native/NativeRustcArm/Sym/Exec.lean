module

public import NativeRustcArm.Sym.Basic

/-!
# The symbolic executor

`Sym.exec ds S`: the basic block `ds` run on the symbolic state `S`, with how it ends, or `none`
where the executor cannot follow it (an instruction form it does not know, an operand it does not
know, an access it cannot place in a region, a branch before the last directive). Each instruction
form's symbolic step mirrors Kraken's semantics (`Operation.interp`); the smart constructors
(`mkBin`, `mkUn`, `mkCmp`, ...) fold constants and keep addresses of the form `ptr r off`
(a region's base plus a constant), which `NativeRustcArm.Sym.Smart` proves sound. An access is at
a constant offset in a region (a pointer, or a label at a region's base, plus a constant); a load
may also be at a bounded index (`SState.bounds`) in a region no write of the block touches. A load
takes the bytes of the newest write covering them, else `env.mem0`'s (`loadSym`). All functions
are structural, for the kernel to evaluate.
-/

namespace NativeRustcArm

@[expose] public section

namespace Sym

/-! ## Smart constructors -/

/-- The literal, if the value is one. -/
def asLit : Sym → Option Nat
  | .lit n => some n
  | _ => none

/-- The region and offset, if the value is a region pointer. -/
def asPtr : Sym → Option (Nat × Int)
  | .ptr r o => some (r, o)
  | _ => none

/-- `0xFFFFFFFFFFFFF000`, the mask of `ADRP`. -/
def pageMask : Nat := 0xFFFFFFFFFFFFF000

/-- Whether the value is a label, possibly plus a literal: an address `ADRP` and `:lo12:` take. -/
def isLabelAddr : Sym → Bool
  | .label _ => true
  | .bin .add .W64 (.label _) (.lit _) => true
  | _ => false

/-- The address, if the value is the page of a label, possibly plus a literal (`ADRP`). -/
def asPage : Sym → Option Sym
  | .bin .and .W64 x (.lit n) => if n = pageMask ∧ x.isLabelAddr = true then some x else none
  | _ => none

/-- The address, if the value is the offset in its page of a label, possibly plus a literal
(`:lo12:`). -/
def asLo12 : Sym → Option Sym
  | .bin .and .W64 x (.lit n) => if n = 0xFFF ∧ x.isLabelAddr = true then some x else none
  | _ => none

/-- The value and literal, if the value is a 64-bit sum with a literal. -/
def asAddLit : Sym → Option (Sym × Nat)
  | .bin .add .W64 x (.lit c) => some (x, c)
  | _ => none

/-- The condition and branches, if the value is a conditional. -/
def asIte : Sym → Option (SBool × Sym × Sym)
  | .ite c x y => some (c, x, y)
  | _ => none

/-- Whether the value is below `2 ^ 32`, by its form. -/
def clean32 : Sym → Bool
  | .lit n => n < 2 ^ 32
  | .load _ _ n => n ≤ 4
  | .bin _ .W32 _ _ => true
  | .un (.memExtend _) _ _ => false
  | .un (.bytes _ n) _ _ => n ≤ 4
  | .un _ .W32 _ => true
  | _ => false

/-- The signed reading of a 64-bit literal. -/
def litInt (c : Nat) : Int := if c % 2 ^ 64 < 2 ^ 63 then (c % 2 ^ 64 : Nat) else (c % 2 ^ 64 : Nat) - 2 ^ 64

/-- The low bits of the width, zero-extended. -/
def truncTo : RegWidth → Sym → Sym
  | .W64, a => a
  | .W32, a => if a.clean32 then a else .un .trunc .W32 a

/-- `x` plus the literal `d`, a region pointer if `x` is one. -/
def addLit (x : Sym) (d : Nat) : Sym :=
  match x.asPtr with
  | some (r, o) => .ptr r (o + litInt d)
  | none => .bin .add .W64 x (.lit d)

/-- A 64-bit sum. -/
def mkAdd64 (a b : Sym) : Sym :=
  match a.asPtr, b.asLit with
  | some (r, o), some c => .ptr r (o + litInt c)
  | _, _ =>
    match a.asLit, b.asPtr with
    | some c, some (r, o) => .ptr r (o + litInt c)
    | _, _ =>
      match a.asPage, b.asLo12 with
      | some x, some x' => if x = x' then x else .bin .add .W64 a b
      | _, _ =>
        match a.asAddLit, b.asLit with
        | some (x, c), some d => .bin .add .W64 x (.lit ((c + d) % 2 ^ 64))
        | _, _ =>
          if b = .lit 0 then a else if a = .lit 0 then b else
          match a.asIte, b.asLit with
          | some (c, x, y), some d => .ite c (addLit x d) (addLit y d)
          | _, _ => .bin .add .W64 a b

/-- A 64-bit difference. -/
def mkSub64 (a b : Sym) : Sym :=
  match a.asPtr, b.asLit with
  | some (r, o), some c => .ptr r (o - litInt c)
  | _, _ =>
    match a.asPtr, b.asPtr with
    | some (r, o), some (r', o') =>
      if r = r' then .lit (BitVec.ofInt 64 (o - o')).toNat else .bin .sub .W64 a b
    | _, _ =>
      match a.asAddLit, b.asLit with
      | some (x, c), some d => .bin .add .W64 x (.lit ((c + (2 ^ 64 - d % 2 ^ 64)) % 2 ^ 64))
      | _, _ => if b = .lit 0 then a else .bin .sub .W64 a b

/-- A unary operation. -/
def mkUn (op : UnOp) (w : RegWidth) (a : Sym) : Sym :=
  match a.asLit with
  | some x => .lit (op.apply w (BitVec.ofNat 64 x)).toNat
  | none =>
    match op with
    | .trunc => truncTo w a
    | .shift _ 0 => truncTo w a
    | .bytes 0 8 => a
    | op => .un op w a

/-- A binary operation. -/
def mkBin (op : BinOp) (w : RegWidth) (a b : Sym) : Sym :=
  match a.asLit, b.asLit with
  | some x, some y => .lit (op.apply w (BitVec.ofNat 64 x) (BitVec.ofNat 64 y)).toNat
  | _, _ =>
    match op, w with
    | .add, .W64 => mkAdd64 a b
    | .sub, .W64 => mkSub64 a b
    | .orr, w => if a = .lit 0 then truncTo w b else if b = .lit 0 then truncTo w a
      else .bin .orr w a b
    | .eor, w => if b = .lit 0 then truncTo w a else .bin .eor w a b
    | .extr lsb, w => if a = b then mkUn (.shift .ROR lsb) w a else .bin (.extr lsb) w a b
    | op, w => .bin op w a b

/-- The `n` bytes of `v` from byte `t`. -/
def mkBytes (v : Sym) (t n : Nat) : Sym :=
  if t = 0 ∧ n = 4 ∧ v.clean32 then v else mkUn (.bytes t n) .W64 v

/-- A conditional value. -/
def mkIte (c : SBool) (a b : Sym) : Sym :=
  match c with
  | .lit true => a
  | .lit false => b
  | c => if a = b then a else .ite c a b

/-- Negation. -/
def mkNot : SBool → SBool
  | .lit b => .lit !b
  | .not b => b
  | b => .not b

/-- Conjunction. -/
def mkAnd (b c : SBool) : SBool :=
  match b, c with
  | .lit true, c => c
  | .lit false, _ => .lit false
  | b, .lit true => b
  | _, .lit false => .lit false
  | b, c => .and b c

/-- Disjunction. -/
def mkOr (b c : SBool) : SBool :=
  match b, c with
  | .lit true, _ => .lit true
  | .lit false, c => c
  | _, .lit true => .lit true
  | b, .lit false => b
  | b, c => .or b c

/-- Boolean equality. -/
def mkBeq (b c : SBool) : SBool :=
  match b, c with
  | .lit x, .lit y => .lit (x == y)
  | b, c => .beq b c

/-- A conditional boolean. -/
def mkIteB (c a b : SBool) : SBool :=
  match c with
  | .lit true => a
  | .lit false => b
  | c => if a = b then a else .ite c a b

/-- A comparison. -/
def mkCmp (op : CmpOp) (w : RegWidth) (a b : Sym) : SBool :=
  match a.asLit, b.asLit with
  | some x, some y => .lit (op.apply w (BitVec.ofNat 64 x) (BitVec.ofNat 64 y))
  | _, _ =>
    match op, w, a.asPtr, b.asPtr with
    | .eq, .W64, some (r, o), some (r', o') =>
      if r = r' then .lit (BitVec.ofInt 64 o == BitVec.ofInt 64 o') else .cmp op w a b
    | _, _, _, _ => .cmp op w a b

/-- The most significant bit. -/
def mkMsb (w : RegWidth) (a : Sym) : SBool :=
  match a.asLit with
  | some x => .lit (low w (BitVec.ofNat 64 x)).msb
  | none => .msb w a

/-- A bit. -/
def mkBit (w : RegWidth) (a : Sym) (n : Nat) : SBool :=
  match a.asLit with
  | some x => .lit ((low w (BitVec.ofNat 64 x)).getLsbD n)
  | none => .bit w a n

/-! ## Flags -/

/-- The flags of `a - b` (`SUBS`, `CMP`). -/
def subsFlags (w : RegWidth) (a b : Sym) : SFlags :=
  ⟨mkMsb w (mkBin .sub w a b), mkCmp .eq w a b, mkNot (mkCmp .ult w a b), mkCmp .subV w a b⟩

/-- The flags of `a + b` (`ADDS`, `CMN`). -/
def addsFlags (w : RegWidth) (a b : Sym) : SFlags :=
  ⟨mkMsb w (mkBin .add w a b), mkCmp .eq w (mkBin .add w a b) (.lit 0), mkCmp .addC w a b,
    mkCmp .addV w a b⟩

/-- The flags of a logical result (`ANDS`, `TST`, `BICS`). -/
def logicFlags (w : RegWidth) (r : Sym) : SFlags :=
  ⟨mkMsb w r, mkCmp .eq w r (.lit 0), .lit false, .lit false⟩

/-- The flags `StatusFlags.ofNat nzcv`. -/
def nzcvFlags (nzcv : Nat) : SFlags :=
  ⟨.lit ((nzcv &&& 8) != 0), .lit ((nzcv &&& 4) != 0), .lit ((nzcv &&& 2) != 0),
    .lit ((nzcv &&& 1) != 0)⟩

/-- The flags `f` if `c`, else `g`. -/
def SFlags.ite (c : SBool) (f g : SFlags) : SFlags :=
  ⟨mkIteB c f.n g.n, mkIteB c f.z g.z, mkIteB c f.c g.c, mkIteB c f.v g.v⟩

/-- A condition code on symbolic flags (`CondCode.interp`). -/
def condSym (cc : CondCode) (f : SFlags) : SBool :=
  match cc with
  | .EQ => f.z
  | .NE => mkNot f.z
  | .CS => f.c
  | .CC => mkNot f.c
  | .MI => f.n
  | .PL => mkNot f.n
  | .VS => f.v
  | .VC => mkNot f.v
  | .HI => mkAnd f.c (mkNot f.z)
  | .LS => mkOr (mkNot f.c) f.z
  | .GE => mkBeq f.n f.v
  | .LT => mkNot (mkBeq f.n f.v)
  | .GT => mkAnd (mkNot f.z) (mkBeq f.n f.v)
  | .LE => mkOr f.z (mkNot (mkBeq f.n f.v))
  | .AL => .lit true
  | .NV => .lit true

/-! ## Registers and operands -/

namespace SState

/-- Register `r` set to `v`. -/
def setReg (S : SState) (r : XReg) (v : Option Sym) : SState := { S with regs := S.regs.set r.idx v }

/-- A 64-bit read where index 31 is the zero register. -/
def getZr64 (S : SState) : XRegOrXzr → Option Sym
  | .XZR => some (.lit 0)
  | .reg r => S.reg r

/-- A 64-bit read where index 31 is SP. -/
def getSp64 (S : SState) : XRegOrSp → Option Sym
  | .SP => some S.sp
  | .reg r => S.reg r

/-- A register operand where index 31 is the zero register; its full 64-bit value. -/
def getZr (S : SState) {w : RegWidth} (r : RegOrZr w) : Option Sym := S.getZr64 r.base

/-- A register operand where index 31 is SP; its full 64-bit value. -/
def getSp (S : SState) {w : RegWidth} (r : RegOrSp w) : Option Sym := S.getSp64 r.base

/-- A write where index 31 is the zero register, of a value already zero-extended. -/
def setZr (S : SState) {w : RegWidth} (r : RegOrZr w) (v : Sym) : SState :=
  match r.base with
  | .XZR => S
  | .reg x => S.setReg x (some v)

/-- A write where index 31 is SP, of a value already zero-extended. -/
def setSp (S : SState) {w : RegWidth} (r : RegOrSp w) (v : Sym) : SState :=
  match r.base with
  | .SP => { S with sp := v }
  | .reg x => S.setReg x (some v)

/-- The flags set. -/
def setFlags (S : SState) (f : SFlags) : SState := { S with flags := some f }

/-- A shifted register operand (`ShiftRegExpr.interp`). -/
def shiftOp (S : SState) {w : RegWidth} (e : ShiftRegExpr w) : Option Sym := do
  let a ← S.getZr e.reg
  some (mkUn (.shift e.shift e.amount.toInt.toNat) w a)

end SState

/-- The address of an `ADRP` or `:lo12:` operand: a label, possibly plus a constant. -/
def labelAddr : ConstExpr → Option Sym
  | .label l => some (.label l)
  | .add (.label l) (.int64 c) => some (.bin .add .W64 (.label l) (.lit c.toBitVec.toNat))
  | _ => none

/-- An immediate operand of `ADD`/`SUB` (`ExtOrImmReg.interp`). -/
def immSym (w : RegWidth) : ConstExpr → ImmShift → Option Sym
  | .int64 k, .S0 => some (.lit (ext w (BitVec.ofInt w.bits k.toInt)).toNat)
  | .int64 k, .S12 => some (.lit (ext w (BitVec.ofInt w.bits (k.toInt <<< 12))).toNat)
  | .lo12 c, .S0 =>
    match w, labelAddr c with
    | .W64, some x => some (.bin .and .W64 x (.lit 0xFFF))
    | _, _ => none
  | _, _ => none

/-- An immediate of a logical instruction. -/
def logicImm (w : RegWidth) : ConstExpr → Option Sym
  | .int64 k => some (.lit (ext w (BitVec.ofInt w.bits k.toInt)).toNat)
  | _ => none

/-- An immediate offset. -/
def constInt : ConstExpr → Option Int
  | .int64 k => some k.toInt
  | _ => none

/-- A branch target. -/
def target : ConstExpr → Option Label
  | .label l => some l
  | _ => none

namespace SState

/-- The second operand of `ADD`/`SUB` (`ExtOrImmReg.interp`). -/
def extOrImm (S : SState) (w : RegWidth) : ExtOrImmReg → Option Sym
  | .ext e => do
    let a ← S.getZr64 e.reg.reg.base
    some (mkUn (.extend e.ext) w a)
  | .imm i => immSym w i.imm i.shift

/-! ## Memory -/

/-- The region and offset an address is by itself: an alias, a region pointer, a label at a
region's base. -/
def basePtr (S : SState) (a : Sym) : Option (Nat × Int) :=
  match S.aliases.lookup a with
  | some ro => some ro
  | none =>
    match a with
    | .ptr r o => some (r, o)
    | .label l => (S.labels.lookup l).map fun r => (r, 0)
    | _ => none

/-- The region and offset an address points to: a region pointer, a label at a region's base or
an alias, possibly plus a literal. -/
def toPtr (S : SState) (a : Sym) : Option (Nat × Int) :=
  match S.basePtr a with
  | some ro => some ro
  | none =>
    match a.asAddLit with
    | some (x, c) => (S.basePtr x).map fun ro => (ro.1, ro.2 + litInt c)
    | none => none

/-- The region and offset of an access of `n` bytes at `a`, if `a` points into a known region and
the access is within it. -/
def access (S : SState) (a : Sym) (n : Nat) : Option (Nat × Nat) :=
  match S.toPtr a with
  | some (r, o) =>
    match S.regions[r]? with
    | some (sz, _) => if 0 ≤ o ∧ o.toNat + n ≤ sz then some (r, o.toNat) else none
    | none => none
  | none => none

/-- The largest value an index can have by the bounds: an index register `x` with a bound
`(x, B)`, possibly shifted left by an address's extension (`[Xn, Xm, lsl #k]`) or a shifted
register operand (`add xd, xn, xm, lsl #k`). -/
def idxMax (S : SState) : Sym → Option Nat
  | .un (.memExtend ⟨.UXTX, k⟩) .W64 x =>
    (S.bounds.lookup x).map fun B => (B - 1) * 2 ^ (match k with
      | .E0 => 0 | .E1 => 1 | .E2 => 2 | .E3 => 3)
  | .un (.shift .LSL k) .W64 x => (S.bounds.lookup x).map fun B => (B - 1) * 2 ^ k
  | x => (S.bounds.lookup x).map fun B => B - 1

/-- An indexed access of `n` bytes at `p + i + d`: the region, offset, index and index bound. -/
def accessIdxAt (S : SState) (p i : Sym) (d : Int) (n : Nat) : Option (Nat × Nat × Sym × Nat) :=
  match S.toPtr p, S.idxMax i with
  | some (r, o), some M =>
    match S.regions[r]? with
    | some (sz, _) =>
      if 0 ≤ o + d ∧ (o + d).toNat + M + n ≤ sz then some (r, (o + d).toNat, i, M) else none
    | none => none
  | _, _ => none

/-- The region, offset, index and index bound of an indexed access of `n` bytes at `a` (a pointer
into a known region plus an index with a bound, possibly plus a literal), if the access is within
the region for every value of the index. -/
def accessIdx (S : SState) (a : Sym) (n : Nat) : Option (Nat × Nat × Sym × Nat) :=
  match a.asAddLit with
  | some (.bin .add .W64 p i, c) => S.accessIdxAt p i (litInt c) n
  | _ =>
    match a with
    | .bin .add .W64 p i => S.accessIdxAt p i 0 n
    | _ => none

/-- SP is a pointer into a 16-byte aligned region at an offset that is a multiple of 16. -/
def spAligned (S : SState) : Bool :=
  match S.sp with
  | .ptr r o =>
    match S.regions[r]? with
    | some (_, al) => al && o % 16 == 0
    | none => false
  | _ => false

/-- Kraken's check of SP's alignment for an access based on it (`AddrExpr.checkSPAlignment`). -/
def checkSp (S : SState) : RegOrSp .W64 → Bool
  | .low .SP .W64 => S.spAligned
  | _ => true

end SState

/-- The newest write overlapping the `n` bytes at `o` in region `r`. -/
def firstOverlap (r o n : Nat) : List Write → Option Write
  | [] => none
  | w :: ws => if w.r = r ∧ w.off < o + n ∧ o < w.off + w.n then some w else firstOverlap r o n ws

/-- The byte at `i` in region `r`: of the newest write covering it, else of `env.mem0`. -/
def byteSym (ws : List Write) (r i : Nat) : Sym :=
  match findWrite r i ws with
  | some (v, t) => mkBytes v t 1
  | none => .load r i 1

/-- The `n` bytes from `o` in region `r`, little-endian, assembled byte by byte. -/
def assemble (ws : List Write) (r : Nat) : Nat → Nat → Sym
  | _, 0 => .lit 0
  | o, n + 1 => mkBin .add .W64 (byteSym ws r o) (mkUn (.shift .LSL 8) .W64 (assemble ws r (o + 1) n))

/-- The `n` bytes at `o` in region `r`: `env.mem0`'s if no write overlaps them, part of the newest
overlapping write if it covers them, else assembled byte by byte. -/
def loadSym (ws : List Write) (r o n : Nat) : Sym :=
  match firstOverlap r o n ws with
  | none => .load r o n
  | some w =>
    if w.off ≤ o ∧ o + n ≤ w.off + w.n then mkBytes w.v (o - w.off) n else assemble ws r o n

/-! ## Indexed accesses as slots

An access at `o + s * x` in a region, `x` a value with a bound `B` (`SState.bounds`) and the scale
`s` at least the access's size, is at one of the `B` slots `o + s * k`. A store writes each slot,
the stored value at slot `k` if `x = k`, else the bytes already there (`slotWrite`); a load is the
conditional over the slots of their bytes (`slotLoad`), where a slot's bytes conditional on `x`
(an earlier indexed store at `x`) are picked (`underEq`). -/

/-- The shift of a memory extension's amount. -/
def extAmt : MemExtendAmount → Nat
  | .E0 => 0 | .E1 => 1 | .E2 => 2 | .E3 => 3

/-- A value as a value times a scale: `x * s` (a multiplication by a constant), `x << j` (a
shifted register), else the value itself at scale `1`. -/
def scaled : Sym → Sym × Nat
  | .bin .mul .W64 x (.lit s) => (x, s)
  | .un (.shift .LSL j) .W64 x => (x, 2 ^ j)
  | x => (x, 1)

/-- An index as a value times a scale: a memory extension `y << k` (`[Xn, Xm, lsl #k]`) of a
scaled value `y` (`scaled`), else a scaled value. -/
def idxScale : Sym → Sym × Nat
  | .un (.memExtend ⟨.UXTX, k⟩) .W64 y => ((scaled y).1, 2 ^ extAmt k * (scaled y).2)
  | y => scaled y

/-- Where `x = k`: a conditional on whether `x = j` is its branch. -/
def pickEq (x : Sym) (k : Nat) : Sym → Sym
  | .ite (.cmp .eq .W64 y (.lit j)) a b =>
    if y = x ∧ j < 2 ^ 64 ∧ k < 2 ^ 64 then (if j = k then a else b)
    else .ite (.cmp .eq .W64 y (.lit j)) a b
  | v => v

/-- Where `x = k`: `pickEq`, also under a unary operation. -/
def underEq (x : Sym) (k : Nat) : Sym → Sym
  | .un op w a => .un op w (pickEq x k a)
  | v => pickEq x k v

/-- Slot `k` of a store of `v` at `o + s * x` in region `r`: `v` if `x = k`, else the bytes there. -/
def slotWrite (ws : List Write) (r o s n : Nat) (x v : Sym) (k : Nat) : Write :=
  ⟨r, o + s * k, n, mkIte (mkCmp .eq .W64 x (.lit k)) v (loadSym ws r (o + s * k) n)⟩

/-- A load of `n` bytes at `o + s * x` in region `r` for `x` from `k` to `k + c`: the conditional
over the slots, the last one where `x` is none of the others. -/
def slotLoad (ws : List Write) (r o s n : Nat) (x : Sym) : Nat → Nat → Sym
  | k, 0 => underEq x k (loadSym ws r (o + s * k) n)
  | k, c + 1 => mkIte (mkCmp .eq .W64 x (.lit k)) (underEq x k (loadSym ws r (o + s * k) n))
      (slotLoad ws r o s n x (k + 1) c)

namespace SState

/-- An indexed access of `n` bytes at `p + i + d` as slots: the region, the offset, the bounded
value `x`, the scale `s` and the bound `B`, `i = s * x` (`idxScale`), `n ≤ s`, every slot in the
region. -/
def slotsAt (S : SState) (p i : Sym) (d : Int) (n : Nat) :
    Option (Nat × Nat × Sym × Nat × Nat) :=
  match S.toPtr p, S.bounds.lookup (idxScale i).1 with
  | some (r, o), some B =>
    match S.regions[r]? with
    | some (sz, _) =>
      if 0 ≤ o + d ∧ n ≤ (idxScale i).2 ∧ 0 < n ∧ 0 < B ∧
          (o + d).toNat + (idxScale i).2 * (B - 1) + n ≤ sz then
        some (r, (o + d).toNat, (idxScale i).1, (idxScale i).2, B)
      else none
    | none => none
  | _, _ => none

/-- An indexed access of `n` bytes at `x + y + d` as slots, either of `x`, `y` the pointer. -/
def slots2 (S : SState) (x y : Sym) (d : Int) (n : Nat) : Option (Nat × Nat × Sym × Nat × Nat) :=
  match S.slotsAt x y d n with
  | some res => some res
  | none => S.slotsAt y x d n

/-- An indexed access of `n` bytes at `a` as slots (`slotsAt`): a pointer plus an index, either
first, possibly plus a literal. -/
def slots (S : SState) (a : Sym) (n : Nat) : Option (Nat × Nat × Sym × Nat × Nat) :=
  match a with
  | .bin .add .W64 (.bin .add .W64 x y) (.lit c) => S.slots2 x y (litInt c) n
  | .bin .add .W64 x y => S.slots2 x y 0 n
  | _ => none

/-- An indexed load as the conditional over the slots (`slotLoad`). -/
def loadSlots (S : SState) (a : Sym) (n : Nat) : Option Sym :=
  match S.slots a n with
  | some (r, o, x, s, B) => some (slotLoad S.mem r o s n x 0 (B - 1))
  | none => none

/-- An indexed store of `v` as a write to each slot (`slotWrite`). -/
def storeSlots (S : SState) (r o s n : Nat) (x v : Sym) (B : Nat) : SState :=
  { S with mem := (List.range B).map (slotWrite S.mem r o s n x v) ++ S.mem }

/-- `S` with the alias `x ↦ (r, o)`: `x`'s value is region `r`'s base plus `o` (a fact a proof
adds, `Match.withAlias`). -/
def withAlias (S : SState) (x : Sym) (r : Nat) (o : Int) : SState :=
  { S with aliases := (x, r, o) :: S.aliases }

/-- `S` with the bound `x < B` (a fact a proof adds, `Match.withBound`). -/
def withBound (S : SState) (x : Sym) (B : Nat) : SState :=
  { S with bounds := (x, B) :: S.bounds }

/-- The writes with `v`'s low `n` bytes at `o` in region `r`, dropping the writes it covers. -/
def store (S : SState) (r o n : Nat) (v : Sym) : SState :=
  { S with mem := ⟨r, o, n, v⟩ :: S.mem.filter fun w => !(w.r = r ∧ o ≤ w.off ∧ w.off + w.n ≤ o + n) }

/-- A load of `n` bytes at `a`: at a constant offset in a region, at an indexed offset in a
region where no write overlaps the bytes the index can reach, else over the slots of an index
with a bound (`loadSlots`). -/
def loadOne (S : SState) (a : Sym) (n : Nat) : Option Sym :=
  match S.access a n with
  | some (r, o) => some (loadSym S.mem r o n)
  | none =>
    match S.accessIdx a n with
    | some (r, o, i, M) =>
      if S.mem.all (fun w => w.r != r || w.off + w.n ≤ o || o + M + n ≤ w.off) then
        some (.loadx r o i n)
      else S.loadSlots a n
    | none => S.loadSlots a n

/-- A load of `n` bytes at `a`, or at each branch of a conditional address. -/
def loadAt (S : SState) (a : Sym) (n : Nat) : Option Sym :=
  match a.asIte with
  | some (c, x, y) => do
    let vx ← S.loadOne x n
    let vy ← S.loadOne y n
    some (mkIte c vx vy)
  | none => S.loadOne a n

/-- A store of the low `n` bytes of `v` at `a`: at a constant offset in a region, else to the
slots of an index with a bound (`storeSlots`). -/
def storeAt (S : SState) (a : Sym) (n : Nat) (v : Sym) : Option SState :=
  match S.access a n with
  | some (r, o) => some (S.store r o n v)
  | none =>
    match S.slots a n with
    | some (r, o, x, s, B) => some (S.storeSlots r o s n x v B)
    | none => none

/-- An address operand (`AddrExpr.eval`): the address and the state after the base's
writeback. -/
def addr (S : SState) (ae : AddrExpr) : Option (Sym × SState) := do
  let b ← S.getSp ae.base
  match ae.off with
  | .reg e => do
    let i ← S.getZr64 e.reg.reg.base
    some (mkBin .add .W64 b (mkUn (.memExtend e.ext) .W64 i), S)
  | .imm i => do
    let off ← constInt i.imm
    let a := mkBin .add .W64 b (.lit (BitVec.ofInt 64 off).toNat)
    match i.index with
    | none => some (a, S)
    | some .Pre => some (a, S.setSp ae.base a)
    | some .Post => some (b, S.setSp ae.base a)

/-- An unscaled address operand (`UnscaledAddrExpr.eval`). -/
def uaddr (S : SState) (ua : UnscaledAddrExpr) : Option Sym := do
  let b ← S.getSp ua.base
  let off ← constInt ua.imm
  some (mkBin .add .W64 b (.lit (BitVec.ofInt 64 off).toNat))

end SState

/-! ## Instructions -/

/-- The result of a step that falls through. -/
abbrev fall (S : SState) : Option (SState × Exit) := some (S, .fall)

namespace Step
variable {w : RegWidth}

/-- `op dst, src1, src2` with a shifted register `src2`. -/
def shifted (op : BinOp) (dst src1 : RegOrZr w) (src2 : ShiftRegExpr w) (S : SState) :
    Option (SState × Exit) := do
  let a ← S.getZr src1
  let b ← S.shiftOp src2
  fall (S.setZr dst (mkBin op w a b))

/-- `ANDS`/`BICS dst, src1, src2` with a shifted register `src2`. -/
def shiftedFlags (op : BinOp) (dst src1 : RegOrZr w) (src2 : ShiftRegExpr w) (S : SState) :
    Option (SState × Exit) := do
  let a ← S.getZr src1
  let b ← S.shiftOp src2
  let r := mkBin op w a b
  fall ((S.setFlags (logicFlags w r)).setZr dst r)

/-- `op dst, src1, #imm` of a logical instruction (`AND`, `ORR`, `EOR`). -/
def logicI (op : BinOp) (dst : RegOrSp w) (src1 : RegOrZr w) (imm : ConstExpr) (S : SState) :
    Option (SState × Exit) := do
  let a ← S.getZr src1
  let b ← logicImm w imm
  fall (S.setSp dst (mkBin op w a b))

/-- `ANDS dst, src1, #imm`. -/
def andsI (dst : RegOrZr w) (src1 : RegOrZr w) (imm : ConstExpr) (S : SState) :
    Option (SState × Exit) := do
  let a ← S.getZr src1
  let b ← logicImm w imm
  let r := mkBin .and w a b
  fall ((S.setFlags (logicFlags w r)).setZr dst r)

/-- `ADD`/`SUB dst, src1, src2` with an extended register or immediate `src2`. -/
def arithE (op : BinOp) (dst : RegOrSp w) (src1 : RegOrSp w) (src2 : ExtOrImmReg) (S : SState) :
    Option (SState × Exit) := do
  let a ← S.getSp src1
  let b ← S.extOrImm w src2
  fall (S.setSp dst (mkBin op w a b))

/-- `ADDS`/`SUBS dst, src1, src2` with an extended register or immediate `src2`. -/
def arithFlagsE (sub : Bool) (dst : RegOrZr w) (src1 : RegOrSp w) (src2 : ExtOrImmReg)
    (S : SState) : Option (SState × Exit) := do
  let a ← S.getSp src1
  let b ← S.extOrImm w src2
  if sub then fall ((S.setFlags (subsFlags w a b)).setZr dst (mkBin .sub w a b))
  else fall ((S.setFlags (addsFlags w a b)).setZr dst (mkBin .add w a b))

/-- `ADDS`/`SUBS dst, src1, src2` with a shifted register `src2`. -/
def arithFlagsS (sub : Bool) (dst src1 : RegOrZr w) (src2 : ShiftRegExpr w) (S : SState) :
    Option (SState × Exit) := do
  let a ← S.getZr src1
  let b ← S.shiftOp src2
  if sub then fall ((S.setFlags (subsFlags w a b)).setZr dst (mkBin .sub w a b))
  else fall ((S.setFlags (addsFlags w a b)).setZr dst (mkBin .add w a b))

/-- `op dst, src1, src2` with registers (`LSLV`, ...). -/
def reg3 (op : BinOp) (dst src1 src2 : RegOrZr w) (S : SState) : Option (SState × Exit) := do
  let a ← S.getZr src1
  let b ← S.getZr src2
  fall (S.setZr dst (mkBin op w a b))

/-- `MADD`/`MSUB dst, src1, src2, src3`. -/
def mulAcc (sub : Bool) (dst src1 src2 src3 : RegOrZr w) (S : SState) :
    Option (SState × Exit) := do
  let a ← S.getZr src1
  let b ← S.getZr src2
  let c ← S.getZr src3
  if sub then fall (S.setZr dst (mkBin .sub w c (mkBin .mul w a b)))
  else fall (S.setZr dst (mkBin .add w (mkBin .mul w a b) c))

/-- `UMADDL dst, src1, src2, src3`: the product of the low 32 bits of `src1` and `src2`, plus
`src3`. -/
def umaddl (dst : RegOrZr .W64) (src1 src2 : RegOrZr .W32) (src3 : RegOrZr .W64) (S : SState) :
    Option (SState × Exit) := do
  let a ← S.getZr src1
  let b ← S.getZr src2
  let c ← S.getZr src3
  fall (S.setZr dst (mkBin .add .W64 (mkBin .mul .W64 (truncTo .W32 a) (truncTo .W32 b)) c))

/-- A unary operation `dst := op src`. -/
def unary (op : UnOp) (dst src : RegOrZr w) (S : SState) : Option (SState × Exit) := do
  let a ← S.getZr src
  fall (S.setZr dst (mkUn op w a))

/-- `BFM dst, src, #immr, #imms`. -/
def bfm (dst src : RegOrZr w) (immr imms : Nat) (S : SState) : Option (SState × Exit) := do
  let d ← S.getZr dst
  let a ← S.getZr src
  fall (S.setZr dst (mkBin (.bfm immr imms) w d a))

/-- The 16-bit immediate of a move wide instruction, shifted. -/
def movVal (w : RegWidth) (imm : ConstExpr) (sh : MovShift w) : Option (BitVec w.bits) :=
  match imm with
  | .int64 k => some ((BitVec.ofInt w.bits k.toInt &&& 0xFFFF#w.bits) <<< sh.toNat)
  | _ => none

/-- `MOVZ`/`MOVN dst, #imm, LSL #sh`. -/
def movzn (inv : Bool) (dst : RegOrZr w) (imm : ConstExpr) (sh : MovShift w) (S : SState) :
    Option (SState × Exit) := do
  let v ← movVal w imm sh
  fall (S.setZr dst (.lit (ext w (if inv then ~~~v else v)).toNat))

/-- `MOVK dst, #imm, LSL #sh`. -/
def movk (dst : RegOrZr w) (imm : ConstExpr) (sh : MovShift w) (S : SState) :
    Option (SState × Exit) := do
  let old ← S.getZr dst
  let v ← movVal w imm sh
  fall (S.setZr dst (mkBin .orr w (mkBin .and w old (.lit (ext w (~~~(0xFFFF#w.bits <<< sh.toNat))).toNat))
    (.lit (ext w v).toNat)))

/-- `CSEL`/`CSINC`/`CSINV`/`CSNEG dst, src1, src2, cond`: `src2` through `op` when `cond` fails. -/
def csel (op : UnOp) (dst src1 src2 : RegOrZr w) (cond : CondCode) (S : SState) :
    Option (SState × Exit) := do
  let f ← S.flags
  let a ← S.getZr src1
  let b ← S.getZr src2
  fall (S.setZr dst (mkIte (condSym cond f) (truncTo w a) (mkUn op w b)))

/-- `CCMP`/`CCMN src1, src2, #nzcv, cond` with the second operand's value `b`. -/
def ccmp (sub : Bool) (src1 : RegOrZr w) (b : Option Sym) (nzcv : Nat) (cond : CondCode)
    (S : SState) : Option (SState × Exit) := do
  let f ← S.flags
  let a ← S.getZr src1
  let b ← b
  let g := if sub then subsFlags w a b else addsFlags w a b
  fall (S.setFlags (SFlags.ite (condSym cond f) g (nzcvFlags nzcv)))

/-- A load of `mw.bytes` bytes into `dst`. -/
def load (mw : MemWidth) (dst : RegOrZr w) (ae : AddrExpr) (S : SState) :
    Option (SState × Exit) := do
  if S.checkSp ae.base then
    let (a, S₁) ← S.addr ae
    let v ← S₁.loadAt a mw.bytes
    fall (S₁.setZr dst v)
  else none

/-- An unscaled load of `mw.bytes` bytes into `dst`. -/
def uload (mw : MemWidth) (dst : RegOrZr w) (ua : UnscaledAddrExpr) (S : SState) :
    Option (SState × Exit) := do
  if S.checkSp ua.base then
    let a ← S.uaddr ua
    let v ← S.loadAt a mw.bytes
    fall (S.setZr dst v)
  else none

/-- A store of the low `mw.bytes` bytes of `src`. -/
def store (mw : MemWidth) (src : RegOrZr w) (ae : AddrExpr) (S : SState) :
    Option (SState × Exit) := do
  if S.checkSp ae.base then
    let v ← S.getZr src
    let (a, S₁) ← S.addr ae
    let S₂ ← S₁.storeAt a mw.bytes v
    fall S₂
  else none

/-- An unscaled store of the low `mw.bytes` bytes of `src`. -/
def ustore (mw : MemWidth) (src : RegOrZr w) (ua : UnscaledAddrExpr) (S : SState) :
    Option (SState × Exit) := do
  if S.checkSp ua.base then
    let v ← S.getZr src
    let a ← S.uaddr ua
    let S₂ ← S.storeAt a mw.bytes v
    fall S₂
  else none

/-- `LDP dst1, dst2, [...]`. -/
def ldp (dst1 dst2 : RegOrZr w) (ae : AddrExpr) (S : SState) : Option (SState × Exit) := do
  if S.checkSp ae.base then
    let (a, S₁) ← S.addr ae
    let v₁ ← S₁.loadAt a (w : MemWidth).bytes
    let v₂ ← S₁.loadAt (mkBin .add .W64 a (.lit (w : MemWidth).bytes)) (w : MemWidth).bytes
    fall ((S₁.setZr dst1 v₁).setZr dst2 v₂)
  else none

/-- `STP src1, src2, [...]`. -/
def stp (src1 src2 : RegOrZr w) (ae : AddrExpr) (S : SState) : Option (SState × Exit) := do
  if S.checkSp ae.base then
    let v₁ ← S.getZr src1
    let v₂ ← S.getZr src2
    let (a, S₁) ← S.addr ae
    let S₂ ← S₁.storeAt a (w : MemWidth).bytes v₁
    let S₃ ← S₂.storeAt (mkBin .add .W64 a (.lit (w : MemWidth).bytes)) (w : MemWidth).bytes v₂
    fall S₃
  else none

/-- `LDR` of an address operand; a literal operand is not supported. -/
def ldr (mw : MemWidth) (dst : RegOrZr w) : AddrOrLit → SState → Option (SState × Exit)
  | .addr ae, S => load mw dst ae S
  | .lit _, _ => none

/-- `ADRP dst, t` of a label, possibly plus a constant: its page. -/
def adrp (dst : RegOrZr .W64) (t : ConstExpr) (S : SState) : Option (SState × Exit) := do
  let x ← labelAddr t
  fall (S.setZr dst (.bin .and .W64 x (.lit pageMask)))

/-- `RET`; only to X30. -/
def ret : RegOrZr .W64 → SState → Option (SState × Exit)
  | .low (.reg .X30) .W64, S => some (S, .ret)
  | _, _ => none

/-- A conditional branch on `c` to `t`. -/
def branch (c : SBool) (t : ConstExpr) (S : SState) : Option (SState × Exit) := do
  let l ← target t
  some (S, .cond c l)

end Step

/-- One instruction's symbolic step. -/
def stepOp {w : RegWidth} (op : Operation w) (S : SState) : Option (SState × Exit) :=
  match op with
  | .LDR dst src => Step.ldr (w : MemWidth) dst src S
  | .STR src ae => Step.store (w : MemWidth) src ae S
  | .LDUR dst ua => Step.uload (w : MemWidth) dst ua S
  | .STUR src ua => Step.ustore (w : MemWidth) src ua S
  | .LDP dst1 dst2 ae => Step.ldp dst1 dst2 ae S
  | .STP src1 src2 ae => Step.stp src1 src2 ae S
  | .LDRB dst ae => Step.load .W8 dst ae S
  | .LDURB dst ua => Step.uload .W8 dst ua S
  | .STRB src ae => Step.store .W8 src ae S
  | .STURB src ua => Step.ustore .W8 src ua S
  | .LDRH dst ae => Step.load .W16 dst ae S
  | .LDURH dst ua => Step.uload .W16 dst ua S
  | .STRH src ae => Step.store .W16 src ae S
  | .STURH src ua => Step.ustore .W16 src ua S
  | .ADD_e dst src1 src2 => Step.arithE .add dst src1 src2 S
  | .ADD_s dst src1 src2 => Step.shifted .add dst src1 src2 S
  | .ADDS_e dst src1 src2 => Step.arithFlagsE false dst src1 src2 S
  | .ADDS_s dst src1 src2 => Step.arithFlagsS false dst src1 src2 S
  | .SUB_e dst src1 src2 => Step.arithE .sub dst src1 src2 S
  | .SUB_s dst src1 src2 => Step.shifted .sub dst src1 src2 S
  | .SUBS_e dst src1 src2 => Step.arithFlagsE true dst src1 src2 S
  | .SUBS_s dst src1 src2 => Step.arithFlagsS true dst src1 src2 S
  | .MADD dst src1 src2 src3 => Step.mulAcc false dst src1 src2 src3 S
  | .MSUB dst src1 src2 src3 => Step.mulAcc true dst src1 src2 src3 S
  | .UMULH dst src1 src2 => Step.reg3 .umulh dst src1 src2 S
  | .UMADDL dst src1 src2 src3 => Step.umaddl dst src1 src2 src3 S
  | .AND_i dst src1 imm => Step.logicI .and dst src1 imm S
  | .AND_s dst src1 src2 => Step.shifted .and dst src1 src2 S
  | .ANDS_i dst src1 imm => Step.andsI dst src1 imm S
  | .ANDS_s dst src1 src2 => Step.shiftedFlags .and dst src1 src2 S
  | .ORR_i dst src1 imm => Step.logicI .orr dst src1 imm S
  | .ORR_s dst src1 src2 => Step.shifted .orr dst src1 src2 S
  | .ORN_s dst src1 src2 => Step.shifted .orn dst src1 src2 S
  | .EOR_i dst src1 imm => Step.logicI .eor dst src1 imm S
  | .EOR_s dst src1 src2 => Step.shifted .eor dst src1 src2 S
  | .EON_s dst src1 src2 => Step.shifted .eon dst src1 src2 S
  | .BIC_s dst src1 src2 => Step.shifted .bic dst src1 src2 S
  | .BICS_s dst src1 src2 => Step.shiftedFlags .bic dst src1 src2 S
  | .BFM dst src immr imms => Step.bfm dst src immr imms S
  | .SBFM dst src immr imms => Step.unary (.sbfm immr imms) dst src S
  | .UBFM dst src immr imms => Step.unary (.ubfm immr imms) dst src S
  | .REV dst src => Step.unary .rev dst src S
  | .RBIT dst src => Step.unary .rbit dst src S
  | .EXTR dst src1 src2 lsb => Step.reg3 (.extr lsb) dst src1 src2 S
  | .MOVZ dst imm sh => Step.movzn false dst imm sh S
  | .MOVK dst imm sh => Step.movk dst imm sh S
  | .MOVN dst imm sh => Step.movzn true dst imm sh S
  | .LSLV dst src1 src2 => Step.reg3 .lslv dst src1 src2 S
  | .LSRV dst src1 src2 => Step.reg3 .lsrv dst src1 src2 S
  | .ASRV dst src1 src2 => Step.reg3 .asrv dst src1 src2 S
  | .RORV dst src1 src2 => Step.reg3 .rorv dst src1 src2 S
  | .CSEL dst src1 src2 cond => Step.csel .trunc dst src1 src2 cond S
  | .CSINC dst src1 src2 cond => Step.csel .inc dst src1 src2 cond S
  | .CSINV dst src1 src2 cond => Step.csel .not dst src1 src2 cond S
  | .CSNEG dst src1 src2 cond => Step.csel .neg dst src1 src2 cond S
  | .CCMP_reg src1 src2 nzcv cond => Step.ccmp true src1 (S.getZr src2) nzcv cond S
  | .CCMP_imm src1 imm nzcv cond =>
    Step.ccmp true src1 (some (.lit (ext w (BitVec.ofNat w.bits imm)).toNat)) nzcv cond S
  | .CCMN_reg src1 src2 nzcv cond => Step.ccmp false src1 (S.getZr src2) nzcv cond S
  | .CCMN_imm src1 imm nzcv cond =>
    Step.ccmp false src1 (some (.lit (ext w (BitVec.ofNat w.bits imm)).toNat)) nzcv cond S
  | .ADRP dst t => Step.adrp dst t S
  | .B t => do
    let l ← target t
    some (S, .jump l)
  | .B_cond cond t => do
    let f ← S.flags
    Step.branch (condSym cond f) t S
  | .BL t => do
    let l ← target t
    some (S.setReg .X30 none, .call l)
  | .RET r => Step.ret r S
  | .CBZ r t => do
    let a ← S.getZr r
    Step.branch (mkCmp .eq w a (.lit 0)) t S
  | .CBNZ r t => do
    let a ← S.getZr r
    Step.branch (mkNot (mkCmp .eq w a (.lit 0))) t S
  | .TBZ r bit t => do
    let a ← S.getZr r
    Step.branch (mkNot (mkBit w a bit)) t S
  | .TBNZ r bit t => do
    let a ← S.getZr r
    Step.branch (mkBit w a bit) t S
  | .NOP => fall S
  | _ => none

/-- One directive's symbolic step: a label is a no-op, data is not code. -/
def stepD : Directive → SState → Option (SState × Exit)
  | .label _, S => some (S, .fall)
  | .instr i, S => stepOp i.operation S
  | _, _ => none

/-- **The symbolic executor**: the block `ds` run on `S`, and how it ends. Only its last directive
may branch. -/
def exec : List Directive → SState → Option (SState × Exit)
  | [], S => some (S, .fall)
  | d :: ds, S =>
    match stepD d S with
    | some (S', .fall) => exec ds S'
    | some (S', x) =>
      match ds with
      | [] => some (S', x)
      | _ :: _ => none
    | none => none

end Sym

end

end NativeRustcArm
