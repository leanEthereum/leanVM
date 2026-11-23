module

public import NativeRustcX64.Sym.Basic

/-!
# The symbolic executor

`Sym.exec ds S`: the basic block `ds` run on the symbolic state `S`, with how it ends, or `none`
where the executor cannot follow it (an instruction form it does not know, an operand it does not
know, an access it cannot place in a region, a branch before the last directive, an address size
other than 64 bits). Each instruction form's symbolic step mirrors Kraken's semantics
(`Operation.interp`); the smart constructors (`mkBin`, `mkUn`, `mkCmp`, ...) fold constants and
keep addresses of the form `ptr r off` (a region's base plus a constant), which
`NativeRustcX64.Sym.Smart` proves sound; a load at a conditional address (from `CMOV`) is the
conditional of the loads. Flags Kraken leaves undefined, or that the executor does not follow (the
overflow of shifts, the carry and overflow of rotations, the flags of `IMUL`, `SHLD`, `SHRD` and
of shifts by `%cl`, the flags of `MUL` but CF and OF), become unknown. All functions are structural,
for the kernel to evaluate.
-/

namespace NativeRustcX64

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

/-- The condition and branches, if the value is a conditional. -/
def asIte : Sym → Option (SBool × Sym × Sym)
  | .ite c x y => some (c, x, y)
  | _ => none

/-- Whether the value is below `2 ^ 32`, by its form. -/
def clean32 : Sym → Bool
  | .lit n => n < 2 ^ 32
  | .load _ _ n => n ≤ 4
  | .loadx _ _ _ n => n ≤ 4
  | .bin .merge _ _ _ => false
  | .bin _ w _ _ => w != .W64
  | .un (.bytes _ n) _ _ => n ≤ 4
  | .un .bswap _ _ => false
  | .un _ w _ => w != .W64
  | .tern _ w _ _ _ => w != .W64
  | _ => false

/-- The signed reading of a 64-bit literal. -/
def litInt (c : Nat) : Int :=
  if c % 2 ^ 64 < 2 ^ 63 then (c % 2 ^ 64 : Nat) else (c % 2 ^ 64 : Nat) - 2 ^ 64

/-- The low bits of the width, zero-extended. -/
def truncTo : Width → Sym → Sym
  | .W64, a => a
  | w, .lit n => .lit (ext w (low w (BitVec.ofNat 64 n))).toNat
  | .W32, a => if a.clean32 then a else .un .trunc .W32 a
  | w, a => .un .trunc w a

/-- The value and literal, if the value is a 64-bit sum with a literal; a label is one plus `0`. -/
def asAddLit : Sym → Option (Sym × Nat)
  | .bin .add .W64 x (.lit c) => some (x, c)
  | .label l => some (.label l, 0)
  | _ => none

/-- `x` plus the literal `d`, a region pointer if `x` is one. -/
def addLit (x : Sym) (d : Nat) : Sym :=
  match x.asPtr with
  | some (r, o) => .ptr r (o + litInt d)
  | none => .bin .add .W64 x (.lit d)

/-- A 64-bit sum. A sum with literals keeps one literal, last: `x + lit c`; a conditional plus a
literal is the conditional of the sums. -/
def mkAdd64 (a b : Sym) : Sym :=
  match a.asPtr, b.asLit with
  | some (r, o), some c => .ptr r (o + litInt c)
  | _, _ =>
    match a.asLit, b.asPtr with
    | some c, some (r, o) => .ptr r (o + litInt c)
    | _, _ =>
      if b = .lit 0 then a else if a = .lit 0 then b else
      match a.asLit, b.asLit with
      | some x, some y => .lit ((x + y) % 2 ^ 64)
      | _, _ =>
        match a.asAddLit, b.asLit with
        | some (x, c), some c' => .bin .add .W64 x (.lit ((c + c') % 2 ^ 64))
        | _, _ =>
          match a.asLit, b.asAddLit with
          | some c, some (x, c') => .bin .add .W64 x (.lit ((c + c') % 2 ^ 64))
          | _, _ =>
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
      if b = .lit 0 then a else
      match a.asLit, b.asLit with
      | some x, some y => .lit ((x + (2 ^ 64 - y % 2 ^ 64)) % 2 ^ 64)
      | _, _ => .bin .sub .W64 a b

/-- A unary operation. -/
def mkUn (op : UnOp) (w : Width) (a : Sym) : Sym :=
  match a.asLit with
  | some x => .lit (op.apply w (BitVec.ofNat 64 x)).toNat
  | none =>
    match op with
    | .trunc => truncTo w a
    | .bytes 0 8 => a
    | op => .un op w a

/-- A binary operation. -/
def mkBin (op : BinOp) (w : Width) (a b : Sym) : Sym :=
  match a.asLit, b.asLit with
  | some x, some y => .lit (op.apply w (BitVec.ofNat 64 x) (BitVec.ofNat 64 y)).toNat
  | _, _ =>
    match op, w with
    | .add, .W64 => mkAdd64 a b
    | .sub, .W64 => mkSub64 a b
    | .or, w => if a = .lit 0 then truncTo w b else if b = .lit 0 then truncTo w a
      else .bin .or w a b
    | .xor, w => if a = b then .lit 0 else if b = .lit 0 then truncTo w a else .bin .xor w a b
    | .mul, w => if b = .lit 1 then truncTo w a else .bin .mul w a b
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
def mkCmp (op : CmpOp) (w : Width) (a b : Sym) : SBool :=
  match a.asLit, b.asLit with
  | some x, some y => .lit (op.apply w (BitVec.ofNat 64 x) (BitVec.ofNat 64 y))
  | _, _ =>
    match op, w, a.asPtr, b.asPtr with
    | .eq, .W64, some (r, o), some (r', o') =>
      if r = r' then .lit (BitVec.ofInt 64 o == BitVec.ofInt 64 o') else .cmp op w a b
    | _, _, _, _ => .cmp op w a b

/-- The most significant bit. -/
def mkMsb (w : Width) (a : Sym) : SBool :=
  match a.asLit with
  | some x => .lit (low w (BitVec.ofNat 64 x)).msb
  | none => .msb w a

/-! ## Flags -/

/-- No flag known. -/
def unknownFlags : SFlags := ⟨none, none, none, none⟩

/-- ZF and SF of a result, with CF and OF given. -/
def resultFlags (w : Width) (r : Sym) (cf of : Option SBool) : SFlags :=
  ⟨cf, some (mkCmp .eq w r (.lit 0)), some (mkMsb w r), of⟩

/-- The flags of `a + b` (`ADD`). -/
def addFlags (w : Width) (a b : Sym) : SFlags :=
  resultFlags w (mkBin .add w a b) (some (mkCmp .addC w a b)) (some (mkCmp .addV w a b))

/-- The flags of `a - b` (`SUB`, `CMP`): the carry an unsigned comparison, ZF an equality. -/
def subFlags (w : Width) (a b : Sym) : SFlags :=
  ⟨some (mkCmp .ult w a b), some (mkCmp .eq w a b), some (mkMsb w (mkBin .sub w a b)),
    some (mkCmp .subV w a b)⟩

/-- The flags of a logical result (`AND`, `OR`, `XOR`, `TEST`). -/
def logicFlags (w : Width) (r : Sym) : SFlags :=
  resultFlags w r (some (.lit false)) (some (.lit false))

/-- CF after a shift `op` (`SHL`, `SHR`, `SAR`) of `a` by a masked count `k`, `0 < k < w.bits`:
the last bit shifted out, as the MSB of `a` shifted left (by `k - 1` for `SHL`, else by
`w.bits - k`). -/
def shiftCF (op : BinOp) (w : Width) (a : Sym) (k : Nat) : Option SBool :=
  if k < w.bits then
    match op with
    | .shl => some (.msb w (.bin .shl w a (.lit (k - 1))))
    | .shr | .sar => some (.msb w (.bin .shl w a (.lit (w.bits - k))))
    | _ => none
  else none

/-- The flags after a shift `op` (`rot` false) or rotation (`rot` true) of width `w` of `a` with
result `v` and count `n`, from the flags `f`: a literal count of zero keeps them; a nonzero one
sets ZF and SF of a shift, CF by `shiftCF`, and keeps them for a rotation, CF unknown; OF
unknown; a count in a register makes them unknown. -/
def shiftFlags (f : SFlags) (op : BinOp) (rot : Bool) (w : Width) (a v n : Sym) : SFlags :=
  match n.asLit with
  | some k =>
    if shiftCount w (BitVec.ofNat 64 k) == 0 then f
    else if rot then { f with cf := none, of := none }
    else resultFlags w v (shiftCF op w a (shiftCount w (BitVec.ofNat 64 k))) none
  | none => unknownFlags

/-- A condition code on symbolic flags (`CondCode.interp`), if the flags it reads are known; the
parity conditions are not followed. -/
def condSym (cc : CondCode) (f : SFlags) : Option SBool :=
  match cc with
  | .o => f.of
  | .no => f.of.map mkNot
  | .c => f.cf
  | .nc => f.cf.map mkNot
  | .z => f.zf
  | .nz => f.zf.map mkNot
  | .be => do let c ← f.cf; let z ← f.zf; some (mkOr c z)
  | .a => do let c ← f.cf; let z ← f.zf; some (mkAnd (mkNot c) (mkNot z))
  | .s => f.sf
  | .ns => f.sf.map mkNot
  | .p => none
  | .np => none
  | .l => do let s ← f.sf; let o ← f.of; some (mkNot (mkBeq s o))
  | .ge => do let s ← f.sf; let o ← f.of; some (mkBeq s o)
  | .le => do let s ← f.sf; let o ← f.of; let z ← f.zf; some (mkOr (mkNot (mkBeq s o)) z)
  | .g => do let s ← f.sf; let o ← f.of; let z ← f.zf; some (mkAnd (mkNot z) (mkBeq s o))

/-! ## Registers -/

namespace SState

/-- Register `r` set to `v`. -/
def setReg (S : SState) (r : Reg64) (v : Option Sym) : SState :=
  { S with regs := S.regs.set r.idx v }

/-- The flags set. -/
def setFlags (S : SState) (f : SFlags) : SState := { S with flags := f }

/-- A register operand; its full 64-bit value. The high byte registers are not followed. -/
def getR (S : SState) {w : Width} : Reg w → Option Sym
  | .low r _ => S.reg r
  | _ => none

/-- A write of width `w` to a register of a value already zero-extended: the whole register at 32
and 64 bits, its low bits at 8 and 16 bits. -/
def setR (S : SState) {w : Width} (r : Reg w) (u : Sym) : Option SState :=
  match r with
  | .low r w =>
    match w with
    | .W64 | .W32 => some (S.setReg r (some u))
    | w => some (S.setReg r ((S.reg r).map fun old => mkBin .merge w old u))
  | _ => none

end SState

/-! ## Memory -/

/-- An immediate. -/
def constInt : ConstExpr → Option Int64
  | .int64 k => some k
  | _ => none

/-- A position-independent symbolic constant; GOT slots remain symbolic addresses. -/
def constSym : ConstExpr → Option Sym
  | .int64 k => some (.lit k.toBitVec.toNat)
  | .label l => some (.label l)
  | .gotSlot l => some (.gotSlot l)
  | _ => none

/-- Only a value known to be a label can be an indirect control target. -/
def asLabel : Sym → Option Label
  | .label l => some l
  | _ => none

/-- A jump target, `l - .` relative to the address after the instruction. -/
def relTarget : RelRegOrMem → Option Label
  | .rel (.sub (.label l) .after_current_instruction) => some l
  | _ => none

namespace SState

/-- The base register of an address, `0` if none; RIP is not a base here. -/
def baseSym (S : SState) : Option RegOrRip → Option Sym
  | none => some (.lit 0)
  | some (.reg r) => S.reg r
  | some .rip => none

/-- The scaled index of an address, `0` if none. -/
def indexSym (S : SState) : Option AddrIndex → Option Sym
  | none => some (.lit 0)
  | some ⟨r, sc⟩ => (S.reg r).map fun v => mkBin .mul .W64 v (.lit sc.bytes)

/-- An address operand (`AddrExpr.interp`, 64-bit addresses): a RIP-relative label, or a base
register plus a scaled index plus a constant (summed in that order, the constant last). -/
def addr (S : SState) (a : AddrExpr) : Option Sym :=
  match a.disp with
  | .sub (.label l) .after_current_instruction =>
    match a.base, a.idx with
    | some .rip, none => some (.label l)
    | _, _ => none
  | .sub (.gotSlot l) .after_current_instruction =>
    match a.base, a.idx with
    | some .rip, none => some (.gotSlot l)
    | _, _ => none
  | c => do
    let d ← constSym c
    let b ← S.baseSym a.base
    let i ← S.indexSym a.idx
    some (mkAdd64 (mkAdd64 b i) d)

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
    match a with
    | .bin .add .W64 x (.lit c) => (S.basePtr x).map fun ro => (ro.1, ro.2 + litInt c)
    | _ => none

/-- The region and offset of an access of `n` bytes at `a`, if `a` points into a known region and
the access is within it. -/
def access (S : SState) (a : Sym) (n : Nat) : Option (Nat × Nat) :=
  match S.toPtr a with
  | some (r, o) =>
    match S.regions[r]? with
    | some sz => if 0 ≤ o ∧ o.toNat + n ≤ sz then some (r, o.toNat) else none
    | none => none
  | none => none

/-- The largest value an index can have by the bounds: a value `x` with a bound `(x, B)`,
possibly scaled (`x * s`, an index register of an address). -/
def idxMax (S : SState) : Sym → Option Nat
  | .bin .mul .W64 x (.lit s) => (S.bounds.lookup x).map fun B => (B - 1) * s
  | x => (S.bounds.lookup x).map fun B => B - 1

/-- An indexed access of `n` bytes at `p + i + d`: the region, offset, index and index bound. -/
def accessIdxAt (S : SState) (p i : Sym) (d : Int) (n : Nat) : Option (Nat × Nat × Sym × Nat) :=
  match S.toPtr p, S.idxMax i with
  | some (r, o), some M =>
    match S.regions[r]? with
    | some sz => if 0 ≤ o + d ∧ (o + d).toNat + M + n ≤ sz then some (r, (o + d).toNat, i, M)
      else none
    | none => none
  | _, _ => none

/-- An indexed access of `n` bytes at `x + y + d`, either of `x`, `y` the pointer. -/
def accessIdx2 (S : SState) (x y : Sym) (d : Int) (n : Nat) : Option (Nat × Nat × Sym × Nat) :=
  match S.accessIdxAt x y d n with
  | some res => some res
  | none => S.accessIdxAt y x d n

/-- The region, offset, index and index bound of an indexed access of `n` bytes at `a` (a pointer
into a known region plus an index with a bound, possibly plus a literal), if the access is within
the region for every value of the index. -/
def accessIdx (S : SState) (a : Sym) (n : Nat) : Option (Nat × Nat × Sym × Nat) :=
  match a with
  | .bin .add .W64 (.bin .add .W64 x y) (.lit c) => S.accessIdx2 x y (litInt c) n
  | .bin .add .W64 x y => S.accessIdx2 x y 0 n
  | _ => none

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
  | o, n + 1 =>
    mkBin .add .W64 (byteSym ws r o) (mkBin .shl .W64 (assemble ws r (o + 1) n) (.lit 8))

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

/-- An index as a value times a scale: `x * s` (a scaled index register, a multiplication by a
constant), `x << j` (a shift by a constant below 64), else the index itself at scale `1`. -/
def idxScale : Sym → Sym × Nat
  | .bin .mul .W64 x (.lit s) => (x, s)
  | .bin .shl .W64 x (.lit j) => if j < 64 then (x, 2 ^ j) else (.bin .shl .W64 x (.lit j), 1)
  | x => (x, 1)

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
value `x`, the scale `s` and the bound `B`, `i = s * x` (`idxScale`), `0 < n ≤ s`, every slot in
the region. -/
def slotsAt (S : SState) (p i : Sym) (d : Int) (n : Nat) :
    Option (Nat × Nat × Sym × Nat × Nat) :=
  match S.toPtr p, S.bounds.lookup (idxScale i).1 with
  | some (r, o), some B =>
    match S.regions[r]? with
    | some sz =>
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

/-- An indexed access of `n` bytes at `a` as slots (`slotsAt`): a pointer plus an index, possibly
plus a literal. -/
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

/-- Record symbolic initial bytes without adding a write to the block's footprint.
`Match.withKnownBytes` proves their contents in `env.mem0`; actual stores take precedence. -/
def withKnownBytes (S : SState) (r off n : Nat) (v : Sym) : SState :=
  { S with known := ⟨r, off, n, v⟩ :: S.known }

/-- The writes with `v`'s low `n` bytes at `o` in region `r`, dropping the writes it covers. -/
def store (S : SState) (r o n : Nat) (v : Sym) : SState :=
  { S with
    mem := ⟨r, o, n, v⟩ :: S.mem.filter fun w => !(w.r = r ∧ o ≤ w.off ∧ w.off + w.n ≤ o + n) }

/-- A load of `n` bytes at `a`: at a constant offset in a region, at an indexed offset in a
region where no write overlaps the bytes the index can reach, else over the slots of an index
with a bound (`loadSlots`). -/
def loadOne (S : SState) (a : Sym) (n : Nat) : Option Sym :=
  match S.access a n with
  | some (r, o) => some (loadSym (S.mem ++ S.known) r o n)
  | none =>
    match S.accessIdx a n with
    | some (r, o, i, M) =>
      if S.mem.all (fun w => w.r != r || w.off + w.n ≤ o || o + M + n ≤ w.off) then
        some (.loadx r o i n)
      else S.loadSlots a n
    | none => S.loadSlots a n

/-- A load of `n` bytes at `a` (`loadOne`); at a conditional address, the conditional of the
loads at its branches. -/
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

/-- A register or memory operand of width `w` (`RegOrMem.interp`); its low `w` bits are the
value. -/
def readRM (S : SState) {w : Width} : RegOrMem w → Option Sym
  | .reg r => S.getR r
  | .mem a => do
    let x ← S.addr a
    S.loadAt x w.bytes

/-- An operand of width `w` (`Operand.interp`); its low `w` bits are the value. -/
def readOp (S : SState) {w : Width} : Operand w → Option Sym
  | .regOrMem o => S.readRM o
  | .imm c => constSym c

/-- A write of width `w` of a value already zero-extended to a destination (`MachineData.set`). -/
def writeDst (S : SState) {w : Width} (d : Dst w) (u : Sym) : Option SState :=
  match d with
  | .reg r => S.setR r u
  | .mem a => do
    let x ← S.addr a
    S.storeAt x w.bytes u

/-- A shift count (`ShiftCountExpr.interp`); its low byte is the count. -/
def count (S : SState) : ShiftCountExpr → Option Sym
  | .cl => S.reg .rcx
  | .imm8 c => do
    let k ← constInt c
    some (.lit k.toBitVec.toNat)

/-- Bit offsets use the full operand-width register, but only the immediate's low byte. -/
def bitOffset (S : SState) {w : Width} : BitOffset w → Option Sym
  | .reg r => S.getR r
  | .imm c => (constSym c).map (truncTo .W8)

/-- Resolve direct and indirect control targets without guessing concrete addresses. -/
def target (S : SState) : RelRegOrMem → Option Label
  | .rel c => relTarget (.rel c)
  | .reg r => do
    let v ← S.getR r
    asLabel v
  | .mem a => do
    let v ← S.readRM (.mem a : RegOrMem .W64)
    asLabel v

end SState

/-! ## Instructions -/

/-- The result of a step that falls through. -/
abbrev fall (S : SState) : Option (SState × Exit) := some (S, .fall)

namespace Step
variable {w : Width}

/-- `MOV dst, src`. -/
def mov (dst : Dst w) (src : Operand w) (S : SState) : Option (SState × Exit) := do
  let v ← S.readOp src
  let S' ← S.writeDst dst (truncTo w v)
  fall S'

/-- `MOVZX`/`MOVSX dst, src` with `op` the extension. -/
def movx (op : UnOp) {w' : Width} (dst : Dst w) (src : RegOrMem w') (S : SState) :
    Option (SState × Exit) := do
  let v ← S.readRM src
  let S' ← S.writeDst dst (mkUn op w v)
  fall S'

/-- `LEA dst, a`. -/
def lea (dst : Reg w) (a : AddrExpr) (S : SState) : Option (SState × Exit) := do
  let x ← S.addr a
  let S' ← S.setR dst (truncTo w x)
  fall S'

/-- `PUSH src`. -/
def push (src : Operand w) (S : SState) : Option (SState × Exit) := do
  let v ← S.readOp src
  let sp ← S.reg .rsp
  let sp' := mkSub64 sp (.lit w.bytes)
  let S' ← (S.setReg .rsp (some sp')).storeAt sp' w.bytes v
  fall S'

/-- `POP dst`. -/
def pop (dst : Dst w) (S : SState) : Option (SState × Exit) := do
  let sp ← S.reg .rsp
  let v ← S.loadAt sp w.bytes
  let S' ← (S.setReg .rsp (some (mkAdd64 sp (.lit w.bytes)))).writeDst dst v
  fall S'

/-- `SETcc dst`. -/
def setcc (cc : CondCode) (dst : Dst w) (S : SState) : Option (SState × Exit) := do
  let c ← condSym cc S.flags
  let S' ← S.writeDst dst (mkIte c (.lit 1) (.lit 0))
  fall S'

/-- `CMOVcc dst, src`. -/
def cmovcc (cc : CondCode) (dst : Reg w) (src : RegOrMem w) (S : SState) :
    Option (SState × Exit) := do
  let v ← S.readRM src
  let c ← condSym cc S.flags
  let old ← S.getR dst
  let S' ← S.setR dst (mkIte c (truncTo w v) (truncTo w old))
  fall S'

/-- `ADD dst, src`. -/
def add (dst : Dst w) (src : Operand w) (S : SState) : Option (SState × Exit) := do
  let a ← S.readOp src
  let b ← S.readRM dst
  let S' ← (S.setFlags (addFlags w a b)).writeDst dst (mkBin .add w a b)
  fall S'

/-- `SUB dst, src`. -/
def sub (dst : Dst w) (src : Operand w) (S : SState) : Option (SState × Exit) := do
  let a ← S.readOp src
  let b ← S.readRM dst
  let S' ← (S.setFlags (subFlags w b a)).writeDst dst (mkBin .sub w b a)
  fall S'

/-- `AND`/`OR`/`XOR dst, src`. -/
def logic (op : BinOp) (dst : Dst w) (src : Operand w) (S : SState) : Option (SState × Exit) := do
  let a ← S.readRM dst
  let b ← S.readOp src
  let v := mkBin op w a b
  let S' ← (S.setFlags (logicFlags w v)).writeDst dst v
  fall S'

/-- `CMP a, b`. -/
def cmp (a : RegOrMem w) (b : Operand w) (S : SState) : Option (SState × Exit) := do
  let x ← S.readRM a
  let y ← S.readOp b
  fall (S.setFlags (subFlags w x y))

/-- `TEST a, b`. -/
def test (a : RegOrMem w) (b : Operand w) (S : SState) : Option (SState × Exit) := do
  let x ← S.readRM a
  let y ← S.readOp b
  fall (S.setFlags (logicFlags w (mkBin .and w x y)))


/-- `BT`: CF is the selected bit, ZF is preserved, all other tracked flags are unknown. -/
def bt (base : Reg w) (offset : BitOffset w) (S : SState) : Option (SState × Exit) :=
  if w == .W8 then none else do
    let a ← S.getR base
    let b ← S.bitOffset offset
    fall (S.setFlags ⟨some (mkCmp .bit w a b), S.flags.zf, none, none⟩)

/-- `BTS` has `BT`'s flags and sets the selected bit in the base register. -/
def bts (base : Reg w) (offset : BitOffset w) (S : SState) : Option (SState × Exit) :=
  if w == .W8 then none else do
    let a ← S.getR base
    let b ← S.bitOffset offset
    let S' ← (S.setFlags ⟨some (mkCmp .bit w a b), S.flags.zf, none, none⟩).setR base
      (mkBin .bts w a b)
    fall S'

/-- `INC dst`. -/
def inc (dst : RegOrMem w) (S : SState) : Option (SState × Exit) := do
  let a ← S.readRM dst
  let v := mkBin .add w a (.lit 1)
  let S' ← (S.setFlags (resultFlags w v S.flags.cf (some (mkCmp .incV w a a)))).writeDst dst v
  fall S'

/-- `DEC dst`. -/
def dec (dst : RegOrMem w) (S : SState) : Option (SState × Exit) := do
  let a ← S.readRM dst
  let v := mkBin .sub w a (.lit 1)
  let S' ← (S.setFlags (resultFlags w v S.flags.cf (some (mkCmp .decV w a a)))).writeDst dst v
  fall S'

/-- `NEG dst`. -/
def neg (dst : RegOrMem w) (S : SState) : Option (SState × Exit) := do
  let a ← S.readRM dst
  let v := mkUn .neg w a
  let S' ← (S.setFlags (resultFlags w v (some (mkNot (mkCmp .eq w a (.lit 0))))
    (some (mkCmp .negV w a a)))).writeDst dst v
  fall S'

/-- `NOT dst`. -/
def not (dst : Dst w) (S : SState) : Option (SState × Exit) := do
  let a ← S.readRM dst
  let S' ← S.writeDst dst (mkUn .not w a)
  fall S'

/-- `IMUL` with two or three operands; its flags unknown. -/
def imul (dst : Option (Dst w)) (src1 : RegOrMem w) (src2 : Operand w) (S : SState) :
    Option (SState × Exit) := do
  let a ← S.readRM src1
  let b ← S.readOp src2
  let S' ← S.writeDst (dst.getD src1) (mkBin .mul w a b)
  fall (S'.setFlags unknownFlags)

/-- One-operand `MUL src` at a width other than 8 bits (`mul`): RDX:RAX the product of RAX and
`src`; CF and OF whether the high half is nonzero, the other flags unknown. -/
def mulW (src : RegOrMem w) (S : SState) : Option (SState × Exit) := do
  let a ← S.getR (.low .rax w)
  let b ← S.readRM src
  let S₁ ← S.setR (.low .rax w) (mkBin .mul w a b)
  let S₂ ← S₁.setR (.low .rdx w) (mkBin .mulhi w a b)
  let c := mkCmp .mulC w a b
  fall (S₂.setFlags ⟨some c, none, none, some c⟩)

/-- One-operand `MUL src`; not at 8 bits (which writes AX). -/
def mul (src : RegOrMem w) (S : SState) : Option (SState × Exit) :=
  match w with
  | .W8 => none
  | _ => mulW src S

/-- The carry flag as a value, `1` or `0`. -/
def carryBit (c : SBool) : Sym := mkIte c (.lit 1) (.lit 0)

/-- `ADC dst, src`, with the carry flag known. -/
def adc (dst : Dst w) (src : Operand w) (S : SState) : Option (SState × Exit) := do
  let a ← S.readOp src
  let b ← S.readRM dst
  let c ← S.flags.cf
  let v := mkBin .add w (mkBin .add w a b) (carryBit c)
  let S' ← (S.setFlags (resultFlags w v (some (mkIteB c (mkCmp (.adcC true) w a b)
    (mkCmp (.adcC false) w a b))) (some (mkIteB c (mkCmp (.adcV true) w a b)
    (mkCmp (.adcV false) w a b))))).writeDst dst v
  fall S'

/-- `SBB dst, src`, with the carry flag known. -/
def sbb (dst : Dst w) (src : Operand w) (S : SState) : Option (SState × Exit) := do
  let a ← S.readOp src
  let b ← S.readRM dst
  let c ← S.flags.cf
  let v := mkBin .sub w (mkBin .sub w b a) (carryBit c)
  let S' ← (S.setFlags (resultFlags w v (some (mkIteB c (mkCmp (.sbbC true) w b a)
    (mkCmp (.sbbC false) w b a))) (some (mkIteB c (mkCmp (.sbbV true) w b a)
    (mkCmp (.sbbV false) w b a))))).writeDst dst v
  fall S'

/-- A shift or rotation `op dst, count`; its flags `shiftFlags`. -/
def shift (op : BinOp) (rot : Bool) (dst : Dst w) (c : ShiftCountExpr) (S : SState) :
    Option (SState × Exit) := do
  let a ← S.readRM dst
  let n ← S.count c
  let v := mkBin op w a n
  let S' ← (S.setFlags (shiftFlags S.flags op rot w a v n)).writeDst dst v
  fall S'

/-- `SHLD`/`SHRD dst, src, count` at 32 or 64 bits; the flags unknown. -/
def shiftD (op : TernOp) (dst : Dst w) (src : Reg w) (c : ShiftCountExpr) (S : SState) :
    Option (SState × Exit) :=
  match w with
  | .W32 | .W64 => do
    let a ← S.readRM dst
    let b ← S.getR src
    let n ← S.count c
    let S' ← (S.setFlags unknownFlags).writeDst dst (.tern op w a b n)
    fall S'
  | _ => none

/-- `BSWAP dst` at 32 or 64 bits. -/
def bswap (dst : Reg w) (S : SState) : Option (SState × Exit) :=
  match w with
  | .W32 | .W64 => do
    let a ← S.getR dst
    let S' ← S.setR dst (mkUn .bswap w a)
    fall S'
  | _ => none

/-- `CALL`: resolve the target before pushing the return address (`Sym.retAddr`). -/
def call (t : RelRegOrMem) (S : SState) : Option (SState × Exit) := do
  let l ← S.target t
  let sp ← S.reg .rsp
  let sp' := mkSub64 sp (.lit 8)
  let S' ← (S.setReg .rsp (some sp')).storeAt sp' 8 .retAddr
  some (S', .call l)

/-- `RET`: to the address popped. -/
def ret (S : SState) : Option (SState × Exit) := do
  let sp ← S.reg .rsp
  let a ← S.loadAt sp 8
  some (S.setReg .rsp (some (mkAdd64 sp (.lit 8))), .ret a)

end Step

/-- One instruction's symbolic step (64-bit addresses). -/
def stepOp : {w : Width} → Operation w → SState → Option (SState × Exit)
  | _, .mov dst src, S => Step.mov dst src S
  | _, .movzx (w' := w') dst src, S => Step.movx (.zext w') dst src S
  | _, .movsx (w' := w') dst src, S => Step.movx (.sext w') dst src S
  | _, .push src, S => Step.push src S
  | _, .pop dst, S => Step.pop dst S
  | _, .setcc cc dst, S => Step.setcc cc dst S
  | _, .cmovcc cc dst src, S => Step.cmovcc cc dst src S
  | _, .lea dst a, S => Step.lea dst a S
  | _, .add dst src, S => Step.add dst src S
  | _, .sub dst src, S => Step.sub dst src S
  | _, .adc dst src, S => Step.adc dst src S
  | _, .sbb dst src, S => Step.sbb dst src S
  | _, .and dst src, S => Step.logic .and dst src S
  | _, .or dst src, S => Step.logic .or dst src S
  | _, .xor dst src, S => Step.logic .xor dst src S
  | _, .cmp a b, S => Step.cmp a b S
  | _, .test a b, S => Step.test a b S
  | _, .bt base offset, S => Step.bt base offset S
  | _, .bts base offset, S => Step.bts base offset S
  | _, .inc dst, S => Step.inc dst S
  | _, .dec dst, S => Step.dec dst S
  | _, .neg dst, S => Step.neg dst S
  | _, .not dst, S => Step.not dst S
  | _, .imul dst src1 src2, S => Step.imul dst src1 src2 S
  | _, .mul src, S => Step.mul src S
  | _, .shl dst c, S => Step.shift .shl false dst c S
  | _, .shr dst c, S => Step.shift .shr false dst c S
  | _, .sar dst c, S => Step.shift .sar false dst c S
  | _, .rol dst c, S => Step.shift .rol true dst c S
  | _, .ror dst c, S => Step.shift .ror true dst c S
  | _, .shld dst src c, S => Step.shiftD .shld dst src c S
  | _, .shrd dst src c, S => Step.shiftD .shrd dst src c S
  | _, .bswap dst, S => Step.bswap dst S
  | _, .jcc cc l, S => do
    let c ← condSym cc S.flags
    some (S, .cond c l)
  | _, .jmp t, S => do
    let l ← S.target t
    some (S, .jump l)
  | _, .call t, S => Step.call t S
  | _, .ret, S => Step.ret S
  | _, .nop _, S => fall S
  | _, .nopalign _ _, S => fall S
  | _, _, _ => none

/-- One directive's symbolic step: a label is a no-op, data is not code, only 64-bit addresses. -/
def stepD : Directive → SState → Option (SState × Exit)
  | .label _, S => some (S, .fall)
  | .instr (.regular .W64 _ op), S => stepOp op S
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

end NativeRustcX64
