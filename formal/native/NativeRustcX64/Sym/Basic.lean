module

public import NativeRustcX64.Basic
public import NativeRustcX64.Sym.State

/-!
# Symbolic states of Kraken's x86-64 machine

The symbolic executor (`NativeRustcX64.Sym.exec`) runs a basic block on a symbolic state
`Sym.SState`: each register a symbolic value `Sym` over the atoms of an environment `Sym.Env` (the
registers, flags and memory at some earlier point, the base addresses of the memory regions, the
labels' addresses, the return address of a call, further variables), the flags symbolic booleans
`SBool`, memory the list of the symbolic writes into the regions, newest first.
`Sym.Match env S m`: the machine state `m` is what `S` describes in `env`. An operation of width
`w` computes on the low `w` bits of its operands and zero-extends its result (`Sym.low`, `Sym.ext`).
Initial-memory descriptions (`SState.known`) are separately justified against `env.mem0`; they
name values loaded from unwritten bytes without enlarging the block's write footprint.
-/

namespace NativeRustcX64

@[expose] public section

namespace Sym

/-- What the atoms of symbolic values stand for. -/
structure Env where
  regs : Reg64 → BitVec 64
  flags : StatusFlags
  /-- The memory symbolic loads of unwritten bytes read. -/
  mem0 : DataMem
  /-- Each region's base and size. -/
  regions : List (BitVec 64 × Nat)
  vars : Nat → BitVec 64 := fun _ => 0
  /-- The return address `call` pushes (`Sym.retAddr`). -/
  ret : BitVec 64 := 0

/-- The low `w.bits` bits of a 64-bit value, as Kraken reads a register of width `w`. -/
def low (w : Width) (x : BitVec 64) : w.type := x.setWidth w.bits

/-- A value of width `w` zero-extended. -/
def ext (w : Width) (v : w.type) : BitVec 64 := v.setWidth 64

/-- The byte `t` of a 64-bit value. -/
def byteOf (x : BitVec 64) (t : Nat) : UInt8 := UInt8.ofNat (x.toNat / 2 ^ (8 * t))

/-- The `n` bytes of a value from byte `t`. -/
def bytesOf (x : BitVec 64) (t n : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (x.toNat / 2 ^ (8 * t) % 2 ^ (8 * n))

/-- The mask of a shift count at width `w`. -/
def shiftMask : Width → Nat
  | .W64 => 0x3f
  | _ => 0x1f

/-- A shift count of width `w`, the low byte of `y`, masked (`ShiftCountExpr.interpMasked`). -/
def shiftCount (w : Width) (y : BitVec 64) : Nat := (low .W8 y).toNat &&& shiftMask w

/-- `BSWAP` of 32 bits, as Kraken computes it. -/
def bswap32 {n : Nat} (a : BitVec n) : BitVec n :=
  (a.take 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.drop 24).setWidth n

/-- `BSWAP` of 64 bits, as Kraken computes it. -/
def bswap64 {n : Nat} (a : BitVec n) : BitVec n :=
  (a.take 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8
    ++ a.extractLsb' 32 8 ++ a.extractLsb' 40 8 ++ a.extractLsb' 48 8 ++ a.drop 56).setWidth n

/-- Region `r`'s base. -/
def Env.base (env : Env) (r : Nat) : BitVec 64 := ((env.regions[r]?).map (·.1)).getD 0

/-- The `n` bytes of `env.mem0` at `off` in region `r`, little-endian. -/
def Env.load (env : Env) (r off n : Nat) : BitVec 64 :=
  BitVec.ofInt 64 (Int.ofBytes ((List.range n).map fun i =>
    (env.mem0.get? (env.base r + BitVec.ofNat 64 (off + i))).getD 0))

end Sym

open Sym

/-- A binary operation's value. -/
def BinOp.apply : BinOp → (w : Width) → BitVec 64 → BitVec 64 → BitVec 64
  | .add, w, x, y => ext w (low w x + low w y)
  | .sub, w, x, y => ext w (low w x - low w y)
  | .and, w, x, y => ext w (low w x &&& low w y)
  | .or, w, x, y => ext w (low w x ||| low w y)
  | .xor, w, x, y => ext w (low w x ^^^ low w y)
  | .mul, w, x, y => ext w (low w x * low w y)
  | .mulhi, w, x, y =>
    ext w (BitVec.ofInt w.bits (((low w x).unsigned * (low w y).unsigned) >>> w.bits))
  | .bts, w, x, y => ext w (low w x ||| ((1 : w.type) <<< ((low w y).toNat % w.bits)))
  | .shl, w, x, y => ext w (low w x <<< shiftCount w y)
  | .shr, w, x, y => ext w ((low w x).ushiftRight (shiftCount w y))
  | .sar, w, x, y => ext w ((low w x).sshiftRight (shiftCount w y))
  | .rol, w, x, y => ext w ((low w x).rotateLeft (shiftCount w y))
  | .ror, w, x, y => ext w ((low w x).rotateRight (shiftCount w y))
  | .merge, w, x, y => x.replaceLow (low w y)

/-- A double-precision shift's value: the destination when the count is zero. -/
def TernOp.apply : TernOp → (w : Width) → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64
  | .shld, w, x, y, z =>
    if shiftCount w z == 0 then ext w (low w x)
    else ext w (((((low w x).append (low w y)) <<< shiftCount w z).drop w.bits).setWidth w.bits)
  | .shrd, w, x, y, z =>
    if shiftCount w z == 0 then ext w (low w x)
    else ext w (((((low w y).append (low w x)) >>> shiftCount w z).take w.bits).setWidth w.bits)

/-- `BSWAP` of width `w`; the identity at a width it does not have. -/
def bswapW : (w : Width) → BitVec 64 → BitVec 64
  | .W32, x => ext .W32 (bswap32 (low .W32 x))
  | .W64, x => ext .W64 (bswap64 (low .W64 x))
  | _, x => x

/-- A unary operation's value. -/
def UnOp.apply : UnOp → (w : Width) → BitVec 64 → BitVec 64
  | .trunc, w, x => ext w (low w x)
  | .not, w, x => ext w (~~~low w x)
  | .neg, w, x => ext w (-low w x)
  | .bswap, w, x => bswapW w x
  | .zext w', w, x => ext w ((low w' x).zeroExtend w.bits)
  | .sext w', w, x => ext w ((low w' x).signExtend w.bits)
  | .bytes t n, _, x => bytesOf x t n

/-- A comparison's value. -/
def CmpOp.apply : CmpOp → (w : Width) → BitVec 64 → BitVec 64 → Bool
  | .eq, w, x, y => low w x == low w y
  | .ult, w, x, y => (low w x).ult (low w y)
  | .addC, w, x, y => (low w x + low w y).unsigned != (low w x).unsigned + (low w y).unsigned
  | .addV, w, x, y => (low w x + low w y).signed != (low w x).signed + (low w y).signed
  | .subV, w, x, y => (low w x - low w y).signed != (low w x).signed - (low w y).signed
  | .incV, w, x, _ => (low w x + 1).signed != (low w x).signed + 1
  | .decV, w, x, _ => (low w x - 1).signed != (low w x).signed - 1
  | .negV, w, x, _ => (-low w x).signed != -(low w x).signed
  | .mulC, w, x, y => (low w x * low w y).unsigned != (low w x).unsigned * (low w y).unsigned
  | .bit, w, x, y => (low w x).getLsbD ((low w y).toNat % w.bits)
  | .adcC c, w, x, y => (low w x + low w y + (c : w.type)).unsigned !=
    (low w x).unsigned + (low w y).unsigned + (c : Nat)
  | .adcV c, w, x, y => (low w x + low w y + (c : w.type)).signed !=
    (low w x).signed + (low w y).signed + (c : Nat)
  | .sbbC c, w, x, y => (low w x - low w y - (c : w.type)).unsigned !=
    (low w x).unsigned - (low w y).unsigned - (c : Nat)
  | .sbbV c, w, x, y => (low w x - low w y - (c : w.type)).signed !=
    (low w x).signed - (low w y).signed - (c : Nat)

variable [Labels]

mutual

/-- A symbolic value's value in an environment. -/
def Sym.eval (env : Env) : Sym → BitVec 64
  | .lit n => BitVec.ofNat 64 n
  | .reg r => env.regs r
  | .var i => env.vars i
  | .ptr r off => env.base r + BitVec.ofInt 64 off
  | .label l => (Labels.label l).toBitVec
  | .gotSlot l => (Labels.gotSlot l).toBitVec
  | .load r off n => env.load r off n
  | .loadx r off idx n => env.load r (off + (idx.eval env).toNat) n
  | .retAddr => env.ret
  | .bin op w a b => op.apply w (a.eval env) (b.eval env)
  | .un op w a => op.apply w (a.eval env)
  | .tern op w a b c => op.apply w (a.eval env) (b.eval env) (c.eval env)
  | .ite c a b => if c.eval env then a.eval env else b.eval env

/-- A symbolic boolean's value in an environment. -/
def SBool.eval (env : Env) : SBool → Bool
  | .lit b => b
  | .not b => !b.eval env
  | .and b c => b.eval env && c.eval env
  | .or b c => b.eval env || c.eval env
  | .beq b c => b.eval env == c.eval env
  | .ite c a b => if c.eval env then a.eval env else b.eval env
  | .cmp op w a b => op.apply w (a.eval env) (b.eval env)
  | .msb w a => (low w (a.eval env)).msb
  | .flagCF => env.flags.cf
  | .flagZF => env.flags.zf
  | .flagSF => env.flags.sf
  | .flagOF => env.flags.of

end

-- The equation lemmas of the evaluation functions, generated here once rather than in each
-- importer that unfolds them.
attribute [local simp] BinOp.apply TernOp.apply UnOp.apply CmpOp.apply Sym.eval SBool.eval

namespace Sym

/-- 64-bit addresses, the only address size the executor follows. -/
scoped instance instAddressSize64 : AddressSize := ⟨.W64⟩

/-- The known symbolic flags are the flags' values. -/
def FlagsOk (env : Env) (f : SFlags) (st : StatusFlags) : Prop :=
  (∀ b, f.cf = some b → st.cf = b.eval env) ∧ (∀ b, f.zf = some b → st.zf = b.eval env) ∧
    (∀ b, f.sf = some b → st.sf = b.eval env) ∧ (∀ b, f.of = some b → st.of = b.eval env)

/-- The index of a register among RAX to R15. -/
def _root_.Reg64.idx : Reg64 → Nat
  | .rax => 0 | .rbx => 1 | .rcx => 2 | .rdx => 3 | .rsi => 4 | .rdi => 5 | .rsp => 6
  | .rbp => 7 | .r8 => 8 | .r9 => 9 | .r10 => 10 | .r11 => 11 | .r12 => 12 | .r13 => 13
  | .r14 => 14 | .r15 => 15

/-- RAX to R15. -/
def allRegs : List Reg64 :=
  [.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .rsp, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- The symbolic value of a register, if known. -/
def SState.reg (S : SState) (r : Reg64) : Option Sym := (S.regs[r.idx]?).getD none

/-- The newest write covering byte `i` of region `r`: its value and the byte's index in it. -/
def findWrite (r i : Nat) : List Write → Option (Sym × Nat)
  | [] => none
  | w :: ws => if w.r = r ∧ w.off ≤ i ∧ i < w.off + w.n then some (w.v, i - w.off)
    else findWrite r i ws

/-- The byte at `i` in region `r` (base `b`) that the writes `ws` over `env.mem0` give. -/
def memByte (env : Env) (ws : List Write) (r : Nat) (b : BitVec 64) (i : Nat) : Option UInt8 :=
  match findWrite r i ws with
  | some (v, t) => some (byteOf (v.eval env) t)
  | none => env.mem0.get? (b + BitVec.ofNat 64 i)

/-- The address `a` is in none of the regions. -/
def Env.Outside (env : Env) (a : BitVec 64) : Prop :=
  ∀ (r : Nat) (b : BitVec 64) (n : Nat), env.regions[r]? = some (b, n) →
    ¬(b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + n)

/-- The regions do not wrap around, are mapped in `mem0` and are pairwise disjoint. -/
structure Env.WF (env : Env) : Prop where
  noWrap : ∀ (r : Nat) (b : BitVec 64) (n : Nat), env.regions[r]? = some (b, n) →
    b.toNat + n ≤ 2 ^ 64
  mapped : ∀ (r : Nat) (b : BitVec 64) (n : Nat), env.regions[r]? = some (b, n) → ∀ i < n,
    (env.mem0.get? (b + BitVec.ofNat 64 i)).isSome
  disjoint : ∀ (r r' : Nat) (b b' : BitVec 64) (n n' : Nat), r ≠ r' →
    env.regions[r]? = some (b, n) → env.regions[r']? = some (b', n') →
    b.toNat + n ≤ b'.toNat ∨ b'.toNat + n' ≤ b.toNat

/-- **The machine state `m` is what `S` describes in `env`.** Known registers and known flags are
their symbolic values; the regions are `env`'s, with the sizes `S` records; each byte of a region
is what the newest write covering it says, else `env.mem0`'s; the labels `S` places at regions'
bases are there; the bounds and aliases `S` records hold; memory outside the regions is
`env.mem0`'s. -/
structure Match (env : Env) (S : SState) (m : MachineData) : Prop where
  regs : ∀ r v, S.reg r = some v → m.regs.get64 r = v.eval env
  flags : FlagsOk env S.flags m.status
  regions : ∀ (r n : Nat), S.regions[r]? = some n → ∃ b : BitVec 64, env.regions[r]? = some (b, n)
  mem : ∀ (r : Nat) (b : BitVec 64) (n : Nat), env.regions[r]? = some (b, n) → ∀ i < n,
    m.dmem.get? (b + BitVec.ofNat 64 i) = memByte env S.mem r b i
  labels : ∀ l r, S.labels.lookup l = some r → env.base r = (Labels.label l).toBitVec
  bounds : ∀ x n, (x, n) ∈ S.bounds → (x.eval env).toNat < n
  aliases : ∀ x r o, S.aliases.lookup x = some (r, o) → x.eval env = env.base r + BitVec.ofInt 64 o
  outside : ∀ a, env.Outside a → m.dmem.get? a = env.mem0.get? a
  known : ∀ w ∈ S.known, ∀ i < w.n,
    env.mem0.get? (env.base w.r + BitVec.ofNat 64 (w.off + i)) =
      some (byteOf (w.v.eval env) i) := by
        first
        | intro w hw; cases hw
        | intro w hw i hi
          solve_by_elim [Match.known]

/-- Where a block's exit leaves the machine, `next` the address after the block. A call leaves the
return address at RSP (`retOf`); a return goes to the address it popped. -/
def PcOk (env : Env) (x : Exit) (next : Int64) (st : MachineState) : Prop :=
  match x with
  | .fall => st.pc = next
  | .jump l => st.pc = Labels.label l
  | .cond c l => st.pc = if c.eval env then Labels.label l else next
  | .call l => st.pc = Labels.label l ∧ retOf st.data = next
  | .ret a => st.pc = Int64.ofBitVec (a.eval env)

/-- The environment of a machine state: its registers, flags and memory, and the regions. -/
def Env.ofMachine (m : MachineData) (regions : List (BitVec 64 × Nat))
    (vars : Nat → BitVec 64 := fun _ => 0) (ret : BitVec 64 := 0) : Env where
  regs r := m.regs.get64 r
  flags := m.status
  mem0 := m.dmem
  regions := regions
  vars := vars
  ret := ret

/-- The symbolic state of an environment: each register its atom unless `known` gives it, the
flags their atoms, no writes, the regions `regions`, the labels at regions' bases `labels`, the
bounds `bounds` and the aliases `aliases`. -/
def init (regions : List Nat) (known : List (Reg64 × Sym) := [])
    (labels : List (Label × Nat) := []) (bounds : List (Sym × Nat) := [])
    (aliases : List (Sym × Nat × Int) := []) : SState where
  regs := allRegs.map fun r => some ((known.lookup r).getD (.reg r))
  flags := ⟨some .flagCF, some .flagZF, some .flagSF, some .flagOF⟩
  mem := []
  regions := regions
  labels := labels
  bounds := bounds
  aliases := aliases

end Sym

end

end NativeRustcX64
