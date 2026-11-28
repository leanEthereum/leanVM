module

public import NativeRustcArm.Basic
public import NativeRustcArm.Sym.State

/-!
# What symbolic states of Kraken's AArch64 machine mean

The symbolic executor (`NativeRustcArm.Sym.exec`) runs a basic block on a symbolic state
`Sym.SState`: each register a symbolic value `Sym` over the atoms of an environment `Sym.Env` (the
registers, SP, flags and memory at some earlier point, the base addresses of the memory regions,
the labels' addresses, further variables), the flags symbolic booleans `SBool`, memory the list of
the symbolic writes into the regions, newest first. `Sym.Match env S m`: the machine state `m`
is what `S` describes in `env`. An operation of width `W32` computes on the low 32 bits of its
operands and zero-extends its result, as Kraken's 32-bit instructions do (`Sym.low`, `Sym.ext`).
-/

namespace NativeRustcArm

@[expose] public section

namespace Sym

/-- What the atoms of symbolic values stand for. -/
structure Env where
  regs : XReg → BitVec 64
  sp : BitVec 64
  flags : StatusFlags
  /-- The memory symbolic loads of unwritten bytes read. -/
  mem0 : DataMem
  /-- Each region's base and size. -/
  regions : List (BitVec 64 × Nat)
  vars : Nat → BitVec 64 := fun _ => 0

/-- The low `w.bits` bits of a 64-bit value, as Kraken reads a register of width `w`. -/
def low (w : RegWidth) (x : BitVec 64) : w.type := x.take w.bits

/-- A value of width `w` zero-extended, as Kraken writes a register of width `w`. -/
def ext : (w : RegWidth) → w.type → BitVec 64
  | .W64, v => v
  | .W32, v => v.zeroExtend 64

/-- The byte `t` of a 64-bit value. -/
def byteOf (x : BitVec 64) (t : Nat) : UInt8 := UInt8.ofNat (x.toNat / 2 ^ (8 * t))

/-- The `n` bytes of a value from byte `t`. -/
def bytesOf (x : BitVec 64) (t n : Nat) : BitVec 64 :=
  BitVec.ofNat 64 (x.toNat / 2 ^ (8 * t) % 2 ^ (8 * n))

/-- Region `r`'s base. -/
def Env.base (env : Env) (r : Nat) : BitVec 64 := ((env.regions[r]?).map (·.1)).getD 0

/-- The `n` bytes of `env.mem0` at `off` in region `r`, little-endian. -/
def Env.load (env : Env) (r off n : Nat) : BitVec 64 :=
  BitVec.ofInt 64 (Int.ofBytes ((List.range n).map fun i =>
    (env.mem0.get? (env.base r + BitVec.ofNat 64 (off + i))).getD 0))

end Sym

open Sym

/-- A binary operation's value. -/
def BinOp.apply : BinOp → (w : RegWidth) → BitVec 64 → BitVec 64 → BitVec 64
  | .add, w, x, y => ext w (low w x + low w y)
  | .sub, w, x, y => ext w (low w x - low w y)
  | .and, w, x, y => ext w (low w x &&& low w y)
  | .orr, w, x, y => ext w (low w x ||| low w y)
  | .eor, w, x, y => ext w (low w x ^^^ low w y)
  | .bic, w, x, y => ext w (low w x &&& ~~~low w y)
  | .orn, w, x, y => ext w (low w x ||| ~~~low w y)
  | .eon, w, x, y => ext w (low w x ^^^ ~~~low w y)
  | .mul, w, x, y => ext w (low w x * low w y)
  | .umulh, w, x, y => ext w ((BitVec.ofInt (w.bits + w.bits)
      ((low w x).unsigned * (low w y).unsigned)).extractLsb' w.bits w.bits)
  | .lslv, w, x, y => ext w (low w x <<< ((low w y).toNat % w.bits))
  | .lsrv, w, x, y => ext w ((low w x).ushiftRight ((low w y).toNat % w.bits))
  | .asrv, w, x, y => ext w ((low w x).sshiftRight ((low w y).toNat % w.bits))
  | .rorv, w, x, y => ext w ((low w x).rotateRight ((low w y).toNat % w.bits))
  | .bfm immr imms, w, x, y => ext w (evalBFM (low w x) (low w y) immr imms)
  | .extr lsb, w, x, y =>
    ext w (if lsb % w.bits == 0 then low w y
      else (low w x <<< (w.bits - lsb % w.bits)) ||| (low w y >>> (lsb % w.bits)))

/-- `REV` of width `w`, as Kraken computes it. -/
def revW : (w : RegWidth) → w.type → w.type
  | .W32, v =>
    let step1 := ((v &&& 0x00FF00FF#32) <<< 8) ||| ((v &&& 0xFF00FF00#32) >>> 8)
    ((step1 &&& 0x0000FFFF#32) <<< 16) ||| ((step1 &&& 0xFFFF0000#32) >>> 16)
  | .W64, v =>
    let step1 := ((v &&& 0x00FF00FF00FF00FF#64) <<< 8) ||| ((v &&& 0xFF00FF00FF00FF00#64) >>> 8)
    let step2 := ((step1 &&& 0x0000FFFF0000FFFF#64) <<< 16) |||
      ((step1 &&& 0xFFFF0000FFFF0000#64) >>> 16)
    ((step2 &&& 0x00000000FFFFFFFF#64) <<< 32) ||| ((step2 &&& 0xFFFFFFFF00000000#64) >>> 32)

/-- A shift or rotation by a constant, as Kraken computes a shifted register operand. -/
def shiftW {n : Nat} (k : ShiftType) (x : BitVec n) (a : Nat) : BitVec n :=
  match k with
  | .LSL => x <<< a
  | .LSR => x.ushiftRight a
  | .ASR => x.sshiftRight a
  | .ROR => x.rotateRight a

/-- A unary operation's value. -/
def UnOp.apply : UnOp → (w : RegWidth) → BitVec 64 → BitVec 64
  | .trunc, w, x => ext w (low w x)
  | .not, w, x => ext w (~~~low w x)
  | .neg, w, x => ext w (-low w x)
  | .inc, w, x => ext w (low w x + 1#w.bits)
  | .rev, w, x => ext w (revW w (low w x))
  | .rbit, w, x => ext w (low w x).reverse
  | .shift k n, w, x => ext w (shiftW k (low w x) n)
  | .ubfm immr imms, w, x => ext w (evalUBFM (low w x) immr imms)
  | .sbfm immr imms, w, x => ext w (evalSBFM (low w x) immr imms)
  | .extend e, w, x => ext w (BitVec.ofInt w.bits (x.apply_extend e))
  | .memExtend e, _, x => BitVec.ofInt 64 (x.apply_mem_extend e)
  | .bytes t n, _, x => bytesOf x t n

/-- A comparison's value. -/
def CmpOp.apply : CmpOp → (w : RegWidth) → BitVec 64 → BitVec 64 → Bool
  | .eq, w, x, y => low w x == low w y
  | .ult, w, x, y => (low w x).ult (low w y)
  | .subV, w, x, y => (low w x - low w y).signed != (low w x).signed - (low w y).signed
  | .addC, w, x, y => (low w x + low w y).unsigned != (low w x).unsigned + (low w y).unsigned
  | .addV, w, x, y => (low w x + low w y).signed != (low w x).signed + (low w y).signed

variable [Labels]

mutual

/-- A symbolic value's value in an environment. -/
def Sym.eval (env : Env) : Sym → BitVec 64
  | .lit n => BitVec.ofNat 64 n
  | .reg r => env.regs r
  | .sp => env.sp
  | .var i => env.vars i
  | .ptr r off => env.base r + BitVec.ofInt 64 off
  | .label l => (Labels.label l).toBitVec
  | .load r off n => env.load r off n
  | .loadx r off idx n => env.load r (off + (idx.eval env).toNat) n
  | .bin op w a b => op.apply w (a.eval env) (b.eval env)
  | .un op w a => op.apply w (a.eval env)
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
  | .bit w a n => (low w (a.eval env)).getLsbD n
  | .flagN => env.flags.n
  | .flagZ => env.flags.z
  | .flagC => env.flags.c
  | .flagV => env.flags.v

end

-- The equation lemmas of the evaluation functions, generated here once rather than in each
-- importer that unfolds them.
attribute [local simp] BinOp.apply UnOp.apply CmpOp.apply Sym.eval SBool.eval

/-- Symbolic flags' value. -/
def SFlags.eval (env : Env) (f : SFlags) : StatusFlags :=
  ⟨f.n.eval env, f.z.eval env, f.c.eval env, f.v.eval env⟩

namespace Sym

/-- The index of a register among X0 to X30. -/
def _root_.XReg.idx : XReg → Nat
  | .X0 => 0 | .X1 => 1 | .X2 => 2 | .X3 => 3 | .X4 => 4 | .X5 => 5 | .X6 => 6 | .X7 => 7
  | .X8 => 8 | .X9 => 9 | .X10 => 10 | .X11 => 11 | .X12 => 12 | .X13 => 13 | .X14 => 14
  | .X15 => 15 | .X16 => 16 | .X17 => 17 | .X18 => 18 | .X19 => 19 | .X20 => 20 | .X21 => 21
  | .X22 => 22 | .X23 => 23 | .X24 => 24 | .X25 => 25 | .X26 => 26 | .X27 => 27 | .X28 => 28
  | .X29 => 29 | .X30 => 30

/-- X0 to X30. -/
def allXRegs : List XReg :=
  [.X0, .X1, .X2, .X3, .X4, .X5, .X6, .X7, .X8, .X9, .X10, .X11, .X12, .X13, .X14, .X15, .X16,
    .X17, .X18, .X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29, .X30]

/-- The symbolic value of a register, if known. -/
def SState.reg (S : SState) (r : XReg) : Option Sym := (S.regs[r.idx]?).getD none

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
  ∀ (r : Nat) (b : BitVec 64) (n : Nat), env.regions[r]? = some (b, n) → ¬(b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + n)

/-- The regions do not wrap around, are mapped in `mem0` and are pairwise disjoint. -/
structure Env.WF (env : Env) : Prop where
  noWrap : ∀ (r : Nat) (b : BitVec 64) (n : Nat), env.regions[r]? = some (b, n) → b.toNat + n ≤ 2 ^ 64
  mapped : ∀ (r : Nat) (b : BitVec 64) (n : Nat), env.regions[r]? = some (b, n) → ∀ i < n,
    (env.mem0.get? (b + BitVec.ofNat 64 i)).isSome
  disjoint : ∀ (r r' : Nat) (b b' : BitVec 64) (n n' : Nat), r ≠ r' → env.regions[r]? = some (b, n) →
    env.regions[r']? = some (b', n') → b.toNat + n ≤ b'.toNat ∨ b'.toNat + n' ≤ b.toNat

/-- **The machine state `m` is what `S` describes in `env`.** Known registers, SP and known flags
are their symbolic values; the regions are `env`'s, with the sizes and alignment `S` records; each
byte of a region is what the newest write covering it says, else `env.mem0`'s; the labels `S`
places at regions' bases are there; the bounds and aliases `S` records hold; memory outside the
regions is `env.mem0`'s. -/
structure Match (env : Env) (S : SState) (m : MachineData) : Prop where
  regs : ∀ r v, S.reg r = some v → (m.regs.getXReg r).toBitVec = v.eval env
  sp : m.regs.SP.toBitVec = S.sp.eval env
  flags : ∀ f, S.flags = some f → m.status = f.eval env
  regions : ∀ (r n : Nat) (al : Bool), S.regions[r]? = some (n, al) →
    ∃ b : BitVec 64, env.regions[r]? = some (b, n) ∧ (al = true → b.toNat % 16 = 0)
  mem : ∀ (r : Nat) (b : BitVec 64) (n : Nat), env.regions[r]? = some (b, n) → ∀ i < n,
    m.dmem.get? (b + BitVec.ofNat 64 i) = memByte env S.mem r b i
  labels : ∀ l r, S.labels.lookup l = some r → env.base r = (Labels.label l).toBitVec
  bounds : ∀ x n, (x, n) ∈ S.bounds → (x.eval env).toNat < n
  aliases : ∀ x r o, S.aliases.lookup x = some (r, o) → x.eval env = env.base r + BitVec.ofInt 64 o
  outside : ∀ a, env.Outside a → m.dmem.get? a = env.mem0.get? a

/-- Where a block's exit leaves the machine, `next` the address after the block. A call leaves the
return address in X30 (`retOf`). -/
def PcOk (env : Env) (x : Exit) (next : Int64) (st : MachineState) : Prop :=
  match x with
  | .fall => st.pc = next
  | .jump l => st.pc = Labels.label l
  | .cond c l => st.pc = if c.eval env then Labels.label l else next
  | .call l => st.pc = Labels.label l ∧ retOf st.data = next
  | .ret => st.pc = retOf st.data

/-- The environment of a machine state: its registers, SP, flags and memory, and the regions. -/
def Env.ofMachine (m : MachineData) (regions : List (BitVec 64 × Nat))
    (vars : Nat → BitVec 64 := fun _ => 0) : Env where
  regs r := (m.regs.getXReg r).toBitVec
  sp := m.regs.SP.toBitVec
  flags := m.status
  mem0 := m.dmem
  regions := regions
  vars := vars

/-- The symbolic state of an environment: each register its atom unless `known` gives it, SP
`sp₀`, the flags their atoms, no writes, the regions `regions`, the labels at regions' bases
`labels`, the bounds `bounds` and the aliases `aliases`. -/
def init (regions : List (Nat × Bool)) (sp₀ : Sym := .sp) (known : List (XReg × Sym) := [])
    (labels : List (Label × Nat) := []) (bounds : List (Sym × Nat) := [])
    (aliases : List (Sym × Nat × Int) := []) : SState where
  regs := allXRegs.map fun r => some ((known.lookup r).getD (.reg r))
  sp := sp₀
  flags := some ⟨.flagN, .flagZ, .flagC, .flagV⟩
  mem := []
  regions := regions
  labels := labels
  bounds := bounds
  aliases := aliases

end Sym

end

end NativeRustcArm
