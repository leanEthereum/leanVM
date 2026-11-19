module

public import Kraken.X64.Semantics
public import Mathlib.Logic.Function.Basic

/-!
# QM: an x86-64 subset, as a word machine

The verifiers are written in a small subset of x86-64: 64-bit general-purpose registers, aligned
64-bit loads and stores, and structured control flow. This file gives that subset a semantics of its
own, on a state of sixteen 64-bit registers and a memory of aligned 64-bit words (`QState`), with no
flags: a branch compares and jumps in one construct (`Cond`). Each instruction (`QInstr`) is one
Kraken instruction (`QInstr.toInstr`), and a statement (`Stmt`) compiles to Kraken's x86-64
(`X86.Compile`), where `Compile.program_correct` proves that the compiled code does on
Kraken's machine what `Exec` says the statement does.

`QState.mem` holds the words the code may read and write: a load or a store anywhere else is
stuck (`QInstr.step` is `none`), as in Kraken, where it faults.
-/

@[expose] public section

namespace X86

/-- The machine state: the registers and the aligned 64-bit words the code may touch. -/
structure QState where
  /-- The general-purpose registers. -/
  reg : Reg64 → UInt64
  /-- The 64-bit word at each address the code may touch; `none` elsewhere. -/
  mem : UInt64 → Option UInt64

/-- `s` with register `r` set to `v`. -/
def QState.setReg (s : QState) (r : Reg64) (v : UInt64) : QState :=
  { s with reg := Function.update s.reg r v }

/-- `s` with the word at `a` set to `v`. -/
def QState.setMem (s : QState) (a : UInt64) (v : UInt64) : QState :=
  { s with mem := Function.update s.mem a (some v) }

/-- An address `base + index · scale + disp`. -/
structure Addr where
  /-- The base register. -/
  base : Reg64
  /-- The index register and its scale (`W8`: 1, `W16`: 2, `W32`: 4, `W64`: 8 bytes). -/
  idx : Option (Reg64 × Width) := none
  /-- The displacement, a signed 32-bit value for the assembler. -/
  disp : Int64 := 0
  deriving DecidableEq, Repr

/-- The address `a` names in `s`. -/
def Addr.eval (a : Addr) (s : QState) : UInt64 :=
  s.reg a.base + (match a.idx with
    | some (r, w) => s.reg r * w.bytes.toUInt64
    | none => 0) + a.disp.toUInt64

/-- The instructions of the subset. Immediates other than `movi`'s fit a signed 32-bit word; shift
counts are below 64. -/
inductive QInstr
  /-- `d := s`. -/
  | mov (d s : Reg64)
  /-- `d := k` (`movabs` when `k` needs it). -/
  | movi (d : Reg64) (k : Int64)
  /-- `d := [a]`. -/
  | load (d : Reg64) (a : Addr)
  /-- `[a] := s`. -/
  | store (a : Addr) (s : Reg64)
  /-- `[a] := k`. -/
  | storei (a : Addr) (k : Int64)
  /-- `d := a`, the address itself. -/
  | lea (d : Reg64) (a : Addr)
  /-- `d := d + s`. -/
  | add (d s : Reg64)
  /-- `d := d + k`. -/
  | addi (d : Reg64) (k : Int64)
  /-- `d := d - s`. -/
  | sub (d s : Reg64)
  /-- `d := d - k`. -/
  | subi (d : Reg64) (k : Int64)
  /-- `d := d ^ s`. -/
  | xor (d s : Reg64)
  /-- `d := d ^ k`. -/
  | xori (d : Reg64) (k : Int64)
  /-- `d := d & s`. -/
  | and (d s : Reg64)
  /-- `d := d & k`. -/
  | andi (d : Reg64) (k : Int64)
  /-- `d := d | s`. -/
  | or (d s : Reg64)
  /-- `d := ~d`. -/
  | not (d : Reg64)
  /-- `d := -d`. -/
  | neg (d : Reg64)
  /-- `d := d << n`. -/
  | shli (d : Reg64) (n : Nat)
  /-- `d := d >> n`, logical. -/
  | shri (d : Reg64) (n : Nat)
  /-- `d := d >> n`, arithmetic. -/
  | sari (d : Reg64) (n : Nat)
  /-- `d := d` rotated left by `n`. -/
  | roli (d : Reg64) (n : Nat)
  /-- `d := d << (cl & 63)`. -/
  | shlcl (d : Reg64)
  deriving DecidableEq, Repr

/-- One instruction: `none` when it loads or stores a word outside `mem`. -/
def QInstr.step : QInstr → QState → Option QState
  | .mov d r, s => some (s.setReg d (s.reg r))
  | .movi d k, s => some (s.setReg d k.toUInt64)
  | .load d a, s => (s.mem (a.eval s)).map fun v => s.setReg d v
  | .store a r, s => (s.mem (a.eval s)).map fun _ => s.setMem (a.eval s) (s.reg r)
  | .storei a k, s => (s.mem (a.eval s)).map fun _ => s.setMem (a.eval s) k.toUInt64
  | .lea d a, s => some (s.setReg d (a.eval s))
  | .add d r, s => some (s.setReg d (s.reg d + s.reg r))
  | .addi d k, s => some (s.setReg d (s.reg d + k.toUInt64))
  | .sub d r, s => some (s.setReg d (s.reg d - s.reg r))
  | .subi d k, s => some (s.setReg d (s.reg d - k.toUInt64))
  | .xor d r, s => some (s.setReg d (s.reg d ^^^ s.reg r))
  | .xori d k, s => some (s.setReg d (s.reg d ^^^ k.toUInt64))
  | .and d r, s => some (s.setReg d (s.reg d &&& s.reg r))
  | .andi d k, s => some (s.setReg d (s.reg d &&& k.toUInt64))
  | .or d r, s => some (s.setReg d (s.reg d ||| s.reg r))
  | .not d, s => some (s.setReg d (~~~ s.reg d))
  | .neg d, s => some (s.setReg d (0 - s.reg d))
  | .shli d n, s => some (s.setReg d (s.reg d <<< n.toUInt64))
  | .shri d n, s => some (s.setReg d (s.reg d >>> n.toUInt64))
  | .sari d n, s => some (s.setReg d (UInt64.ofBitVec ((s.reg d).toBitVec.sshiftRight (n % 64))))
  | .roli d n, s => some (s.setReg d (UInt64.ofBitVec ((s.reg d).toBitVec.rotateLeft (n % 64))))
  | .shlcl d, s => some (s.setReg d (s.reg d <<< (s.reg .rcx &&& 63)))

/-- The right operand of a comparison. -/
inductive Rhs
  | reg (r : Reg64)
  | imm (k : Int64)
  deriving DecidableEq, Repr

/-- The value of `r` in `s`. -/
def Rhs.eval : Rhs → QState → UInt64
  | .reg r, s => s.reg r
  | .imm k, _ => k.toUInt64

/-- A comparison of unsigned words. -/
inductive Rel
  | eq
  | ne
  /-- unsigned `<` -/
  | ltu
  /-- unsigned `≥` -/
  | geu
  deriving DecidableEq, Repr

/-- A branch condition, evaluated without changing the state (the flags are not part of it). -/
inductive Cond
  /-- `a rel b` (x86 `cmp`). -/
  | cmp (rel : Rel) (a : Reg64) (b : Rhs)
  /-- `(a & b) = 0` when `zero`, `≠ 0` otherwise (x86 `test`). -/
  | test (zero : Bool) (a : Reg64) (b : Rhs)
  deriving DecidableEq, Repr

/-- The value of a condition. -/
def Cond.eval : Cond → QState → Bool
  | .cmp .eq a b, s => s.reg a == b.eval s
  | .cmp .ne a b, s => s.reg a != b.eval s
  | .cmp .ltu a b, s => decide (s.reg a < b.eval s)
  | .cmp .geu a b, s => decide (b.eval s ≤ s.reg a)
  | .test zero a b, s => ((s.reg a &&& b.eval s) == 0) == zero

/-- Structured statements over the subset. -/
inductive Stmt
  | skip
  | ins (i : QInstr)
  | seq (a b : Stmt)
  /-- If `c` then `t` else `e`. -/
  | ite (c : Cond) (t e : Stmt)
  /-- While `c`, `body`. -/
  | loop (c : Cond) (body : Stmt)
  /-- Stop with an error: jump to the program's failure exit. -/
  | fail
  deriving Repr

/-- How a statement ends: normally, or at the failure exit. -/
inductive Outcome
  | ok (s : QState)
  | err (s : QState)

/-- Big-step semantics: `Exec c s o` when `c` run from `s` ends with `o`. -/
inductive Exec : Stmt → QState → Outcome → Prop
  | skip (s : QState) : Exec .skip s (.ok s)
  | ins {i : QInstr} {s s' : QState} : i.step s = some s' → Exec (.ins i) s (.ok s')
  | seqOk {a b : Stmt} {s s₁ : QState} {o : Outcome} :
      Exec a s (.ok s₁) → Exec b s₁ o → Exec (.seq a b) s o
  | seqErr {a b : Stmt} {s s₁ : QState} : Exec a s (.err s₁) → Exec (.seq a b) s (.err s₁)
  | iteTrue {c : Cond} {t e : Stmt} {s : QState} {o : Outcome} :
      c.eval s = true → Exec t s o → Exec (.ite c t e) s o
  | iteFalse {c : Cond} {t e : Stmt} {s : QState} {o : Outcome} :
      c.eval s = false → Exec e s o → Exec (.ite c t e) s o
  | loopTrue {c : Cond} {body : Stmt} {s s₁ : QState} {o : Outcome} :
      c.eval s = true → Exec body s (.ok s₁) → Exec (.loop c body) s₁ o → Exec (.loop c body) s o
  | loopErr {c : Cond} {body : Stmt} {s s₁ : QState} :
      c.eval s = true → Exec body s (.err s₁) → Exec (.loop c body) s (.err s₁)
  | loopFalse {c : Cond} {body : Stmt} {s : QState} :
      c.eval s = false → Exec (.loop c body) s (.ok s)
  | fail (s : QState) : Exec .fail s (.err s)

/-! ## The Kraken instructions -/

/-- A 64-bit register operand. -/
abbrev r64 (r : Reg64) : Reg .W64 := .low r .W64

/-- Kraken's form of an address. -/
def Addr.toAddrExpr (a : Addr) : AddrExpr :=
  ⟨some (.reg a.base), a.idx.map fun (r, w) => ⟨r, w⟩, .int64 a.disp⟩

/-- A 64-bit operation at a 64-bit address size. -/
abbrev op64 (op : Operation .W64) : Instr := .regular .W64 .W64 op

/-- The Kraken instruction of a `QInstr`. -/
def QInstr.toInstr : QInstr → Instr
  | .mov d s => op64 (.mov (.reg (r64 d)) (.reg (r64 s)))
  | .movi d k => op64 (.mov (.reg (r64 d)) (.imm (.int64 k)))
  | .load d a => op64 (.mov (.reg (r64 d)) (.mem a.toAddrExpr))
  | .store a s => op64 (.mov (.mem a.toAddrExpr) (.reg (r64 s)))
  | .storei a k => op64 (.mov (.mem a.toAddrExpr) (.imm (.int64 k)))
  | .lea d a => op64 (.lea (r64 d) a.toAddrExpr)
  | .add d s => op64 (.add (.reg (r64 d)) (.reg (r64 s)))
  | .addi d k => op64 (.add (.reg (r64 d)) (.imm (.int64 k)))
  | .sub d s => op64 (.sub (.reg (r64 d)) (.reg (r64 s)))
  | .subi d k => op64 (.sub (.reg (r64 d)) (.imm (.int64 k)))
  | .xor d s => op64 (.xor (.reg (r64 d)) (.reg (r64 s)))
  | .xori d k => op64 (.xor (.reg (r64 d)) (.imm (.int64 k)))
  | .and d s => op64 (.and (.reg (r64 d)) (.reg (r64 s)))
  | .andi d k => op64 (.and (.reg (r64 d)) (.imm (.int64 k)))
  | .or d s => op64 (.or (.reg (r64 d)) (.reg (r64 s)))
  | .not d => op64 (.not (.reg (r64 d)))
  | .neg d => op64 (.neg (.reg (r64 d)))
  | .shli d n => op64 (.shl (.reg (r64 d)) (.imm8 (.int64 (Int64.ofNat n))))
  | .shri d n => op64 (.shr (.reg (r64 d)) (.imm8 (.int64 (Int64.ofNat n))))
  | .sari d n => op64 (.sar (.reg (r64 d)) (.imm8 (.int64 (Int64.ofNat n))))
  | .roli d n => op64 (.rol (.reg (r64 d)) (.imm8 (.int64 (Int64.ofNat n))))
  | .shlcl d => op64 (.shl (.reg (r64 d)) .cl)

/-- Kraken's form of a comparison's right operand. -/
def Rhs.toOperand : Rhs → Operand .W64
  | .reg r => .reg (r64 r)
  | .imm k => .imm (.int64 k)

/-- The flag-setting instruction of a condition. -/
def Cond.toInstr : Cond → Instr
  | .cmp _ a b => op64 (.cmp (.reg (r64 a)) b.toOperand)
  | .test _ a b => op64 (.test (.reg (r64 a)) b.toOperand)

/-- The condition code that holds, after `Cond.toInstr`, exactly when the condition does. -/
def Cond.cc : Cond → CondCode
  | .cmp .eq _ _ => .z
  | .cmp .ne _ _ => .nz
  | .cmp .ltu _ _ => .c
  | .cmp .geu _ _ => .nc
  | .test true _ _ => .z
  | .test false _ _ => .nz

/-- The negation of a condition code. -/
def CondCode.not : CondCode → CondCode
  | .o => .no | .no => .o | .c => .nc | .nc => .c | .z => .nz | .nz => .z | .be => .a | .a => .be
  | .s => .ns | .ns => .s | .p => .np | .np => .p | .l => .ge | .ge => .l | .le => .g | .g => .le

/-! ## The machine relation

A `QState` describes a Kraken `MachineData` when the registers agree and every word of `mem` is
eight bytes of the data memory at an aligned address, little-endian. Kraken's flags and vector
registers are unconstrained. -/

/-- The words of `q` are in `d`: each at an aligned address, its eight bytes little-endian. -/
def MemRel (q : UInt64 → Option UInt64) (d : DataMem) : Prop :=
  ∀ a v, q a = some v → a.toNat % 8 = 0 ∧ d.loadBytes a.toBitVec 8 = some v.toBytes

/-- `s` describes `m`. -/
def StateRel (s : QState) (m : MachineData) : Prop :=
  (∀ r, m.regs.get64 r = (s.reg r).toBitVec) ∧ MemRel s.mem m.dmem

/-! ## Building blocks -/

/-- One instruction. -/
abbrev I (i : QInstr) : Stmt := .ins i

/-- A sequence of statements. -/
def blk : List Stmt → Stmt
  | [] => .skip
  | [s] => s
  | s :: ss => .seq s (blk ss)

/-- Fail when `c` holds. -/
def failIf (c : Cond) : Stmt := .ite c .fail .skip

/-- The address `base + disp`. -/
def at_ (base : Reg64) (disp : Int64) : Addr := { base := base, disp := disp }

end X86
