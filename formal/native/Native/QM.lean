module

public import Mathlib.Logic.Function.Basic

/-!
# QM: a word machine for native code

The verifiers are written for a small machine that both x86-64 and AArch64 implement directly:
sixteen 64-bit registers, 64-bit loads and stores, and structured control flow. This file gives it a
semantics of its own, on a state of registers and a memory of 64-bit words (`QState`), with no
flags: a branch compares and jumps in one construct (`Cond`). Each backend compiles a statement
(`Stmt`) to its architecture's instructions in Kraken (`NativeX64.Compile`, `NativeArm.Compile`) and
proves that the compiled code does on Kraken's machine what `Exec` says the statement does. The
registers carry x86-64's names; AArch64 maps them to its own (`NativeArm`).

`QState.mem` holds the words the code may read and write: a load or a store anywhere else is
stuck (`QInstr.step` is `none`), as in Kraken, where it faults.
-/

@[expose] public section

namespace Native

/-- The machine's registers, named as x86-64's general-purpose registers. -/
inductive Reg64
  | rax | rbx | rcx | rdx | rsi | rdi | rsp | rbp
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr

/-- An index register's scale: `1`, `2`, `4` or `8` bytes. -/
inductive Width | W8 | W16 | W32 | W64
  deriving DecidableEq, Repr

/-- The bytes of a scale. -/
@[simp] def Width.bytes : Width → Nat | .W8 => 1 | .W16 => 2 | .W32 => 4 | .W64 => 8

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

end Native
