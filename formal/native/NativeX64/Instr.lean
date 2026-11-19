module

public import Native.QM
public import Kraken.X64.Semantics

/-!
# QM instructions as Kraken's x86-64 instructions

Each QM register is the x86-64 register of its name (`Reg64.toX64`), and each instruction
(`QInstr.toInstr`) is one Kraken instruction; a condition is a `cmp` or `test` (`Cond.toInstr`)
followed by a jump on its condition code (`Cond.cc`). `StateRel s m`: the machine `m` holds the QM
state `s`, every word of `s.mem` eight little-endian bytes of `m`'s memory at an aligned address.
Kraken's flags and vector registers are unconstrained.
-/

open Native hiding Reg64 Width

@[expose] public section

/-- The x86-64 register of a QM register. -/
def Native.Reg64.toX64 : Native.Reg64 → _root_.Reg64
  | .rax => .rax | .rbx => .rbx | .rcx => .rcx | .rdx => .rdx
  | .rsi => .rsi | .rdi => .rdi | .rsp => .rsp | .rbp => .rbp
  | .r8 => .r8 | .r9 => .r9 | .r10 => .r10 | .r11 => .r11
  | .r12 => .r12 | .r13 => .r13 | .r14 => .r14 | .r15 => .r15

/-- Kraken's form of a scale. -/
def Native.Width.toX64 : Native.Width → _root_.Width
  | .W8 => .W8 | .W16 => .W16 | .W32 => .W32 | .W64 => .W64

namespace NativeX64

/-- A 64-bit register operand. -/
abbrev r64 (r : Native.Reg64) : Reg .W64 := .low r.toX64 .W64

/-- Kraken's form of an address. -/
def _root_.Native.Addr.toAddrExpr (a : Addr) : AddrExpr :=
  ⟨some (.reg a.base.toX64), a.idx.map fun (r, w) => ⟨r.toX64, w.toX64⟩, .int64 a.disp⟩

/-- A 64-bit operation at a 64-bit address size. -/
abbrev op64 (op : Operation .W64) : Instr := .regular .W64 .W64 op

/-- The Kraken instruction of a `QInstr`. -/
def _root_.Native.QInstr.toInstr : QInstr → Instr
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
def _root_.Native.Rhs.toOperand : Rhs → Operand .W64
  | .reg r => .reg (r64 r)
  | .imm k => .imm (.int64 k)

/-- The flag-setting instruction of a condition. -/
def _root_.Native.Cond.toInstr : Cond → Instr
  | .cmp _ a b => op64 (.cmp (.reg (r64 a)) b.toOperand)
  | .test _ a b => op64 (.test (.reg (r64 a)) b.toOperand)

/-- The condition code that holds, after `Cond.toInstr`, exactly when the condition does. -/
def _root_.Native.Cond.cc : Cond → CondCode
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

/-! ## The machine relation -/

/-- The words of `q` are in `d`: each at an aligned address, its eight bytes little-endian. -/
def MemRel (q : UInt64 → Option UInt64) (d : DataMem) : Prop :=
  ∀ a v, q a = some v → a.toNat % 8 = 0 ∧ d.loadBytes a.toBitVec 8 = some v.toBytes

/-- `m` holds `s`: each QM register in the x86-64 register of its name, and the memory. -/
def StateRel (s : QState) (m : MachineData) : Prop :=
  (∀ r : Native.Reg64, m.regs.get64 r.toX64 = (s.reg r).toBitVec) ∧ MemRel s.mem m.dmem

end NativeX64
