import Rv64Verifier.Proofs.Contracts
import Rv64Verifier.Model.FieldAlg

/-!
# Contracts of the field functions

Statements only: a caller takes these as hypotheses, and `Proofs/Field/*.lean` prove them.

`clmul_low` reads its mask `M3 = 0x8888888888888888` from `.rodata` at `0xa0000008`
(`Field/ClmulLow.lean`), so every function that reaches it asks for that word (`PoolOk`), apart
from the stack it writes; `RodataOk` gives it (`poolOk_of_rodata`). `EMulSpec` is `mul`'s contract
with `PoolOk`; `Contracts.MulSpec`, with `RodataOk`, follows from it (`Proofs/Field/All.lean`).

A `K` is a word (`kOf`); an `E` three (`eAt`). Every contract states the bytes below `sp` it may
write, its callees' included, and the rest of the memory it may write.
-/

namespace Rv64Verifier.FieldContracts
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts

/-- Where the image keeps `M3`. -/
@[rv_addr] def poolAddr : Word := 0xa0000008

/-- `M3`. -/
def poolWord : Word := 0x8888888888888888

/-- `M3` is in place, apart from the `n` bytes below `sp`. -/
structure PoolOk (s : MachineState) (n : Nat) : Prop where
  word : s.getMem poolAddr = poolWord
  apart : Apart poolAddr 8 (stackLo s n) n

/-- `M3` from `.rodata`, the stack apart from it. -/
theorem poolOk_of_rodata {s : MachineState} {n : Nat} (h : RodataOk s)
    (ha : Apart (stackLo s n) n rodataBase rodataSize) : PoolOk s n :=
  ⟨h.clmulMask, by addr_omega [ha]⟩

/-- Memory changes only in the `n` bytes below `sp`. -/
def StackFrame (s t : MachineState) (n : Nat) : Prop := MemFrame s t (stackLo s n) n

/-- The `K` in a register. -/
abbrev kOf (w : Word) : K := BF64.ofBitVec w

/-! ## `clmul`, at `0x8000dbb0` -/

/-- `clmul`'s frame and `clmul_low`'s. -/
@[rv_addr] def clmulStack : Nat := 96

structure ClmulPre (s : MachineState) : Prop where
  stack : StackOk s clmulStack
  pool : PoolOk s clmulStack

/-- The 128-bit carry-less product of `a0` and `a1`: its low word in `a0`, its high in `a1`. -/
structure ClmulPost (s t : MachineState) : Prop where
  lo : t.getReg .x10 = (Model.clmul (s.getReg .x10) (s.getReg .x11)).2
  hi : t.getReg .x11 = (Model.clmul (s.getReg .x10) (s.getReg .x11)).1
  frame : StackFrame s t clmulStack

abbrev ClmulSpec : Prop := FunSpec Image.code 0x8000dbb0 ClmulPre ClmulPost

/-! ## `base_mul`, at `0x8000d774` -/

@[rv_addr] def baseMulStack : Nat := 112

structure BaseMulPre (s : MachineState) : Prop where
  stack : StackOk s baseMulStack
  pool : PoolOk s baseMulStack

/-- `a0 = a0 * a1` in `K`. -/
structure BaseMulPost (s t : MachineState) : Prop where
  value : t.getReg .x10 = (kOf (s.getReg .x10) * kOf (s.getReg .x11)).toBitVec
  frame : StackFrame s t baseMulStack

abbrev BaseMulSpec : Prop := FunSpec Image.code 0x8000d774 BaseMulPre BaseMulPost

/-! ## `<E as Mul>::mul`, at `0x80008c48` -/

/-- `mul`'s contract with `M3` in place, for `.rodata`. -/
abbrev EMulSpec : Prop :=
  FunSpec Image.code 0x80008c48 (fun s ↦ MulArgs s ∧ PoolOk s mulStack) MulPost

/-! ## `<E as Mul<K>>::mul`, at `0x8000ce64` -/

/-- `mul`'s frame and `base_mul`'s stack below it. -/
@[rv_addr] def mulKStack : Nat := 48 + baseMulStack

/-- `a0` = the return slot, `a1` = `self`, `a2` = `rhs` (a `K`, by value). -/
structure MulKPre (s : MachineState) : Prop where
  out : ValidMemRange (s.getReg .x10) 3
  lhs : ValidMemRange (s.getReg .x11) 3
  stack : StackOk s mulKStack
  pool : PoolOk s mulKStack
  outStack : Apart (s.getReg .x10) 24 (stackLo s mulKStack) mulKStack
  lhsStack : Apart (s.getReg .x11) 24 (stackLo s mulKStack) mulKStack

/-- `*out = self * ofK rhs`; memory changes only in `*out` and the stack. -/
structure MulKPost (s t : MachineState) : Prop where
  value : eAt t (s.getReg .x10) = eAt s (s.getReg .x11) * ofK (kOf (s.getReg .x12))
  frame : ∀ a, ¬ Within a (s.getReg .x10) 24 →
    ¬ Within a (stackLo s mulKStack) mulKStack → t.getMem a = s.getMem a

abbrev MulKSpec : Prop := FunSpec Image.code 0x8000ce64 MulKPre MulKPost

/-! ## `K::square`, at `0x8000d670`: a leaf, no stack -/

structure KSquarePost (s t : MachineState) : Prop where
  value : t.getReg .x10 = (kOf (s.getReg .x10) * kOf (s.getReg .x10)).toBitVec
  mem : ∀ a, t.getMem a = s.getMem a

abbrev KSquareSpec : Prop := FunSpec Image.code 0x8000d670 (fun _ ↦ True) KSquarePost

/-! ## `E::square`, at `0x8000e2a0`: a leaf, no stack -/

/-- `a0` = the return slot, `a1` = `self`. -/
structure ESquarePre (s : MachineState) : Prop where
  out : ValidMemRange (s.getReg .x10) 3
  arg : ValidMemRange (s.getReg .x11) 3

/-- `*out = self * self`; memory changes only in `*out`. -/
structure ESquarePost (s t : MachineState) : Prop where
  value : eAt t (s.getReg .x10) = eAt s (s.getReg .x11) * eAt s (s.getReg .x11)
  frame : MemFrame s t (s.getReg .x10) 24

abbrev ESquareSpec : Prop := FunSpec Image.code 0x8000e2a0 ESquarePre ESquarePost

/-! ## `K::inv`, at `0x8000d7f4` -/

/-- `inv`'s frame and `base_mul`'s stack below it. -/
@[rv_addr] def kInvStack : Nat := 32 + baseMulStack

structure KInvPre (s : MachineState) : Prop where
  stack : StackOk s kInvStack
  pool : PoolOk s kInvStack

/-- `a0 = a0⁻¹` in `K`, zero to zero. -/
structure KInvPost (s t : MachineState) : Prop where
  value : t.getReg .x10 = (kOf (s.getReg .x10))⁻¹.toBitVec
  frame : StackFrame s t kInvStack

abbrev KInvSpec : Prop := FunSpec Image.code 0x8000d7f4 KInvPre KInvPost

/-! ## `E::pow`, at `0x8000ef7c` -/

/-- `pow`'s frame and `mul`'s stack below it. -/
@[rv_addr] def powStack : Nat := 80 + mulStack

/-- `a0` = the return slot, `a1` = `self` (the caller's copy, which `pow` overwrites),
`a2` = `exponent`. -/
structure PowPre (s : MachineState) : Prop where
  out : ValidMemRange (s.getReg .x10) 3
  base : ValidMemRange (s.getReg .x11) 3
  stack : StackOk s powStack
  pool : PoolOk s powStack
  outBase : Apart (s.getReg .x10) 24 (s.getReg .x11) 24
  outStack : Apart (s.getReg .x10) 24 (stackLo s powStack) powStack
  baseStack : Apart (s.getReg .x11) 24 (stackLo s powStack) powStack
  basePool : Apart poolAddr 8 (s.getReg .x11) 24

/-- `*out = self ^ exponent`; memory changes only in `*out`, `self` and the stack. -/
structure PowPost (s t : MachineState) : Prop where
  value : eAt t (s.getReg .x10) = eAt s (s.getReg .x11) ^ (s.getReg .x12).toNat
  frame : ∀ a, ¬ Within a (s.getReg .x10) 24 → ¬ Within a (s.getReg .x11) 24 →
    ¬ Within a (stackLo s powStack) powStack → t.getMem a = s.getMem a

abbrev PowSpec : Prop := FunSpec Image.code 0x8000ef7c PowPre PowPost

/-! ## `E::sum` over a slice, at `0x800108b4`: a leaf, no stack -/

/-- The slice's length: `a2 - a1` bytes over 24. -/
def sumLen (s : MachineState) : Nat := ((s.getReg .x12).toNat - (s.getReg .x11).toNat) / 24

/-- `a0` = the return slot, `a1`..`a2` = the slice's bounds, `a2 - a1` a multiple of 24. -/
structure SumPre (s : MachineState) : Prop where
  out : ValidMemRange (s.getReg .x10) 3
  slice : ValidMemRange (s.getReg .x11) (3 * sumLen s)
  bounds : (s.getReg .x11).toNat ≤ (s.getReg .x12).toNat
  whole : ((s.getReg .x12).toNat - (s.getReg .x11).toNat) % 24 = 0

/-- `*out` is the sum of the slice; memory changes only in `*out`. -/
structure SumPost (s t : MachineState) : Prop where
  value : eAt t (s.getReg .x10) = (eListAt s (s.getReg .x11) (sumLen s)).sum
  frame : MemFrame s t (s.getReg .x10) 24

abbrev SumSpec : Prop := FunSpec Image.code 0x800108b4 SumPre SumPost

end Rv64Verifier.FieldContracts
