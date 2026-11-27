-- Integer operations and `f64`.
module
public import Aeneas
public import CoreModels
@[expose] public section
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error

namespace CoreModels

/-! ## Integers -/

/-- `u64::reverse_bits`: bit `i` of the result is bit `63 - i` of the operand. -/
def core.num.U64.reverse_bits (x : Std.U64) : RustM Std.U64 :=
  ok ⟨x.bv.reverse⟩

/-- `u64::trailing_zeros`: the index of the lowest set bit, `64` for zero. -/
def core.num.U64.trailing_zeros (x : Std.U64) : RustM Std.U32 :=
  ok ⟨BitVec.ofNat 32 (((List.range 64).find? fun i => x.val.testBit i).getD 64)⟩

/-- `u64::checked_shl`: `None` when the shift is at least the width. -/
def core.num.U64.checked_shl (x : Std.U64) (rhs : Std.U32) :
    RustM (core.option.Option Std.U64) :=
  if rhs.val < 64 then ok (.Some ⟨x.bv <<< rhs.val⟩) else ok .None

/-- `usize::trailing_zeros`: the index of the lowest set bit, `usize::BITS` for zero. -/
def core.num.Usize.trailing_zeros (x : Std.Usize) : RustM Std.U32 :=
  let bits := Std.UScalarTy.Usize.numBits
  ok ⟨BitVec.ofNat 32 (((List.range bits).find? fun i => x.val.testBit i).getD bits)⟩

/-- `usize::next_power_of_two`: the least power of two at least `x` (`1` for zero). Its
overflow panics, as overflow does throughout the extraction (Rust's debug semantics). -/
def core.num.Usize.next_power_of_two (x : Std.Usize) : RustM Std.Usize :=
  let p := 2 ^ Nat.log2 (2 * x.val - 1)
  if h : p < 2 ^ Std.UScalarTy.Usize.numBits then ok ⟨BitVec.ofNatLT p h⟩ else fail .panic

/-- `usize::next_multiple_of`: the least multiple of `rhs` at least `x`, a panic for a zero
`rhs` or where that overflows. -/
def core.num.Usize.next_multiple_of (x rhs : Std.Usize) : RustM Std.Usize :=
  if rhs.val = 0 then fail .panic
  else
    let m := (x.val + rhs.val - 1) / rhs.val * rhs.val
    if h : m < 2 ^ Std.UScalarTy.Usize.numBits then ok (Std.UScalar.ofNatCore m h)
    else fail .panic

/-- `&u32 + u32`, failing on overflow as `u32 + u32` does. -/
def core.U32.Insts.CoreOpsArithAddShared0U32U32.add (self rhs : Std.U32) : RustM Std.U32 :=
  self + rhs

/-! ## Floating point -/

/-- `f64`, the name Aeneas gives it: an IEEE 754 binary64, as Lean's `Float` is. -/
abbrev F64 := Float

/-- The derived-like `Clone` of `f64`: a copy. -/
def core.F64.Insts.CoreCloneClone.clone (x : F64) : RustM F64 :=
  ok x

end CoreModels
