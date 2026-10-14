module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result

/- Nonopaque logical-content models of the standard-library operations the
   generic WHIR replay reaches. Vec content only: capacity and allocator state are
   erased, as everywhere else in the Aeneas library. -/

/-- `usize::trailing_zeros`: the number of low zero bits, the width for zero. -/
@[rust_fun "core::num::{usize}::trailing_zeros"]
def core.num.Usize.trailing_zeros (x : Usize) : Result U32 :=
  let n := if x.val = 0 then 64 else
    (List.range 64).find? (fun i => x.val.testBit i) |>.getD 64
  .ok ⟨BitVec.ofNat 32 n⟩

/-- `usize::div_ceil`, which panics on a zero divisor. -/
@[rust_fun "core::num::{usize}::div_ceil"]
def core.num.Usize.div_ceil (a b : Usize) : Result Usize :=
  if b.val = 0 then .fail .panic
  else .ok ⟨BitVec.ofNat _ ((a.val + b.val - 1) / b.val)⟩

/-- `usize::next_power_of_two` in release: the smallest power of two at least `x` (one for
zero), wrapped to zero when it does not fit. -/
@[rust_fun "core::num::{usize}::next_power_of_two"]
def core.num.Usize.next_power_of_two (x : Usize) : Result Usize :=
  let p := x.val.nextPowerOfTwo
  .ok (if p ≤ Usize.max then ⟨BitVec.ofNat _ p⟩ else 0#usize)

/-- `Option::as_ref`: references are erased, so the option itself. -/
@[rust_fun "core::option::{core::option::Option<@T>}::as_ref"]
def core.option.Option.as_ref {T : Type} (o : Option T) : Result (Option T) :=
  .ok o

/-- `Option::map_or`: the default for `none`, the closure on the payload of `some`. -/
@[rust_fun "core::option::{core::option::Option<@T>}::map_or"]
def core.option.Option.map_or {T U F : Type} (fnOnce : core.ops.function.FnOnce F T U)
    (o : Option T) (default : U) (f : F) : Result U :=
  match o with
  | some value => fnOnce.call_once f value
  | none => .ok default
