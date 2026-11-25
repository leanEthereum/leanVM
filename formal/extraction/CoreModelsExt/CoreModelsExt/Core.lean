-- `Ord`, `bool`, `Option`, ranges and `Borrow`.
module
public import Aeneas
public import CoreModels
@[expose] public section
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error

namespace CoreModels

/-! ## `Ord` -/

/-- `Ord::min`, projected from the dictionary: `other` exactly when `other < self`. -/
abbrev core.cmp.Ord.min {Self : Type} (OrdInst : core.cmp.Ord Self) (self other : Self) :
    RustM Self :=
  core.cmp.min OrdInst self other

/-- `Ord::max`, projected from the dictionary: `other` unless `other < self`. -/
abbrev core.cmp.Ord.max {Self : Type} (OrdInst : core.cmp.Ord Self) (self other : Self) :
    RustM Self :=
  core.cmp.max OrdInst self other

/-- `Ord::clamp`, projected from the dictionary: `max(min, min(self, max))`, a panic unless
`min <= max`. -/
abbrev core.cmp.Ord.clamp {Self : Type} (OrdInst : core.cmp.Ord Self) (self min max : Self) :
    RustM Self :=
  core.cmp.clamp OrdInst self min max

/-- `Ord::cmp` of `[T; N]`: lexicographic, the first unequal elements deciding. -/
def core.Array.Insts.CoreCmpOrd.cmp {T : Type} {N : Std.Usize} (OrdInst : core.cmp.Ord T)
    (self other : Array T N) : RustM core.cmp.Ordering :=
  (self.val.zip other.val).foldlM
    (fun order (x, y) => match order with
      | .Equal => OrdInst.cmp x y
      | _ => ok order)
    .Equal

/-! ## `bool` and `Option` -/

/-- `bool::then`: `if self { Some(f()) } else { None }`. -/
def core.bool.Bool.then {T F : Type} (FnOnceInst : core.ops.function.FnOnce F Unit T)
    (self : Bool) (f : F) : RustM (core.option.Option T) :=
  if self then do
    let x ← FnOnceInst.call_once f ()
    ok (.Some x)
  else ok .None

/-- `bool::then_some`: `if self { Some(t) } else { None }`. -/
def core.bool.Bool.then_some {T : Type} (self : Bool) (t : T) : RustM (core.option.Option T) :=
  ok (if self then .Some t else .None)

/-- `Option<&T>::copied`: references are erased, so the option itself. -/
def core.option.OptionShared0T.copied {T : Type} (_ : core.marker.Copy T)
    (self : core.option.Option T) : RustM (core.option.Option T) :=
  ok self

/-! ## Ranges -/

/-- `Range::contains`, the inherent method: `RangeBounds::contains`. The first dictionary is
the impl block's `Idx: PartialOrd<Idx>` bound, which the body does not use. -/
def core.ops.range.Range.contains {Idx U : Type} (_ : core.cmp.PartialOrd Idx Idx)
    (IdxU : core.cmp.PartialOrd Idx U) (UIdx : core.cmp.PartialOrd U Idx)
    (self : core.ops.range.Range Idx) (item : U) : RustM Bool :=
  core.ops.range.RangeBounds.contains.default
    (core.ops.range.Range.Insts.CoreOpsRangeRangeBounds Idx) IdxU UIdx self item

/-- The derived `Clone` of `Range`: both bounds cloned. -/
def core.ops.range.Range.Insts.CoreCloneClone.clone {Idx : Type}
    (CloneInst : core.clone.Clone Idx) (self : core.ops.range.Range Idx) :
    RustM (core.ops.range.Range Idx) := do
  let start ← CloneInst.clone self.start
  let «end» ← CloneInst.clone self.end
  ok { start, «end» }

/-- The derived `PartialEq` of `Range`: both bounds equal. -/
def core.ops.range.Range.Insts.CoreCmpPartialEqRange.eq {Idx : Type}
    (EqInst : core.cmp.PartialEq Idx Idx) (self other : core.ops.range.Range Idx) :
    RustM Bool := do
  let start ← EqInst.eq self.start other.start
  if start then EqInst.eq self.end other.end else ok false

/-! ## `Borrow` -/

/-- The blanket `T: Borrow<T>`, the identity. -/
def core.borrow.Borrow.Blanket (T : Type) : core.borrow.Borrow T T where
  borrow := fun x => ok x

/-! ## `Copy` -/

/-- `[T; N]: Copy` for `T: Copy`, which the hax Lean library has for `Clone` only. -/
@[reducible]
def core.Array.Insts.CoreMarkerCopy {T : Type _} (N : Std.Usize)
    (copyInst : core.marker.Copy T) : core.marker.Copy (Array T N) where
  cloneCloneInst := core.Array.Insts.CoreCloneClone N copyInst.cloneCloneInst

end CoreModels
