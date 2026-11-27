-- Arrays, slices and `Vec`.
module
public import Aeneas
public import CoreModels
@[expose] public section
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error

namespace CoreModels

/-! ## Arrays -/

/-- `<&[T; N]>::try_from(&[T])`: the slice as an array when it has `N` elements. -/
def core.SharedAArray.Insts.CoreConvertTryFromSharedASliceTryFromSliceError.try_from {T : Type}
    (N : Std.Usize) (s : Slice T) :
    RustM (core.result.Result (Std.Array T N) core.array.TryFromSliceError) :=
  if h : s.val.length = N.val then ok (.Ok (Std.Array.make N s.val h)) else ok (.Err ())

/-- `<[[T; N]]>::as_flattened`: the arrays' elements in order. -/
def core.slice.SliceArray.as_flattened {T : Type} {N : Std.Usize} (self : Slice (Array T N)) :
    RustM (Slice T) :=
  let flat := (self.val.map Array.val).flatten
  if h : flat.length ≤ Usize.max then ok (Slice.from flat h) else fail .panic

/-- `<[[T; N]]>::as_flattened_mut`, assumed: the arrays' elements in order, and the back
function regrouping the flat slice into the arrays. -/
opaque core.slice.SliceArray.as_flattened_mut {T : Type} {N : Std.Usize}
    (self : Slice (Array T N)) : RustM (Slice T × (Slice T → Slice (Array T N)))

/-! ## Slices and vectors -/

/-- `<[T]>::sort_unstable`: the slice sorted ascending by `Ord::cmp`. -/
opaque core.slice.Slice.sort_unstable {T : Type} (OrdInst : core.cmp.Ord T) :
    Slice T → RustM (Slice T)

/-- `Vec::dedup`: each run of consecutive equal elements cut down to its first. -/
opaque alloc.vec.Vec.dedup {T : Type} (PartialEqInst : core.cmp.PartialEq T T) :
    alloc.vec.Vec T → RustM (alloc.vec.Vec T)

end CoreModels
