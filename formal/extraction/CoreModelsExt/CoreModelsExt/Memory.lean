-- Raw pointers and uninitialized memory, which have no value model: assumed.
module
public import Aeneas
public import CoreModels
@[expose] public section
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error

namespace CoreModels

/-- `<[T]>::as_mut_ptr`. -/
opaque core.slice.Slice.as_mut_ptr {T : Type} : Slice T → RustM (MutRawPtr T × Slice T)

/-- `<*mut T>::cast`. -/
opaque core.ptr.mut_ptr.RawPtrMutT.cast {T : Type} (U : Type) : MutRawPtr T → RustM (MutRawPtr U)

/-- `MaybeUninit<T>`: a `T` that may not be initialized yet, which has no model. -/
opaque core.mem.maybe_uninit.MaybeUninit (T : Type) : Type

end CoreModels
