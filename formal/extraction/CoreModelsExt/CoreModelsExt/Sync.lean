-- Shared ownership and locks, which the extractions only read through.
module
public import Aeneas
public import CoreModels
@[expose] public section
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error

namespace CoreModels

/-- `Arc<T>`, as the value it shares: the extraction only reads through it. -/
def alloc.sync.Arc (T : Type) : Type := T

/-- `Deref` of `Arc`: the shared value. -/
def alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref {T : Type} (self : alloc.sync.Arc T) :
    RustM T :=
  ok self

/-- `std::sync::Mutex<T>`, assumed: interior mutability has no value model here. -/
opaque std.sync.poison.mutex.Mutex (T : Type) : Type

/-- `Mutex::new`, assumed. -/
opaque std.sync.poison.mutex.Mutex.new {T : Type} (value : T) :
    RustM (std.sync.poison.mutex.Mutex T)

end CoreModels
