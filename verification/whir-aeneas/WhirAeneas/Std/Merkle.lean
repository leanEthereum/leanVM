module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result

/- Nonopaque models of the standard-library operations the Merkle opening surface reaches.
   Each is the operation's documented, fully determined result; Vec content only, as in the
   rest of the Aeneas library. -/

/-- `Option::branch` (`Try`): `Some v ⇒ Continue v`, `None ⇒ Break None`. -/
@[rust_fun "core::option::{core::ops::try_trait::Try<core::option::Option<@T>>}::branch"]
def core.option.Option.Insts.CoreOpsTry_traitTry.branch {T : Type} :
    Option T → Result (core.ops.control_flow.ControlFlow (Option Never) T)
  | some v => .ok (.Continue v)
  | none => .ok (.Break none)

/-- `Option::from_residual` (`FromResidual`): the only residual is `None`. -/
@[rust_fun
  "core::option::{core::ops::try_trait::FromResidual<core::option::Option<@T>, core::option::Option<!>>}::from_residual"]
def core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual (T : Type) :
    Option Never → Result (Option T)
  | none => .ok none
  | some x => x.casesOn

/-- `Vec::clear`: no elements remain. -/
@[rust_fun "alloc::vec::{alloc::vec::Vec<@T>}::clear"]
def alloc.vec.Vec.clear {T : Type} (_A : Type) (_v : alloc.vec.Vec T) : Result (alloc.vec.Vec T) :=
  .ok (alloc.vec.Vec.new T)

/-- `Option::get_or_insert`: the stored value, or `value` when there is none, with the option
    holding it; the backward function stores the borrow's final value. -/
@[rust_fun "core::option::{core::option::Option<@T>}::get_or_insert"]
def core.option.Option.get_or_insert {T : Type} (o : Option T) (value : T) :
    Result (T × (T → Option T)) :=
  .ok (o.getD value, some)
