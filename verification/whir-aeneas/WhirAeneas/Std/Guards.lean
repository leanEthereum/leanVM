module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result

@[rust_fun
  "core::option::{core::cmp::PartialEq<core::option::Option<@T>, core::option::Option<@T>>}::eq"]
def core.option.Option.Insts.CoreCmpPartialEqOption.eq {T : Type}
    (inst : Aeneas.Std.core.cmp.PartialEq T T) (left right : Option T) : Result Bool :=
  match left, right with
  | some x, some y => inst.eq x y
  | none, none => .ok true
  | _, _ => .ok false

@[rust_fun "core::slice::{[@T]}::first"]
def core.slice.Slice.first {T : Type} (s : Slice T) : Result (Option T) :=
  .ok s.val.head?

namespace WhirAeneas.StdGuards

theorem option_some_eq {T : Type} (inst : Aeneas.Std.core.cmp.PartialEq T T) (x y : T) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq inst (some x) (some y) = inst.eq x y := rfl

theorem option_none_eq {T : Type} (inst : Aeneas.Std.core.cmp.PartialEq T T) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq inst none none = .ok true := rfl

theorem option_some_none {T : Type} (inst : Aeneas.Std.core.cmp.PartialEq T T) (x : T) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq inst (some x) none = .ok false := rfl

theorem option_none_some {T : Type} (inst : Aeneas.Std.core.cmp.PartialEq T T) (x : T) :
    core.option.Option.Insts.CoreCmpPartialEqOption.eq inst none (some x) = .ok false := rfl

theorem first_empty {T : Type} (s : Slice T) (h : s.val = []) :
    core.slice.Slice.first s = .ok none := by
  simp [core.slice.Slice.first, h]

theorem first_nonempty {T : Type} (s : Slice T) (x : T) (xs : List T) (h : s.val = x :: xs) :
    core.slice.Slice.first s = .ok (some x) := by
  simp [core.slice.Slice.first, h]

end WhirAeneas.StdGuards
