-- `String`, `str` and formatting. CoreModels' `fmt::Arguments` is `Unit`: a formatted message carries no text.
module
public import Aeneas
public import CoreModels
@[expose] public section
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error

namespace CoreModels

/-! Dictionaries exist at every type: the witnesses `opaque` needs, nothing more. -/

local instance {X Y : Type} : Inhabited (core.borrow.Borrow X Y) := ⟨{ borrow := fun _ => default }⟩

local instance {X Y : Type} : Inhabited (core.convert.From X Y) := ⟨{ «from» := fun _ => default }⟩

/-! ## `String` and `str` -/

/-- `String::clone`. -/
def alloc.string.String.Insts.CoreCloneClone.clone (self : alloc.string.String) :
    RustM alloc.string.String :=
  ok self

/-- `String: Clone`. -/
@[reducible]
def alloc.string.String.Insts.CoreCloneClone : core.clone.Clone alloc.string.String where
  clone := alloc.string.String.Insts.CoreCloneClone.clone
  clone_from := fun _ s => ok s

/-- `String: Eq`, by characters. -/
def alloc.string.String.Insts.CoreCmpEq : core.cmp.Eq alloc.string.String where
  PartialEqInst :=
    { eq := fun a b => ok (@decide _ (instDecidableEqString a b))
      ne := fun a b => ok !(@decide _ (instDecidableEqString a b)) }

/-- `str: Eq`, by bytes. -/
def core.Str.Insts.CoreCmpEq : core.cmp.Eq Str where
  PartialEqInst := { eq := fun a b => ok (a.val == b.val), ne := fun a b => ok (a.val != b.val) }

/-- `String::as_bytes`, its UTF-8 encoding. -/
opaque alloc.string.String.as_bytes : alloc.string.String → RustM (Slice Std.U8)

/-- `String: From<&str>`, the UTF-8 decoding of the bytes. -/
opaque alloc.string.String.Insts.CoreConvertFromShared0Str : core.convert.From alloc.string.String Str

/-- `String: Borrow<str>`, `String::as_str`, its UTF-8 encoding. -/
opaque alloc.string.String.Insts.CoreBorrowBorrowStr : core.borrow.Borrow alloc.string.String Str

/-- The `ToString` trait: its one method, `to_string`. -/
structure alloc.string.ToString (Self : Type) where
  to_string : Self → RustM alloc.string.String

/-! ## Formatting -/

/-- `Debug` for `String`, as CoreModels gives every type it models: the formatter, unwritten. -/
def alloc.string.String.Insts.CoreFmtDebug : core.fmt.Debug alloc.string.String where
  fmt := fun _ f => ok (.Ok (), f)

/-- `Arguments::from_str`, the message of a `panic!` or `assert!` with a literal: CoreModels'
`Arguments` is `Unit`. -/
def core.fmt.Arguments.from_str (_ : Str) : RustM core.fmt.Arguments :=
  ok ()

/-- `fmt::rt::Argument::new_display`, the argument a `{}` placeholder formats. -/
def core.fmt.rt.Argument.new_display {T : Type} (_ : core.fmt.Display T) (_ : T) :
    RustM core.fmt.rt.Argument :=
  ok ⟨.Placeholder ()⟩

/-- `fmt::rt::Argument::new_debug`: an argument of a format string. CoreModels' `Arguments` carry
no text, so the argument is the placeholder every other one is. -/
def core.fmt.rt.Argument.new_debug {T : Type} (_ : core.fmt.Debug T) (_ : T) :
    RustM core.fmt.rt.Argument :=
  ok { ty := .Placeholder () }

/-- `alloc::fmt::format`, `format!`'s string. -/
opaque alloc.fmt.format : core.fmt.Arguments → RustM alloc.string.String

end CoreModels
