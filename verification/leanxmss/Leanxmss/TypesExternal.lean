import Aeneas
import Leanxmss.Bytes

/-!
# Models of the SDK's opaque types

Written by hand: Aeneas lists what this file must define in `TypesExternal_Template.lean.txt`.

Both types are the message bytes a hash will take, which is all the guest can observe of them.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

/-- `leanvm_guest::Template<W>`: a one-block message of `W` words, which is a block whose chaining value is BLAKE2s's
initial one and whose message is these `8 W` bytes, zero-padded (`sdk/src/blake2s.rs`). -/
@[rust_type "leanvm_guest::Template"]
abbrev leanvm_guest.Template (_W : Std.Usize) : Type := List UInt8

/-- `leanvm_guest::Stream`: the bytes written so far to the message `hash_with` hashes. -/
@[rust_type "leanvm_guest::Stream"]
abbrev leanvm_guest.Stream : Type := List UInt8
