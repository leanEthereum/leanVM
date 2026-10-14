module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result

/- Nonopaque logical-content models of the standard-library operations the native transcript
   reads reach (`FromNarg`, `FromUniform`, proof of work). Each is the operation's documented,
   fully determined result; a length a model cannot carry in its type is checked, and the check
   never fails on the result it builds. -/

/-- The closure's results at `ks`, in order, threading its state. -/
def core.array.from_fn.calls {T F : Type} (inst : core.ops.function.FnMut F Usize T) :
    List Nat → F → Result (List T)
  | [], _ => .ok []
  | k :: ks, f => do
    let (x, f') ← inst.call_mut f ⟨BitVec.ofNat _ k⟩
    let xs ← core.array.from_fn.calls inst ks f'
    .ok (x :: xs)

/-- `core::array::from_fn`: the closure called at `0, 1, ..., N - 1`, in order. -/
@[rust_fun "core::array::from_fn"]
def core.array.from_fn {T F : Type} (N : Usize) (inst : core.ops.function.FnMut F Usize T) (f : F) :
    Result (Aeneas.Std.Array T N) :=
  core.array.from_fn.calls inst (List.range N.val) f >>= fun l =>
    if h : l.length = N.val then .ok (Aeneas.Std.Array.make N l h) else .fail .panic

/-- The closure's results on `xs`, in order, threading its state. -/
def core.array.Array.map.calls {T F U : Type} (inst : core.ops.function.FnMut F T U) :
    List T → F → Result (List U)
  | [], _ => .ok []
  | x :: xs, f => do
    let (y, f') ← inst.call_mut f x
    let ys ← core.array.Array.map.calls inst xs f'
    .ok (y :: ys)

/-- `<[T; N]>::map`: the closure on each element, in order. -/
@[rust_fun "core::array::{[@T; @N]}::map"]
def core.array.Array.map {T F U : Type} {N : Usize} (inst : core.ops.function.FnMut F T U)
    (a : Aeneas.Std.Array T N) (f : F) : Result (Aeneas.Std.Array U N) :=
  core.array.Array.map.calls inst a.val f >>= fun l =>
    if h : l.length = N.val then .ok (Aeneas.Std.Array.make N l h) else .fail .panic

/-- `bool::then_some`. -/
@[rust_fun "core::bool::{bool}::then_some"]
def core.bool.Bool.then_some {T : Type} (b : Bool) (x : T) : Result (Option T) :=
  .ok (if b then some x else none)

/-- `Option<&T>::copied`. -/
@[rust_fun "core::option::{core::option::Option<&'0 @T>}::copied"]
def core.option.OptionShared0T.copied {T : Type} (_inst : core.marker.Copy T) (o : Option T) :
    Result (Option T) :=
  .ok o

/-- `<[T]>::split_first_chunk::<N>`: the first `N` elements and the rest, or nothing when the
slice is shorter. -/
@[rust_fun "core::slice::{[@T]}::split_first_chunk"]
def core.slice.Slice.split_first_chunk {T : Type} (N : Usize) (s : Slice T) :
    Result (Option (Aeneas.Std.Array T N × Slice T)) :=
  if h : N.val ≤ s.val.length then
    .ok (some (Aeneas.Std.Array.make N (s.val.take N.val) (by simp; omega),
      Slice.from (s.val.drop N.val) (by have := s.property; simp; omega)))
  else .ok none

/-- The whole `n`-element chunks of `l`, in order. -/
def core.slice.Slice.as_chunks.chunks {T : Type} (N : Usize) (l : List T) : List (Aeneas.Std.Array T N) :=
  if h : 0 < N.val ∧ N.val ≤ l.length then
    Aeneas.Std.Array.make N (l.take N.val) (by simp; omega) ::
      core.slice.Slice.as_chunks.chunks N (l.drop N.val)
  else []
termination_by l.length
decreasing_by simp; omega

/-- `<[T]>::as_chunks::<N>`: the whole chunks and the remainder; it panics for `N = 0`. -/
@[rust_fun "core::slice::{[@T]}::as_chunks"]
def core.slice.Slice.as_chunks {T : Type} (N : Usize) (s : Slice T) :
    Result (Slice (Aeneas.Std.Array T N) × Slice T) :=
  if N.val = 0 then .fail .panic
  else
    let cs := core.slice.Slice.as_chunks.chunks N s.val
    if h : cs.length ≤ Usize.max then
      .ok (Slice.from cs h, Slice.from (s.val.drop (cs.length * N.val)) (by
        have := s.property; simp; omega))
    else .fail .panic

/-- `PartialEq` for pairs: the first components, then the second. -/
@[rust_fun "core::tuple::{core::cmp::PartialEq<(@U, @T), (@U, @T)>}::eq"]
def Pair.Insts.CoreCmpPartialEqPair.eq {U T : Type} (i1 : core.cmp.PartialEq U U)
    (i2 : core.cmp.PartialEq T T) (a b : U × T) : Result Bool := do
  let e ← i1.eq a.1 b.1
  if e then i2.eq a.2 b.2 else .ok false
