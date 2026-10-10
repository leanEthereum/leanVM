import Aeneas
import Leanxmss.Types
import Leanxmss.Bytes

/-!
# Models of the SDK's opaque functions

Written by hand: Aeneas lists what this file must define in `FunsExternal_Template.lean.txt`.

Each is what the SDK function computes in `sdk/src/blake2s.rs`, panics included, with BLAKE2s-256 being the
specification's `Blake2s.hash`. These models are trusted: see the README.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
open leanxmss leanxmss.Bytes

/-! ## `core` -/

/-- `bool::then_some`: `Some(t)` if `true`, else `None`. -/
@[rust_fun "core::bool::{bool}::then_some"]
def core.bool.Bool.then_some {T : Type} (b : Bool) (t : T) : Result (Option T) :=
  ok (if b then some t else none)

/-! ## `Plain`: what `Template::write` takes

A value's size and alignment are `size_of` and `align_of`, and its bytes are those it has in memory, little-endian. -/

@[rust_fun "leanvm_guest::plain::{leanvm_guest::plain::Plain<u32>}::byte"]
def U32.Insts.Leanvm_guestPlainPlain.byte (v : Std.U32) (i : Std.Usize) : Result Std.U8 :=
  ok ⟨BitVec.ofNat 8 (v.val / 2 ^ (8 * i.val))⟩

@[rust_const "leanvm_guest::plain::{leanvm_guest::plain::Plain<u32>}::ALIGN"]
def U32.Insts.Leanvm_guestPlainPlain.ALIGN : Result Std.Usize := ok 4#usize

@[rust_const "leanvm_guest::plain::{leanvm_guest::plain::Plain<u32>}::SIZE"]
def U32.Insts.Leanvm_guestPlainPlain.SIZE : Result Std.Usize := ok 4#usize

@[rust_fun "leanvm_guest::plain::{leanvm_guest::plain::Plain<u64>}::byte"]
def U64.Insts.Leanvm_guestPlainPlain.byte (v : Std.U64) (i : Std.Usize) : Result Std.U8 :=
  ok ⟨BitVec.ofNat 8 (v.val / 2 ^ (8 * i.val))⟩

@[rust_const "leanvm_guest::plain::{leanvm_guest::plain::Plain<u64>}::ALIGN"]
def U64.Insts.Leanvm_guestPlainPlain.ALIGN : Result Std.Usize := ok 8#usize

@[rust_const "leanvm_guest::plain::{leanvm_guest::plain::Plain<u64>}::SIZE"]
def U64.Insts.Leanvm_guestPlainPlain.SIZE : Result Std.Usize := ok 8#usize

/-- An array's elements lie back to back: byte `i` is byte `i % size` of element `i / size`. -/
@[rust_fun "leanvm_guest::plain::{leanvm_guest::plain::Plain<[@T; @N]>}::byte"]
def Array.Insts.Leanvm_guestPlainPlain.byte {T : Type} {N : Std.Usize}
    (PlainInst : leanvm_guest.plain.Plain T) (a : Std.Array T N) (i : Std.Usize) : Result Std.U8 := do
  let size ← PlainInst.SIZE
  match a.val[i.val / size.val]? with
  | some x => PlainInst.byte x ⟨BitVec.ofNat _ (i.val % size.val)⟩
  | none => fail .arrayOutOfBounds

@[rust_const "leanvm_guest::plain::{leanvm_guest::plain::Plain<[@T; @N]>}::ALIGN"]
def Array.Insts.Leanvm_guestPlainPlain.ALIGN {T : Type} (_N : Std.Usize)
    (PlainInst : leanvm_guest.plain.Plain T) : Result Std.Usize :=
  PlainInst.ALIGN

@[rust_const "leanvm_guest::plain::{leanvm_guest::plain::Plain<[@T; @N]>}::SIZE"]
def Array.Insts.Leanvm_guestPlainPlain.SIZE {T : Type} (N : Std.Usize)
    (PlainInst : leanvm_guest.plain.Plain T) : Result Std.Usize := do
  let size ← PlainInst.SIZE
  ok ⟨BitVec.ofNat _ (N.val * size.val)⟩

/-! ## `Template` -/

/-- `Template::new`: the words, then zeros to the end of the block; at most a block (a compile-time assertion). -/
@[rust_fun "leanvm_guest::{leanvm_guest::Template<@W>}::new"]
def leanvm_guest.Template.new {W1 : Std.Usize} (words : Std.Array Std.U64 W1) :
    Result (leanvm_guest.Template W1) := do
  massert (W1.val ≤ 8)
  ok (Bytes.ofWords words.val)

/-- `Template::write`: the value's bytes over the message's from byte `at`, which panics unless the value is aligned
and inside the message. -/
@[rust_fun "leanvm_guest::{leanvm_guest::Template<@W>}::write"]
def leanvm_guest.Template.write {T : Type} {W1 : Std.Usize} (plainPlainInst : leanvm_guest.plain.Plain T)
    (t : leanvm_guest.Template W1) (pos : Std.Usize) (value : T) : Result (leanvm_guest.Template W1) := do
  let size ← plainPlainInst.SIZE
  let align ← plainPlainInst.ALIGN
  massert (pos.val % align.val = 0 ∧ size.val ≤ 8 * W1.val ∧ pos.val ≤ 8 * W1.val - size.val)
  let bytes ← (List.range size.val).mapM fun i => plainPlainInst.byte value ⟨BitVec.ofNat _ i⟩
  ok (Bytes.splice t pos.val (bytes.map fun b => UInt8.ofNat b.val))

/-- `Template::digest`: BLAKE2s-256 of the message, which is one block. -/
@[rust_fun "leanvm_guest::{leanvm_guest::Template<@W>}::digest"]
def leanvm_guest.Template.digest {W1 : Std.Usize} (t : leanvm_guest.Template W1) :
    Result ((Std.Array Std.U64 4#usize) × (leanvm_guest.Template W1)) :=
  ok (Bytes.blake2s t, t)

/-- One step of `Template::chain`: write the counter and the value, and take the digest's first two words. -/
def leanvm_guest.Template.chainStep (COUNTER VALUE : Nat) (t : List UInt8) (value : Std.Array Std.U64 2#usize)
    (c : Nat) : List UInt8 × Std.Array Std.U64 2#usize :=
  let t := Bytes.splice (Bytes.splice t COUNTER (Bytes.le 4 c)) VALUE (Bytes.ofWords value.val)
  let d := Bytes.blake2s t
  (t, Std.Array.make 2#usize [d.val[0]!, d.val[1]!])

/-- `Template::chain`: for each counter in order, write it as the `u32` at byte `COUNTER` and the value at byte
`VALUE`, and the digest's first two words become the value. The two fields must be aligned and inside the message (a
compile-time assertion), and the range not reversed (a run-time one). -/
@[rust_fun "leanvm_guest::{leanvm_guest::Template<@W>}::chain"]
def leanvm_guest.Template.chain {W1 : Std.Usize} (COUNTER VALUE : Std.Usize) (t : leanvm_guest.Template W1)
    (counters : core.ops.range.Range Std.U32) (value : Std.Array Std.U64 2#usize) :
    Result ((Std.Array Std.U64 2#usize) × (leanvm_guest.Template W1)) := do
  massert (COUNTER.val % 4 = 0 ∧ COUNTER.val + 4 ≤ 8 * W1.val)
  massert (VALUE.val % 8 = 0 ∧ VALUE.val + 16 ≤ 8 * W1.val)
  massert (counters.start.val ≤ counters.end.val)
  let (t, value) := (List.range' counters.start.val (counters.end.val - counters.start.val)).foldl
    (fun (t, value) c => leanvm_guest.Template.chainStep COUNTER.val VALUE.val t value c) ((t : List UInt8), value)
  ok (value, t)

/-! ## `hash_with` -/

/-- `Stream::write`: append the words' bytes. The `&mut Self` it returns is the stream itself. -/
@[rust_fun "leanvm_guest::{leanvm_guest::Stream}::write"]
def leanvm_guest.Stream.write {N : Std.Usize} (s : leanvm_guest.Stream) (words : Std.Array Std.U64 N) :
    Result (leanvm_guest.Stream × (leanvm_guest.Stream → leanvm_guest.Stream)) :=
  ok ((s : List UInt8) ++ Bytes.ofWords words.val, fun s => s)

/-- What a closure given to `hash_with` returns in Aeneas's translation (see `scripts/patch_closures.py`): the final
stream, and possibly the closure's own final state, which the caller gets back. -/
class leanvm_guest.HashWithClosure (R : Type) (O : outParam Type) where
  /-- The stream the closure wrote. -/
  stream : R → List UInt8
  /-- What `hash_with` returns, from the digest. -/
  output : R → Std.Array Std.U64 4#usize → O

instance leanvm_guest.HashWithClosure.ofStream :
    leanvm_guest.HashWithClosure leanvm_guest.Stream (Std.Array Std.U64 4#usize) where
  stream s := s
  output _ d := d

instance leanvm_guest.HashWithClosure.ofPair {C : Type} :
    leanvm_guest.HashWithClosure (C × leanvm_guest.Stream) (Std.Array Std.U64 4#usize × C) where
  stream r := r.2
  output r d := (d, r.1)

/-- `hash_with`: run the closure on an empty stream, then BLAKE2s-256 of what it wrote. -/
@[rust_fun "leanvm_guest::hash_with"]
def leanvm_guest.hash_with {T0 R O : Type} [leanvm_guest.HashWithClosure R O]
    (closure : core.ops.function.FnOnce T0 leanvm_guest.Stream R) (write : T0) : Result O := do
  let r ← closure.call_once write ([] : List UInt8)
  ok (leanvm_guest.HashWithClosure.output r (Bytes.blake2s (leanvm_guest.HashWithClosure.stream r)))
