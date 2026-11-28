module

public import Kraken.Mem
public import NativeVm.Model.Field

/-!
# Memory, for the contracts of the leanVM crate's functions

The vocabulary of the contracts of `rustc/vm`'s functions on both architectures, on Kraken's byte
memory `Mem 64` (`Kraken.Mem`, each architecture's `DataMem`). The first predicates are
`NativeRustcArm.Basic`'s and `NativeRustcX64.Basic`'s, word for word, so that each architecture's
are these by `Iff.rfl`: `Mapped d a n`, the `n` bytes from `a` are data memory; `BytesAt d a bs`,
they hold `bs`; `InRange a n p`, `p` is one of them; `SameOutside d d' R`, `d'` agrees with `d`
outside `R`; `NoWrap a n`, `Apart a n a' n'`.

Then the crate's values in memory, little-endian as rustc lays them out: a word (`u64`, `usize`)
its eight bytes (`wordBytes`), an `E` element (`EW`, `#[repr(C)]` `c0`, `c1`) its two words
(`ewBytes`), arrays end to end (`WordsAt`, `EWsAt`); and the memory as words (`wordView`), the view
`NativeVm.Entry.EntryPre` and `NativeVm.Decoded` describe the caller's areas in.
-/

namespace NativeRustcVm

open NativeVm.Model

@[expose] public section

/-- The `n` bytes from `a` are data memory. -/
def Mapped (d : Mem 64) (a : BitVec 64) (n : Nat) : Prop :=
  ∀ i < n, (d.get? (a + BitVec.ofNat 64 i)).isSome

/-- The bytes from `a` are `bs`. -/
def BytesAt (d : Mem 64) (a : BitVec 64) (bs : List UInt8) : Prop :=
  ∀ i (h : i < bs.length), d.get? (a + BitVec.ofNat 64 i) = some bs[i]

/-- The address `p` is one of the `n` bytes from `a`. -/
def InRange (a : BitVec 64) (n : Nat) (p : BitVec 64) : Prop := (p - a).toNat < n

/-- `d'` agrees with `d` at every address outside `R`. -/
def SameOutside (d d' : Mem 64) (R : BitVec 64 → Prop) : Prop :=
  ∀ p, ¬ R p → d'.get? p = d.get? p

/-- The `n` bytes from `a` do not wrap around the address space. -/
def NoWrap (a : BitVec 64) (n : Nat) : Prop := a.toNat + n ≤ 2 ^ 64

/-- The `n` bytes from `a` and the `n'` bytes from `a'` are apart. -/
def Apart (a : BitVec 64) (n : Nat) (a' : BitVec 64) (n' : Nat) : Prop :=
  a.toNat + n ≤ a'.toNat ∨ a'.toNat + n' ≤ a.toNat

/-- A region of memory: its address and its byte count. -/
structure Region where
  addr : BitVec 64
  size : Nat

/-- A region is data memory that does not wrap around. -/
def Region.Ok (d : Mem 64) (r : Region) : Prop := Mapped d r.addr r.size ∧ NoWrap r.addr r.size

/-- `p` is a byte of the region. -/
def Region.Holds (r : Region) (p : BitVec 64) : Prop := InRange r.addr r.size p

/-- Regions pairwise apart. -/
def Disjoint (rs : List Region) : Prop :=
  rs.Pairwise fun r r' ↦ Apart r.addr r.size r'.addr r'.size

/-- `p` is a byte of one of the regions. -/
def InAny (rs : List Region) (p : BitVec 64) : Prop := ∃ r ∈ rs, r.Holds p

/-! ## Values -/

/-- A word's eight bytes, little-endian (the statement's `wordBytes`). -/
abbrev wordBytes (w : UInt64) : List UInt8 := LeanVM.Protocol.KeccakHash.wordBytes w

/-- An `E` element's sixteen bytes: limb `0`'s word, then limb `1`'s. -/
def ewBytes (x : EW) : List UInt8 := wordBytes x.c0 ++ wordBytes x.c1

/-- The word at `a` is `w`. -/
def WordAt (d : Mem 64) (a : BitVec 64) (w : UInt64) : Prop := BytesAt d a (wordBytes w)

/-- The words from `a` are `ws`, end to end. -/
def WordsAt (d : Mem 64) (a : BitVec 64) (ws : List UInt64) : Prop :=
  BytesAt d a (ws.flatMap wordBytes)

/-- The `E` element at `a` is `x`. -/
def EWAt (d : Mem 64) (a : BitVec 64) (x : EW) : Prop := BytesAt d a (ewBytes x)

/-- The `E` elements from `a` are `xs`, sixteen bytes each. -/
def EWsAt (d : Mem 64) (a : BitVec 64) (xs : List EW) : Prop :=
  BytesAt d a (xs.flatMap ewBytes)

/-! ## The word view

The memory as the 64-bit words `NativeVm.Input` and `NativeVm.Entry.EntryPre` speak of (`UInt64 →
Option UInt64`): the little-endian word of the eight bytes at an address, where all eight are
mapped. -/

/-- The little-endian number of bytes. -/
def leNat (bs : List UInt8) : Nat := bs.foldr (fun b acc ↦ b.toNat + 256 * acc) 0

/-- The word at each address, where its eight bytes are data memory. -/
def wordView (d : Mem 64) (a : UInt64) : Option UInt64 :=
  (d.loadBytes a.toBitVec 8).map fun bs ↦ UInt64.ofNat (leNat bs)

end

end NativeRustcVm
