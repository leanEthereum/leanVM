module

public import NativeRustcVm.Mem

/-!
# Reading the crate's arrays out of memory

The values the contracts of `field.rs`'s array functions and `Buf`'s operations read their
arguments as: the bytes from an address (`bytesFrom`, `0` where unmapped), the word they make
little-endian (`wordOf`), arrays of words and of `E` elements end to end (`wordsOf`, `ewsOf`).
Where `WordsAt`/`EWsAt` say what memory holds, these readers give it back (`wordsOf_of_wordsAt`,
`ewsOf_of_ewsAt`).

A `Buf<T, N>` (`buf.rs`, `#[repr(C)]` `len`, `items`): its count word, then its entries from byte
`8` (`BufEWAt`, `BufWordsAt`); its entries as read (`bufEWOf`, `bufWordsOf`).
-/

namespace NativeRustcVm

open NativeVm.Model

@[expose] public section

/-- The `n` bytes from `a` (`0` where unmapped). -/
def bytesFrom (d : Mem 64) (a : BitVec 64) (n : Nat) : List UInt8 :=
  (List.range n).map fun i ↦ (d.get? (a + BitVec.ofNat 64 i)).getD 0

/-- The little-endian word of the eight bytes from `a`. -/
def wordOf (d : Mem 64) (a : BitVec 64) : UInt64 := UInt64.ofNat (leNat (bytesFrom d a 8))

/-- The `n` words from `a`. -/
def wordsOf (d : Mem 64) (a : BitVec 64) (n : Nat) : List UInt64 :=
  (List.range n).map fun i ↦ wordOf d (a + BitVec.ofNat 64 (8 * i))

/-- The `E` element at `a`: limb `0`'s word, then limb `1`'s. -/
def ewOf (d : Mem 64) (a : BitVec 64) : EW := ⟨wordOf d a, wordOf d (a + 8#64)⟩

/-- The `n` elements of `E` from `a`, sixteen bytes each. -/
def ewsOf (d : Mem 64) (a : BitVec 64) (n : Nat) : List EW :=
  (List.range n).map fun i ↦ ewOf d (a + BitVec.ofNat 64 (16 * i))

/-- A `Buf<EW, N>` at `p` holding `xs`: at most `N` of them, the count, then the entries. -/
def BufEWAt (d : Mem 64) (p : BitVec 64) (N : Nat) (xs : List EW) : Prop :=
  xs.length ≤ N ∧ WordAt d p xs.length.toUInt64 ∧ EWsAt d (p + 8#64) xs

/-- A `Buf<u64, N>` at `p` holding `xs`. -/
def BufWordsAt (d : Mem 64) (p : BitVec 64) (N : Nat) (xs : List UInt64) : Prop :=
  xs.length ≤ N ∧ WordAt d p xs.length.toUInt64 ∧ WordsAt d (p + 8#64) xs

/-- The entries of the `Buf<EW, _>` at `p`, as many as its count word says. -/
def bufEWOf (d : Mem 64) (p : BitVec 64) : List EW := ewsOf d (p + 8#64) (wordOf d p).toNat

/-- The entries of the `Buf<u64, _>` at `p`. -/
def bufWordsOf (d : Mem 64) (p : BitVec 64) : List UInt64 :=
  wordsOf d (p + 8#64) (wordOf d p).toNat

end

end NativeRustcVm
