import Keccak256
import Statement.HashSignatures
import Hax

/-!
# What the proofs about the scheme crates share, stated

`crates/lean_sphincs` and `crates/lean_xmss` hash with `crates/keccak256`, and the statement of
both schemes is over the same hash (`formal/Statement/HashSignatures.lean`). This file fixes what
the proofs about either scheme's extraction start from: how Rust's bytes stand for the statement's
values, and what they ask of the hasher (`HasherSpec`: `keccak256::Hasher` computes Keccak-256 over
the permutation, which `Hasher.lean` proves from what `absorb` and `digest_of` compute).

Rust's byte arrays are the statement's little-endian bit vectors: a digest `[u8; 16]` is the
`BitVec 128` whose `littleEndianBytes 16` are its bytes.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM Std.Do
open HashSig HashSig.OverPermutation
open LeanVM.Semantics (KeccakState)
open LeanVM.Protocol.KeccakHash (digestBytes keccak256With)

namespace Keccak256Proofs

/-! ## Bytes -/

/-- A Rust byte as the statement's. -/
def b8 (x : Std.U8) : UInt8 := UInt8.ofBitVec x.bv

/-- Rust bytes as the statement's. -/
def bytes (l : List Std.U8) : List UInt8 := l.map b8

/-- The number a byte string spells, least significant byte first. -/
def leNat (l : List UInt8) : Nat := l.foldr (fun b acc ↦ b.toNat + 256 * acc) 0

/-- A Rust digest, public parameter or node, `[u8; 16]`, as the statement's. -/
def toDigest (a : Array Std.U8 16#usize) : Digest := BitVec.ofNat 128 (leNat (bytes a.val))

/-- A Rust message, `[u8; 32]`, as the statement's. -/
def toMessage (a : Array Std.U8 32#usize) : Message := BitVec.ofNat 256 (leNat (bytes a.val))

/-! ## The permutation and the hasher -/

/-- A pure permutation as the statement's algorithms take one, in `Id`. -/
def inId (π : KeccakState → KeccakState) : KeccakState → Id KeccakState := fun s ↦ pure (π s)

/-- Keccak-256 over `π`, as its 32 digest bytes. -/
def hashBytes (π : KeccakState → KeccakState) (input : List UInt8) : List UInt8 :=
  digestBytes (Id.run (keccak256With (inId π) input))

/-- **What the proofs ask of the hasher.** `keccak256::Hasher` computes Keccak-256 over `π`: some relation
`Absorbed h l`, "`h` has absorbed the bytes `l`", holds of a new hasher and the empty string, is
kept by `update`, and `finalize` gives the digest of what was absorbed.

`Hasher::update` and `finalize` are extracted with their bodies; what they rest on that is not
(`keccak256::absorb`, `keccak256::digest_of`, and under them the permutation) is what this stands
in for. -/
structure HasherSpec (π : KeccakState → KeccakState) where
  /-- `h` has absorbed the bytes `l`. -/
  Absorbed : keccak256.Hasher → List UInt8 → Prop
  new : ∃ h, keccak256.Hasher.new = ok h ∧ Absorbed h []
  update : ∀ h l (m : Slice Std.U8), Absorbed h l →
    ∃ h' back, keccak256.Hasher.update h m = ok (h', back) ∧ Absorbed h' (l ++ bytes m.val) ∧
      ∀ x, back x = x
  finalize : ∀ h l, Absorbed h l →
    ∃ d, keccak256.Hasher.finalize h = ok d ∧ bytes d.val = hashBytes π l

end Keccak256Proofs
