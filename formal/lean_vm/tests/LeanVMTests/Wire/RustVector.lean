import LeanVM.Wire.Spec
import Statement.Fast.Keccak

/-!
# The wire encoding on the Rust test's vector

The vector of `proof_round_trips_through_its_one_encoding` (`crates/fiat_shamir/src/wire.rs`,
leanVM): a tree of four rows `[0, 0, 1]`, `[0, 2, 3]`, `[0, 0, 4]`,
`[0, 5, 0]`, opened at the queries `3, 1, 3` with leaves of `3` words (`open`,
`crates/fiat_shamir/src/merkle.rs`: the sibling at level `l` of query `q` is the node
`(q >> l) ^ 1`), and the stream `[F128::new(1, 2)]`. As the Rust asserts: the encoding is
`(4 + 16) + 4 + (4 + 3·4) + 3·4 + 2·2·8 + 2·32 = 148` bytes (the stream; the phase count; the
queries; three sizes; two rows of two words, the common zero word dropped; two siblings); it
decodes, with Keccak-256 over Keccak-f[1600], to the proof, whose encoding is the bytes; and one
more byte is refused.

Each check is run compiled (`#guard`, the hash compiled by `Statement.Fast.Keccak`). The kernel
does not reduce the encoding or the decoding themselves: both sort the positions with core's
`List.mergeSort`, defined by well-founded recursion.

The pruning idea and its formalization on leanerVM's main branch are scaraven's
(https://github.com/scaraven).
-/

namespace LeanVMTests.Wire.RustVector

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile

/-- The rows, `F64` words as their bits. -/
def rows : List (List K) := [[0, 0, 1], [0, 2, 3], [0, 0, 4], [0, 5, 0]].map (·.map K.ofBits)

/-- `hash_words`: Keccak-256 of the words' bytes. -/
def hashWords (words : List K) : Digest := keccak256 (words.flatMap K.toBytes)

/-- `hash_pair`: Keccak-256 of the two digests' bytes. -/
def hashPair (left right : Digest) : Digest := keccak256 (digestBytes left ++ digestBytes right)

/-- The test's `node level i`: the leaf's digest at level `0`, the parent of two leaves above. -/
def node : ℕ → ℕ → Digest
  | 0, i => hashWords (rows.getD i [])
  | _, i => hashPair (hashWords (rows.getD (2 * i) [])) (hashWords (rows.getD (2 * i + 1) []))

/-- `open(4, …, 3, node, row)` at the query `q`: height `2`. -/
def opening (q : ℕ) : Opening :=
  ⟨q, rows.getD q [], (List.range 2).map fun level ↦ node level ((q >>> level) ^^^ 1)⟩

/-- The test's proof. -/
def proof : Proof :=
  ⟨[E.ofLimbs (K.ofBits 1) (K.ofBits 2)], [[3, 1, 3].map opening]⟩

/-- A proof's fields, comparable. -/
def fields (p : Proof) : List (List UInt8) × List (List (ℕ × List K × List Digest)) :=
  (p.stream.map E.toBytes, p.openings.map (·.map fun o ↦ (o.leafIndex, o.leaf, o.path)))

/-- Decoding with Keccak-256 over Keccak-f[1600], as the deployed verifier does. -/
def decode (bytes : Bytes) : Option Proof :=
  Proof.fromBytes (m := Id) (fun s ↦ pure (keccakF1600 s)) bytes

#guard proof.toBytes.length = (4 + 16) + 4 + (4 + 3 * 4) + 3 * 4 + 2 * 2 * 8 + 2 * 32

#guard (decode proof.toBytes).map fields == some (fields proof)

#guard (decode (proof.toBytes ++ [0])).isNone

/- One encoding: the decoded proof's encoding is the bytes. -/
#guard (decode proof.toBytes).map Proof.toBytes == some proof.toBytes

end LeanVMTests.Wire.RustVector
