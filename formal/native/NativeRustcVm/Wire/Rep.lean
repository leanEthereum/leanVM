module

public import NativeRustcVm.Transcript.Rep
public import NativeVm.Wire.Model

/-!
# The wire decoder's values in memory

The structs of `rustc/vm/src/wire.rs` and what they hold, in the model's terms
(`NativeVm.Wire.decodeM`):

- `Reader` (24 bytes, `ReaderAt`): the wire bytes' address and count, and the cursor `c`, at most
  the count; the bytes `B` at their address. `Reader::le n` reads `rdLe B c n`.
- `Node` (40 bytes, `NodeAt`): the key word, then the digest's four words; `NodesAt`, nodes end to
  end. Each level's siblings (`DecodeWork.sibs`, `10240` bytes a level) with their counts
  (`DecodeWork.sib_counts`): `SibsAt`.
- The leaves (`DecodeWork.leaves`, `512` bytes a leaf): `LeavesAt`, each leaf's first words.
- The decoded proof: TranscriptArm's `DecodedAt`/`PhaseAt` (`NativeRustcVm.Transcript`), of the
  model's arrays `streamW`, `openingsW` of `decodeM`'s result.
-/

namespace NativeRustcVm.Wire

open NativeVm NativeVm.Model NativeVm.Wire LeanVM.Parameters LeanVM.Protocol
open LeanVM.Protocol.Compile NativeRustcVm.Transcript

@[expose] public section

/-! ## The reader -/

/-- `Reader::le n`: the little-endian word of the `n` bytes from `c`, if they are there. -/
def rdLe (B : List UInt8) (c n : Nat) : Option (UInt64 × Nat) :=
  if c + n ≤ B.length then some (leAt B c n, c + n) else none

/-- **The reader** at `r` (`Reader`, 24 bytes) reads the bytes `B` at `bp`, from `c`: the slice's
address and length, the cursor, at most the length; the bytes at their address, apart from the
reader. -/
structure ReaderAt (d : Mem 64) (r bp : BitVec 64) (B : List UInt8) (c : Nat) : Prop where
  ok : Region.Ok d ⟨r, 24⟩
  ptr : WordAt d r (UInt64.ofBitVec bp)
  len : WordAt d (off r 8) B.length.toUInt64
  cur : WordAt d (off r 16) c.toUInt64
  bytes : BytesAt d bp B
  noWrap : NoWrap bp B.length
  apart : 0 < B.length → Apart r 24 bp B.length
  c_le : c ≤ B.length

/-- The reader's cursor word: what a read changes of it. -/
def curRegion (r : BitVec 64) : Region := ⟨off r 16, 8⟩

/-! ## Nodes, leaves -/

/-- Node `nd` at `a` (`Node`, 40 bytes): its key word, then its digest's four words. -/
def NodeAt (d : Mem 64) (a : BitVec 64) (nd : Nat × Digest) : Prop :=
  nd.1 < 2 ^ 64 ∧ WordAt d a nd.1.toUInt64 ∧ WordsAt d (off a 8) nd.2.toList

/-- The nodes `ns` from `a`, end to end. -/
def NodesAt (d : Mem 64) (a : BitVec 64) (ns : List (Nat × Digest)) : Prop :=
  ∀ i (h : i < ns.length), NodeAt d (off a (40 * i)) ns[i]

/-- The bytes of `MAX_QUERIES` nodes (`[Node; MAX_QUERIES]`). -/
def nodesBytes : Nat := 10240

/-- Each level's siblings: level `l`'s count at `cnt + 8 l` (at most `MAX_QUERIES`), its nodes from
`a + 10240 l`. -/
def SibsAt (d : Mem 64) (a cnt : BitVec 64) (sibs : List (List (Nat × Digest))) : Prop :=
  ∀ l (h : l < sibs.length), sibs[l].length ≤ 256 ∧
    WordAt d (off cnt (8 * l)) sibs[l].length.toUInt64 ∧ NodesAt d (off a (nodesBytes * l)) sibs[l]

/-- The leaves from `a`, `512` bytes reserved each: each leaf's words. -/
def LeavesAt (d : Mem 64) (a : BitVec 64) (leaves : List (List K)) : Prop :=
  ∀ i (h : i < leaves.length), WordsAt d (off a (512 * i)) (leaves[i].map K.lane)

/-! ## The decoded proof as the model's arrays -/

/-- An opening as the decoded area holds it. -/
def openingW (o : Opening) : OpeningW :=
  ⟨o.leafIndex.toUInt64, (o.leaf.map K.lane).toArray, o.path.toArray⟩

/-- A phase's openings. -/
def phaseW (po : PhaseOut) : Array OpeningW := (po.openings.map openingW).toArray

/-- The stream. -/
def streamW (s : List E) : Array EW := (s.map EW.ofE).toArray

/-- The phases' openings. -/
def openingsW (ps : List PhaseOut) : Array (Array OpeningW) := (ps.map phaseW).toArray

/-- The opening of query `q` (`NativeVm.Wire.openingOf`): its leaf, at its position among the
distinct positions `ps`, and at each level `lv < h` the sibling `(sibs lv).lookup (q >>> lv)`,
zeros where there is none. -/
def openingAt (ps : List Nat) (leaves : List (List K)) (sibs : List (List (Nat × Digest)))
    (h q : Nat) : Opening :=
  ⟨q, ((ps.zip leaves).lookup q).getD [],
    (List.range h).map fun lv ↦ ((sibs.getD lv []).lookup (q >>> lv)).getD default⟩

/-! ## Sizes -/

/-- The bytes of a phase in the decoded area (`PHASE_WORDS` words). -/
def phaseBytes : Nat := 8 * phaseWords

/-- The bytes of `DecodeWork`. -/
def workBytes : Nat := 483584

end

end NativeRustcVm.Wire
