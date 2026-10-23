/-
  LeanVM.Protocol.Verifier

  The leanVM verifier (`LeanVM.Spec.Verifier`) on its four files: decoding the bytecode, the
  public input, the scalar stream and the Merkle openings, as the Python's `main` does.
-/

module

public import LeanVM.Parameters.Whir
public import LeanVM.Spec.Blake2s
public import LeanVM.Spec.Verifier
public import LeanVM.Protocol.Compile.Prog
public import LeanVM.Protocol.Blake2sHash
public import LeanVM.Parameters.Field
public import LeanVM.Spec.Fast.Hash

/-!
# The verifier on its four files

The verifier is `LeanVM.Spec.Verifier`. This module adds what `lake exe leanvm-verify` needs to
run it on the files the Rust prover writes (`verifyFiles`), and states that the deployed
verifier is the hash-parametric one at BLAKE2s (`verifyWith_blake2sBytes`).
-/

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters

@[expose] public section

open LeanVM.Semantics LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile
/-- The deployed verifier is the hash-parametric one at `Id` and BLAKE2s. -/
theorem verifyWith_blake2sBytes (bytecode : List K) (publicInput : Digest) (π : Proof) :
    Id.run (verifyWith blake2sBytes bytecode publicInput π) = verify bytecode publicInput π :=
  rfl

/-!
## Loading a proof from its four files

From `verifier.py`, lines 104-106 (`E.from_bytes`), 203-223 (`Digest`),
321-331 (`Proof.load`), 384-400 (`Transcript._merkle_data`, `Transcript.merkle`) and 1411-1428
(`main`). The pinned Rust prover writes the same files
(`crates/leanvm_core/tests/verifiers/python_verifier.rs`, `python_verify`).

The four files:

* `bytecode.bin`: the bytecode table, 8 little-endian bytes per `K` word (`decodeWords`);
* `public_input.bin`: the 32 bytes of the public input digest (`decodeDigest`);
* `stream.bin`: the scalar stream, 24 bytes per `E` element, its three limbs in order
  (`decodeScalars`);
* `merkle_openings.bin`: every Merkle opening in the order the verifier reads them, each its
  leaf's words (8 bytes each) and then one 32-byte sibling per level, with no length fields.

### Cutting the openings

The Python reads the openings file lazily, `8 · leaf_words` bytes then `32 · height` bytes per
queried position, the shape coming from the commitment it opens. `Proof.openings` is that byte
string already cut (`LeanVM.Protocol.Compile.Run`, *Deviation*). The cut is computed here from
the verifier's own configuration rather than by a second interpreter of the program: the
announced sizes at the head of the stream, read by the program's own `readSizes`, fix the stack's
log-size and the rate exponent, and `deriveConfig` fixes the WHIR ladder, whose level `ℓ` opens
commitment `ℓ` at `queries_ℓ` positions in the shape `levelShape` gives (`openingShapes`). These
are the only openings the program makes (commitment `0` is the stack, read by `commitStack`; the
others are WHIR's), and `sampleQueries` returns exactly `queries_ℓ` positions.

The cut is sound with no appeal to that argument: `openOne` checks every opening's width and
height against the commitment it is opened against, and `runProof` requires every opening to be
consumed, so `verify` accepts a cut only if it is the one the program reads; and then its bytes
are the Python's reads in order (`encodeOpenings_splitOpenings`, in
`LeanVM.Protocol.Verifier.Load` with the serializers). It is complete by the round trip
`splitOpenings_encodeOpenings`, given that the shapes are the program's, which the differential
tests on the Rust prover's proofs exercise.
-/

/-! ### Words -/

/-- The word of four little-endian bytes. -/
def wordOfBytes (b0 b1 b2 b3 : UInt8) : UInt32 :=
  UInt32.ofNat (b0.toNat + 2 ^ 8 * b1.toNat + 2 ^ 16 * b2.toNat + 2 ^ 24 * b3.toNat)

/-- Read `n` values of `size` bytes each with `decode`, and the bytes after them; `none` if the
bytes run out (checked on the next `size` bytes, not on the length of all the rest). -/
def readMany {α : Type} (size : ℕ) (decode : Bytes → α) : ℕ → Bytes → Option (List α × Bytes)
  | 0, b => some ([], b)
  | n + 1, b =>
    if (b.take size).length = size then
      (readMany size decode n (b.drop size)).map fun r ↦ (decode (b.take size) :: r.1, r.2)
    else none

/-- The `K` word of eight little-endian bytes (`int.from_bytes(…, "little")`). -/
def kOfBytes (b : Bytes) : K :=
  ofWords (wordOfBytes (b.getD 0 0) (b.getD 1 0) (b.getD 2 0) (b.getD 3 0))
    (wordOfBytes (b.getD 4 0) (b.getD 5 0) (b.getD 6 0) (b.getD 7 0))

/-- The digest of 32 bytes, its words little-endian (`Digest`). -/
def digestOfBytes (b : Bytes) : Digest :=
  Vector.ofFn fun j : Fin 8 ↦
    wordOfBytes (b.getD (4 * j) 0) (b.getD (4 * j + 1) 0) (b.getD (4 * j + 2) 0)
      (b.getD (4 * j + 3) 0)

/-- The scalar of 24 bytes, three little-endian limbs (`E.from_bytes`). -/
def eOfBytes (b : Bytes) : E := E.ofLimbs (kOfBytes b) (kOfBytes (b.drop 8)) (kOfBytes (b.drop 16))

/-! ### The files -/

/-- Read exactly the whole of a byte string as values of `size` bytes. -/
def decodeAll {α : Type} (size : ℕ) (decode : Bytes → α) (b : Bytes) : Option (List α) :=
  match readMany size decode (b.length / size) b with
  | some (xs, []) => some xs
  | _ => none

/-- `bytecode.bin`: the bytecode's words (`main`, `verifier.py:1422-1423`). -/
def decodeWords (b : Bytes) : Option (List K) := decodeAll 8 kOfBytes b

/-- `public_input.bin`: the 32-byte public input (`Digest.__post_init__`). -/
def decodeDigest (b : Bytes) : Option Digest :=
  if b.length = 32 then some (digestOfBytes b) else none

/-- `stream.bin`: the scalars (`Proof.load`). -/
def decodeScalars (b : Bytes) : Option (List E) := decodeAll 24 eOfBytes b

/-- Read one opening of the given height and width (`Transcript._merkle_data`). -/
def readOpening (height width : ℕ) (b : Bytes) : Option (Opening × Bytes) := do
  let (leaf, b) ← readMany 8 kOfBytes width b
  let (path, b) ← readMany 32 digestOfBytes height b
  return (⟨leaf, path⟩, b)

/-- Read one opening per shape `(height, width)`, in order. -/
def readOpenings : List (ℕ × ℕ) → Bytes → Option (List Opening × Bytes)
  | [], b => some ([], b)
  | (height, width) :: shapes, b => do
    let (o, b) ← readOpening height width b
    let (os, b) ← readOpenings shapes b
    return (o :: os, b)

/-- Cut the openings file into openings of the given shapes, consuming it. -/
def splitOpenings (shapes : List (ℕ × ℕ)) (b : Bytes) : Option (List Opening) :=
  match readOpenings shapes b with
  | some (os, []) => some os
  | _ => none

/-! ### The shapes the verifier opens -/

/-- The openings of WHIR's levels after the first, the message log before each level's folds
given: `queries` positions of the next commitment's shape (`levelShape`). -/
def laterOpeningShapes : ℕ → List Whir.Level → List (ℕ × ℕ)
  | _, [] => []
  | messageLog, level :: rest =>
    List.replicate level.queries (levelShape messageLog level (3 * 2 ^ level.fold)) ++
      laterOpeningShapes (messageLog - level.fold) rest

/-- The openings of a WHIR run on a `logN`-variable stack, level by level: level `0` opens the
stack at `commitStack`'s shape, level `ℓ + 1` the commitment read at level `ℓ`
(`verify_whir`, `verifier.py:1008-1086`). -/
def whirOpeningShapes (logN : ℕ) : List Whir.Level → List (ℕ × ℕ)
  | [] => []
  | level :: rest =>
    List.replicate level.queries (levelShape logN level (2 ^ level.fold)) ++
      laterOpeningShapes (logN - level.fold) rest

/-- The announced layout and rate exponent of a stream, read by the program's own `readSizes`
(the hash is not consulted for a value: reads only absorb). -/
def announced (bytecode : List K) (stream : List E) : Option (Layout × ℕ) :=
  (Id.run (Compile.run (fun _ ↦ pure default) (readSizes bytecode) ⟨default, stream, [], []⟩)).map
    (·.1)

/-- The shape of every opening `verify` makes on a proof with this stream, in order. -/
def openingShapes (bytecode : List K) (stream : List E) : Option (List (ℕ × ℕ)) := do
  let (layout, logInverseRate) ← announced bytecode stream
  let config ← deriveConfig layout.stackLog logInverseRate
  return whirOpeningShapes layout.stackLog config

/-- The proof in the files `stream.bin` and `merkle_openings.bin`, for this bytecode. -/
def loadProof (bytecode : List K) (stream openings : Bytes) : Option Proof := do
  let scalars ← decodeScalars stream
  let shapes ← openingShapes bytecode scalars
  let openings ← splitOpenings shapes openings
  return ⟨scalars, openings⟩

/-- **The verifier on the four files**: decode them and run `verify`; a file that does not
decode is rejected, as the Python rejects it. -/
def verifyFiles (bytecode publicInput stream openings : Bytes) : Bool :=
  match decodeWords bytecode, decodeDigest publicInput with
  | some words, some digest =>
    match loadProof words stream openings with
    | some π => verify words digest π
    | none => false
  | _, _ => false

end
end LeanVM.Protocol.Verifier
