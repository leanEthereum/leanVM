/-
  LeanVM.Wire.Spec

  The proof's wire encoding, the shared interface of its proofs: the decoding with a hash of its
  own (`fromBytesWithHash`), the pruned form of a phase (`prunePhase`), the hypotheses under which a
  proof survives its encoding (`WireDecodable`), and the statements the wire modules prove.
-/

module

public import LeanVM.Wire.Encoding

/-!
# The wire encoding: definitions and statements for the proofs

The decoding `Proof.fromBytes π` (`LeanVM.Wire.Encoding`) hashes with
`keccak256With π`; `fromBytesWithHash H` is the same with any hash `H : Bytes → m Digest`
(`fromBytes_eq_withHash`), the form the proofs reason in (as `LeanVM.Protocol.WithHash` is for the
verifier). The encoding `Proof.toBytes` (`LeanVM.Wire.Encoding`) hashes nothing.

The round trip holds for a proof whose every phase is what one Merkle tree over a hash `h` opens
(`WireDecodable h`): at least one query and at most `wireMaxQueries`; every path of one height at
most `wireMaxHeight` and every leaf of one width at most `wireMaxLeafWords`; every position below
`2 ^ height`; two paths at one position equal; and the paths agree on the tree: where two paths
pass through one node they carry the same sibling there and climb to the same digest, and a path's
sibling at a node another path passes through is that path's digest there. At most
`wireMaxPhases` phases and fewer than `2 ^ 32` stream elements.

The pruning idea and its formalization on leanerVM's main branch are scaraven's
(https://github.com/scaraven).
-/

@[expose] public section

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile

/-! ## Decoding with a hash of its own -/

section WithHash

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest)

/-- `climbLevel` with the hash `H`. -/
def climbLevelWithHash (nodes carried : List (ℕ × Digest)) :
    m (List (ℕ × Digest) × List (ℕ × Digest)) := do
  let siblingOf (node : ℕ) : Digest :=
    ((nodes.lookup (node ^^^ 1)).orElse fun _ ↦ carried.lookup node).getD default
  let firstChildren := nodes.filter fun (node, _) ↦ node % 2 = 0 ∨ (node ^^^ 1) ∉ nodes.map (·.1)
  let parents ← firstChildren.mapM fun (node, digest) ↦ do
    let (left, right) :=
      if node % 2 = 0 then (digest, siblingOf node) else (siblingOf node, digest)
    let parent ← H (digestBytes left ++ digestBytes right)
    pure (node >>> 1, parent)
  pure (nodes.map fun (node, _) ↦ (node, siblingOf node), parents)

/-- `climbLevels` with the hash `H`. -/
def climbLevelsWithHash : List (List (ℕ × Digest)) → List (ℕ × Digest) →
    m (List (List (ℕ × Digest)))
  | [], _ => pure []
  | carried :: above, nodes => do
    let (siblings, parents) ← climbLevelWithHash H nodes carried
    let rest ← climbLevelsWithHash above parents
    pure (siblings :: rest)

/-- `unprunePhase` with the hash `H`. -/
def unprunePhaseWithHash (phase : PrunedPhase) : m (List Opening) := do
  let leafDigests ← phase.leaves.mapM fun leaf ↦ H (leaf.flatMap K.toBytes)
  let siblings ← climbLevelsWithHash H phase.carried (phase.positions.zip leafDigests)
  pure (phase.queries.map fun query ↦
    ⟨query, ((phase.positions.zip phase.leaves).lookup query).getD [],
      (List.range phase.height).map fun level ↦
        ((siblings.getD level []).lookup (query >>> level)).getD default⟩)

/-- `Proof.fromBytes` with the hash `H`. -/
def fromBytesWithHash (bytes : Bytes) : m (Option Proof) :=
  match readProof bytes with
  | none => pure none
  | some (stream, phases) => do
    let openings ← phases.mapM (unprunePhaseWithHash H)
    pure (some ⟨stream, openings⟩)

end WithHash

/-! ## The pruned form of a phase and the hypotheses of the round trip -/

/-- The pruned form `Prover.phaseToBytes` writes of a phase's paths, as `readPhase` reads it back:
the queries' positions, the first path's height and leaf width, the distinct positions ascending
with the first path's leaf at each, and, level by level, the sibling of each node of
`carriedSiblings` (the first path's through it), keyed by its node. -/
def prunePhase (paths : List Opening) : PrunedPhase :=
  let height := (paths.head?.map fun path ↦ path.path.length).getD 0
  let leafWords := (paths.head?.map fun path ↦ path.leaf.length).getD 0
  let distinct := dedupByKey Opening.leafIndex
    (paths.mergeSort fun a b ↦ a.leafIndex ≤ b.leafIndex)
  let queries := paths.map Opening.leafIndex
  let positions := distinctPositions queries
  ⟨queries, height, leafWords, positions, distinct.map Opening.leaf,
    (List.range height).map fun level ↦
      (carriedSiblings (levelNodes positions level)).map fun node ↦
        (node, ((distinct.find? fun path ↦ path.leafIndex >>> level = node).map
          fun path ↦ path.path.getD level default).getD default)⟩

/-- The digest a path climbs to at level `level` with the hash `h`: its leaf's at level `0`, then
each parent of the node and the sibling, the position's bit choosing the side. -/
def climbTo (h : Bytes → Digest) (path : Opening) : ℕ → Digest
  | 0 => h (path.leaf.flatMap K.toBytes)
  | level + 1 =>
    let node := climbTo h path level
    let sibling := path.path.getD level default
    if (path.leafIndex >>> level) % 2 = 0 then h (digestBytes node ++ digestBytes sibling)
    else h (digestBytes sibling ++ digestBytes node)

/-- **A phase one Merkle tree over `h` opens**, within the decoding's bounds (see the module
docstring). -/
structure PhaseDecodable (h : Bytes → Digest) (paths : List Opening) (height leafWords : ℕ) :
    Prop where
  nonempty : paths ≠ []
  queries_le : paths.length ≤ wireMaxQueries
  height_le : height ≤ wireMaxHeight
  leafWords_le : leafWords ≤ wireMaxLeafWords
  shape : ∀ path ∈ paths, path.path.length = height ∧ path.leaf.length = leafWords
  position_lt : ∀ path ∈ paths, path.leafIndex < 2 ^ height
  same_position : ∀ a ∈ paths, ∀ b ∈ paths, a.leafIndex = b.leafIndex → a = b
  same_node : ∀ a ∈ paths, ∀ b ∈ paths, ∀ level < height,
    a.leafIndex >>> level = b.leafIndex >>> level →
      climbTo h a level = climbTo h b level ∧ a.path.getD level default = b.path.getD level default
  sibling_node : ∀ a ∈ paths, ∀ b ∈ paths, ∀ level < height,
    (a.leafIndex >>> level) ^^^ 1 = b.leafIndex >>> level →
      a.path.getD level default = climbTo h b level

/-- **A proof that survives its encoding** with the hash `h`: at most `wireMaxPhases` phases, each
one a Merkle tree over `h` opens, and fewer than `2 ^ 32` stream elements. -/
structure WireDecodable (h : Bytes → Digest) (proof : Proof) : Prop where
  stream_lt : proof.stream.length < 2 ^ 32
  phases_le : proof.openings.length ≤ wireMaxPhases
  phases : ∀ phase ∈ proof.openings, ∃ height leafWords, PhaseDecodable h phase height leafWords

/-! ## The statements the wire modules prove -/

/-- **The round trip** (`LeanVM.Wire.RoundTrip`): a proof that survives its encoding with `h`
decodes from it, with the hash `h`. -/
def RoundTripStatement : Prop :=
  ∀ (h : Bytes → Digest) (proof : Proof), WireDecodable h proof →
    fromBytesWithHash (m := Id) h proof.toBytes = some proof

/-- **One encoding** (`LeanVM.Wire.OneEncoding`): bytes that decode, with any hash, to a proof are
that proof's encoding. -/
def OneEncodingStatement : Prop :=
  ∀ (h : Bytes → Digest) (bytes : Bytes) (proof : Proof),
    fromBytesWithHash (m := Id) h bytes = some proof → proof.toBytes = bytes

end LeanVM.Wire

end
