module

public import Statement.LeanDa
public import Common.WithHash

/-!
# LeanDA with a hash of its own

The statement's LeanDA (`Statement/LeanDa.lean`) hashes with Keccak-256 over the permutation it is
given (`LeanDa.keccakDigestBytes`). Benedikt Wagner's framework and its proofs reason with the hash
a parameter of its own, `H`, beside the sponge's permutation `P`: these are LeanDA's algorithms in
that form, each the statement's definition with the hash a parameter (the commitment, the openings,
the membership challenge's duplex, the relation). `LeanDa.WithHashBridge` proves the statement's
definitions equal to these with the hash Keccak-256 over the permutation.

The framework is Benedikt Wagner's (https://github.com/b-wagn/fv-pq-da, Apache-2.0,
`lean_da/NOTICE`), moved to the random-permutation model.
-/

@[expose] public section

open Polynomial OracleComp OracleSpec ENNReal Common MeasureTheory

set_option linter.unusedSectionVars false

namespace LeanDa

open LeanVM.Parameters (K.toBytes E.toBytes)
open LeanVM.Semantics (KeccakState)
open LeanVM.Protocol.KeccakHash (keccak256With littleEndianLane)

/-! ## The challenge's sponge as the proofs read it

`lean_da`'s proofs read the membership challenge's duplex (`verifier/src/transcript.rs`)
in this form, LeanDA's own transcription: the tags in `K`, the root's words as
symbols of its bytes. The challenge needs only the sponge's seeding and its grind: the root is its
public input, no scalar is observed, and each nonce is absorbed into a copy of the seeded sponge
and permuted (`nonceInput`), the answer's lane `2` its proof of work and lanes `0, 1` the
challenge it draws. The statement draws the challenge with the leanVM verifier's sponge
(`Field.lean`'s `Sponge`, `seedInput`, `absorbNonce`, `squeeze`); `membershipChallengeM_eq_withHash`
(`LeanDa.WithHashBridge`) proves the two the same. -/

/-- Lanes of the rate. -/
def rateLanes : ℕ := 16

/-- Word `i` of a digest, its little-endian bytes `8 i … 8 i + 7` (`Digest::words`). -/
def digestWord (d : DigestBytes) (i : ℕ) : K := K.ofLane (littleEndianLane d.toList i)

/-- The element `c0 + c1·y` (`E::new`). -/
def ofLimbs (c0 c1 : K) : E := CompPoly.Extension.Ext.ofVector #v[c0, c1]

/-- Limb `i` of an element, the coefficient of `y^i`. -/
def limb (x : E) (i : Fin 2) : K := CompPoly.Extension.Ext.coeff x i

/-- **The sponge** (`Sponge`): the lanes the last permutation left, and the scalars absorbed
since with their tags (`pending[..n_pending]`; the challenge absorbs one nonce at a time). -/
structure Sponge where
  /-- The lanes the last permutation left (`state`). -/
  state : KeccakState
  /-- The waiting scalars and their tags, in order. -/
  pending : List (E × K)

/-- The rate lanes the waiting scalars fill: scalar `i`'s two limbs, a zero lane and its tag in
lanes `4 i … 4 i + 3`. -/
def rateWords (pending : List (E × K)) : List K :=
  pending.flatMap fun x ↦ [limb x.1 0, limb x.1 1, 0, x.2]

/-- The lanes a duplexing permutes: the waiting scalars over the rate, the rest of the rate zero,
the capacity kept (`duplex`). -/
def duplexInput (s : Sponge) : KeccakState :=
  Vector.ofFn fun i : Fin 25 ↦
    if (i : ℕ) < rateLanes then ((rateWords s.pending).getD i 0).lane else s.state[i]

/-- The lanes of a fresh sponge: the IV's words in lanes `0 … 3`, the public input's in `4 … 7`. -/
def freshSpongeInput (iv publicInput : DigestBytes) : KeccakState :=
  Vector.ofFn fun i : Fin 25 ↦
    if (i : ℕ) < 4 then (digestWord iv i).lane
    else if (i : ℕ) < 8 then (digestWord publicInput (i - 4)).lane
    else 0

/-- `DS_POW_NONCE`, the tag of a grinding nonce (`transcript.rs`). -/
def powTag : K := K.ofBits 4

/-- **The state a nonce is permuted from** (`absorb_nonce` on a copy of the seeded sponge whose
last state is `y`): the nonce `E::new(nonce, 0)` with its tag over the rate, `y`'s capacity kept. -/
def nonceInput (y : KeccakState) (nonce : ℕ) : KeccakState :=
  duplexInput ⟨y, [(LeanVM.Protocol.Verifier.eOfNat nonce, powTag)]⟩

/-- The challenge an answer draws: its lanes `0, 1` (`E::new(state[0], state[1])`). -/
def chalOfState (y : KeccakState) : E := ofLimbs (K.ofLane y[0]) (K.ofLane y[1])

section Duplex

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

/-- A sponge seeded with one permutation of `freshSpongeInput` (`Sponge::new`). -/
def Sponge.newWith (iv publicInput : DigestBytes) : m Sponge := do
  let state ← π (freshSpongeInput iv publicInput)
  pure ⟨state, []⟩

/-- **The nonce search** from the seeded state `y`, from `nonce` with `fuel` nonces left
(`membership_challenge`, `verifier/src/da.rs`): the first nonce whose answer's lane `2` has
a valid proof of work gives the challenge its answer draws; past the last nonce, none. -/
def grindMWithHash (y : KeccakState) : ℕ → ℕ → m (Option E)
  | _, 0 => pure none
  | nonce, fuel + 1 => do
    let o ← π (nonceInput y nonce)
    if powValid o[2] then pure (some (chalOfState o)) else grindMWithHash y (nonce + 1) fuel

end Duplex

/-! ## The commitment with a hash of its own -/

/-- Keccak-256 over `π`, LeanDA's 32 bytes: the hash of the deployed algorithms over a
permutation. -/
abbrev hashOver (π : KeccakState → KeccakState) (bytes : List UInt8) : DigestBytes :=
  Id.run (keccakDigestBytes π bytes)

/-- Cell `j` of a codeword given as a list of symbols. -/
def listCell (row : List E) (j : ℕ) : List E := (row.drop (j * cellSymbols)).take cellSymbols

section Pure

variable (H : List UInt8 → DigestBytes)

/-- The digest of a cell (`hash_cells`). -/
def cellDigestWithHash (x : Cell) : DigestBytes := H (cellBytes x)

/-- One level up a Merkle tree: node `i` hashes nodes `2i` and `2i + 1`. -/
def upWithHash (f : ℕ → DigestBytes) (i : ℕ) : DigestBytes :=
  H (pairBytes (f (2 * i)) (f (2 * i + 1)))

/-- The root of the Merkle tree over the leaves `f 0 … f (2^d - 1)` (`merkle_nodes_from_leaves`). -/
def merkleRootWithHash : ℕ → (ℕ → DigestBytes) → DigestBytes
  | 0, f => f 0
  | d + 1, f => merkleRootWithHash d (upWithHash H f)

/-- The authentication path of leaf `idx`, siblings from the bottom. -/
def merklePathWithHash : ℕ → (ℕ → DigestBytes) → ℕ → List DigestBytes
  | 0, _, _ => []
  | d + 1, f, idx => f (sibling idx) :: merklePathWithHash d (upWithHash H f) (idx / 2)

/-- The leaves of padded row `i`'s tree: its `128` cell digests (`blob_merkle_nodes`). -/
def cellLeavesWithHash {r : ℕ} (c : Fin (r * 128) → Cell) (i j : ℕ) : DigestBytes :=
  cellDigestWithHash H (paddedCell c i j)

/-- The blob root of padded row `i`: the Merkle root of its cell digests (`blob_merkle_nodes`). -/
def blobRootWithHash {r : ℕ} (c : Fin (r * 128) → Cell) (i : ℕ) : DigestBytes :=
  merkleRootWithHash H 7 (cellLeavesWithHash H c i)

/-- **The commitment to a matrix** (`BlobMatrix::commitment`): the Merkle root of the padded rows'
blob roots, hashed with the row count. -/
def commitCellsWithHash {r : ℕ} (c : Fin (r * 128) → Cell) : DigestBytes :=
  H (pairBytes (merkleRootWithHash H logMaxRows (blobRootWithHash H c)) (countBytes r))

/-- The honest opening of a position: the cell's path in its blob's tree, then its blob root's in
the tree over the blob roots. -/
def openCellWithHash {r : ℕ} (c : Fin (r * 128) → Cell) (p : Fin (r * 128)) : CellOpening :=
  ⟨merklePathWithHash H 7 (cellLeavesWithHash H c (positionRow p)) (positionCell p) ++
    merklePathWithHash H logMaxRows (blobRootWithHash H c) (positionRow p)⟩

/-- One level of a Merkle tree: the digests of neighbouring pairs (`merkle_nodes_from_leaves`). -/
def treeLevelWithHash (nodes : List DigestBytes) : List DigestBytes :=
  (List.range (nodes.length / 2)).map (upWithHash H fun i ↦ nodes.getD i default)

/-- The root of the Merkle tree over a power-of-two number of digests (`merkle_nodes_from_leaves`; on
other lengths, which `commitCodewords` never passes, the crate panics). -/
def treeRootWithHash (nodes : List DigestBytes) : DigestBytes :=
  if nodes.length ≤ 1 then nodes.headD default else treeRootWithHash (treeLevelWithHash H nodes)
termination_by nodes.length
decreasing_by simp only [treeLevelWithHash, List.length_map, List.length_range]; omega

/-- The digest of cell `j` of a codeword (`hash_cells`). -/
def listCellDigestWithHash (row : List E) (j : ℕ) : DigestBytes :=
  H ((listCell row j).flatMap E.toBytes)

/-- The blob root of a codeword: the Merkle root of its `128` cell digests, built level by level
(`blob_merkle_nodes`, `fill_levels`). -/
def listBlobRootWithHash (row : List E) : DigestBytes :=
  treeRootWithHash H ((List.range cellsPerRow).map (listCellDigestWithHash H row))

/-- The digest of the zero cell (`padding_merkle_nodes`'s leaves). -/
def paddingCellWithHash : DigestBytes := H ((List.replicate cellSymbols 0).flatMap E.toBytes)

/-- The blob root of the zero codeword, which pads the tree over the blob roots
(`root_of_padding_blob`, `commit.rs`). -/
def paddingBlobRootWithHash : DigestBytes :=
  treeRootWithHash H (List.replicate cellsPerRow (paddingCellWithHash H))

/-- **The commitment to a matrix of codewords, as the crate computes it** (`BlobMatrix::commitment`):
the rows padded to `maxRows` with zero codewords, the tree over their blob roots, hashed with the
row count. -/
def commitCodewordsWithHash (rows : List (List E)) : DigestBytes :=
  H (pairBytes (treeRootWithHash H (rows.map (listBlobRootWithHash H) ++
    List.replicate (maxRows - rows.length) (paddingBlobRootWithHash H))) (countBytes rows.length))

end Pure

/-- **The commitment to a matrix of codewords, as the crate computes it** (`BlobMatrix::commitment`,
`commit.rs`), over a permutation `π`: on codewords of `2^14` symbols it is the statement's
`commitCells π (cellsOfRows rows)` (`commitCodewords_eq_commitCells`, `LeanDa.Commitment`). The
blob roots in the crate's order, each tree built level by level, as compiled code computes it
fast. -/
def commitCodewords (π : KeccakState → KeccakState) (rows : List (List E)) : DigestBytes :=
  commitCodewordsWithHash (hashOver π) rows

section Monadic

variable {m : Type → Type} [Monad m] (H : List UInt8 → m DigestBytes)
  (P : KeccakState → m KeccakState)

/-- **The challenge `z` of a root** (`membership_challenge`, `verifier/src/da.rs`): the
transcript's sponge seeded with the hash of the label as its IV and the root as its public input
(`Sponge::new`), then the nonce search (`grindMWithHash`). -/
def membershipChallengeMWithHash (root : DigestBytes) : m (Option E) := do
  let iv ← H membershipLabel
  let s ← Sponge.newWith P iv root
  grindMWithHash P s.state 0 nonceCount

/-- Climb from `node` at index `idx` along the siblings `path`. -/
def walkMWithHash : ℕ → DigestBytes → List DigestBytes → m DigestBytes
  | _, node, [] => pure node
  | idx, node, s :: rest => do
    let d ← H (if idx % 2 = 0 then pairBytes node s else pairBytes s node)
    walkMWithHash (idx / 2) d rest

/-- **Verification of a cell opening**: a path of `7 + logMaxRows` siblings, then the row count's
word, that climbs from the cell's digest, at index `128 i + j` (the position), to the commitment. -/
def verifyCellMWithHash (r : ℕ) (com : DigestBytes) (p : Fin (r * 128)) (x : Cell)
    (τ : CellOpening) : m Bool := do
  let d ← H (cellBytes x)
  let root ← walkMWithHash H (p : ℕ) d (τ.path ++ [countBytes r])
  pure (decide (τ.path.length = 7 + logMaxRows) && decide (root = com))

/-- One level up a Merkle tree over an oracle (`up`). -/
def upMWithHash (f : ℕ → m DigestBytes) (i : ℕ) : m DigestBytes := do
  let a ← f (2 * i)
  let b ← f (2 * i + 1)
  H (pairBytes a b)

/-- The root of a Merkle tree over an oracle (`merkleRoot`). -/
def merkleRootMWithHash : ℕ → (ℕ → m DigestBytes) → m DigestBytes
  | 0, f => f 0
  | d + 1, f => merkleRootMWithHash d (upMWithHash H f)

/-- The leaves of padded row `i`'s tree over an oracle (`cellLeaves`). -/
def cellLeavesMWithHash {r : ℕ} (c : Fin (r * 128) → Cell) (i j : ℕ) : m DigestBytes :=
  H (cellBytes (paddedCell c i j))

/-- The blob root of padded row `i` over an oracle (`blobRoot`). -/
def blobRootMWithHash {r : ℕ} (c : Fin (r * 128) → Cell) (i : ℕ) : m DigestBytes :=
  merkleRootMWithHash H 7 (cellLeavesMWithHash H c i)

/-- **The commitment to a matrix over an oracle** (`commitCells`): the tree over the blob roots,
hashed with the row count. -/
def commitCellsMWithHash {r : ℕ} (c : Fin (r * 128) → Cell) : m DigestBytes := do
  let t ← merkleRootMWithHash H logMaxRows (blobRootMWithHash H c)
  H (pairBytes t (countBytes r))

end Monadic

/-- **LeanDA's relation**, with a hash `H` and the sponge's permutation `P` in any
monad: the cells commit to the root and pass the membership test on the root's challenge, drawn
by the deployed duplex (`membershipChallengeWith`). In the games `H` is Keccak-256 over `π`
(`keccak256OverPermutation`) and `P` is `π` (`queryPermutation`). -/
noncomputable def relationMWithHash {m : Type → Type} [Monad m] (H : List UInt8 → m DigestBytes)
    (P : KeccakState → m KeccakState) {r : ℕ} (root : DigestBytes) (c : Fin (r * 128) → Cell) :
      m Bool := do
  let z ← membershipChallengeMWithHash H P root
  let d ← commitCellsMWithHash H c
  pure (decide (d = root) && membershipCheckOpt z c)

end LeanDa

end
