module

public import LeanDa.Field
public import Mathlib.LinearAlgebra.Lagrange

/-!
# LeanDA

The erasure code commitment of `crates/lean_da` at leanVM `b64b3d41f`, specified in
`doc/leanvm/body/10-ethereum.tex` §sec:leanda, for a matrix of `r` rows.

* **The code** (`encode.rs:12-36`). A row's payload is `2^14` symbols of `K`, the evaluations on
  the domain points `0 … 2^14 - 1` of the polynomial of degree below `2^14` they determine. Its
  codeword is that polynomial's evaluations on all `2^15` points (`encodeRow`): the inverse
  additive NTT interpolates, the forward one evaluates, so the payload is the codeword's first
  half. Both transforms compute these maps (Annex D, Proposition prop:ntt); they are not
  transcribed here.
* **Cells** (`lib.rs:23-39`). A codeword is `128` cells of `256` symbols, cell `j` its symbols
  `256 j … 256 j + 255`. A matrix of `r` codewords has `128 r` cells, cell `j` of row `i` at
  position `128 i + j`: the positions of the erasure code commitment are the cells sampling
  opens.
* **The commitment** (`commit.rs:55-151`). The rows are padded to `2^⌈log₂ r⌉` with zero
  codewords. A cell's digest is BLAKE2s of its symbols' little-endian bytes (`hash_cells`). The
  row tree is the Merkle tree over each row's digest of its first `64` cell digests (the payload),
  the column tree the one over all cell digests in column-major order, and the root is
  `H(rowRoot ‖ colRoot)`. A tree hashes neighbours in pairs, level by level (`tree_from_leaves`).
  The padding digests of `padding_digests` are the digests of zero cells and rows, so the root is
  the commitment to the padded matrix.
* **Openings.** A cell is opened by its authentication path in the column tree and the row root.
  The crate keeps the column tree for this (`DaWitness::column_tree`, `commit.rs:23-45`), whose
  level `⌈log₂ r⌉` holds the column roots (`column_roots`), but verifies no sample:
  `verifyCell` is the check this path determines.
* **Membership** (`membership.rs:32-82`, `verifier/src/da.rs:15-89`). Challenges `z ∈ E^14` give
  the dual codeword `L`, the tensor `⊗_j (1, z_j)` read as novel-basis coefficients and encoded,
  that is `L(x) = ∏_j (1 + z_j Ŵ_j(x))` on the domain (Annex D, eq. dual-product), with
  `Ŵ_j` the normalized subspace polynomial of the span of `e_0 … e_(j-1)`. A matrix passes when
  every row is orthogonal to `L` (`check_membership`, `membership.rs:90-99`; the guest's
  `da_verify`). The challenges are a BLAKE2s chain from the label over the root
  (`membership_challenges`); the security game models them as one random oracle on the root.
* **The deployed algorithms** (`commit.rs:55-145`, `verifier/src/da.rs:14-101`). The crate's
  computations, transcribed computably on lists, for `formal/lean_vm` to state the aggregation
  node's DA claim with: `commitCodewords`, the commitment level by level, which is `commitCells`
  of the matrix (`commitCodewords_eq_commitCells`, `LeanDa.Commitment`); the challenges' BLAKE2s
  chain (`membershipChallenges`); the dual codeword by the additive NTT (`membershipVector`),
  whose agreement with `dual` is not proved; and the vector's digest (`vectorDigest`).

The row count `r` is a parameter. The crate takes `1 ≤ r ≤ 1024` (`row_count`, `lib.rs:41-46`);
the statements hold for every `r ≥ 1`. So is the hash `H`: the crate's is BLAKE2s-256, which
`formal/lean_vm` supplies (`LeanVM.Da.blake2s`), and the statements hold for every `H`.
-/

open Polynomial

namespace LeanDa

@[expose] public section

/-- A digest of the hash, 32 bytes (`fiat_shamir::merkle::Hash`, `[u8; 32]`). -/
abbrev Digest := Vector UInt8 32

/-! ## Shapes (`lib.rs:23-39`) -/

/-- Payload symbols per row, as a logarithm (`DA_LOG_K`). -/
def logK : ℕ := 14

/-- Codeword symbols per row, as a logarithm: rate one half (`LOG_M`). -/
def logM : ℕ := 15

/-- Symbols per cell (`CELL_SYMBOLS`). -/
def cellSymbols : ℕ := 256

/-- Cells per codeword (`CELLS_PER_ROW`). -/
def cellsPerRow : ℕ := 128

/-- Cells per payload (`PAYLOAD_CELLS`). -/
def payloadCells : ℕ := 64

/-- The most rows the crate commits to (`DA_MAX_ROWS`). -/
def maxRows : ℕ := 1024

/-- A row's payload. -/
abbrev Payload := Fin (2 ^ 14) → K

/-- A codeword, in domain order. -/
abbrev Row := Fin (2 ^ 15) → K

/-- A sampling cell. -/
abbrev Cell := Fin 256 → K

/-! ## The code (`encode.rs`) -/

/-- The polynomial of degree below `2^14` taking the payload's values on the points
`0 … 2^14 - 1` (`inverse_transform`). -/
noncomputable def interpolate (p : Payload) : K[X] :=
  Lagrange.interpolate Finset.univ (fun a : Fin (2 ^ 14) ↦ point a) p

/-- **The systematic encoding of a payload** (`encode_rows`): its polynomial's values on all
`2^15` points (`encode_interleaved_in_place`). -/
noncomputable def encodeRow (p : Payload) : Row := fun b ↦ (interpolate p).eval (point b)

/-- Cell `j` of a codeword: its symbols `256 j … 256 j + 255`. -/
def rowCell (w : Row) (j : Fin 128) : Cell := fun s ↦ w ⟨256 * j + s, by omega⟩

/-- The position of cell `j` of row `i`. -/
def pos {r : ℕ} (i : Fin r) (j : Fin 128) : Fin (r * 128) := ⟨128 * i + j, by omega⟩

/-- The row of a position. -/
def posRow {r : ℕ} (p : Fin (r * 128)) : Fin r := ⟨p / 128, by omega⟩

/-- The cell of a position within its row. -/
def posCell {r : ℕ} (p : Fin (r * 128)) : Fin 128 := ⟨p % 128, by omega⟩

/-- The cells of a matrix of encoded payloads. -/
noncomputable def encodeMatrix {r : ℕ} (msg : Fin r → Payload) : Fin (r * 128) → Cell :=
  fun p ↦ rowCell (encodeRow (msg (posRow p))) (posCell p)

/-- Row `i` of a matrix given by its cells. -/
def rowOf {r : ℕ} (c : Fin (r * 128) → Cell) (i : Fin r) : Row :=
  fun b ↦ c (pos i ⟨b / 256, by omega⟩) ⟨b % 256, by omega⟩

/-! ## The commitment (`commit.rs`) -/

variable (H : List UInt8 → Digest)

/-- The eight little-endian bytes of a symbol (`as_bytes`). -/
def kBytes (a : K) : List UInt8 := (List.range 8).map fun t ↦ (a.toBitVec.toNat >>> (8 * t)).toUInt8

/-- A cell's bytes: its symbols' bytes in order. -/
def cellBytes (x : Cell) : List UInt8 := (List.ofFn x).flatMap kBytes

/-- The 64 bytes of a pair of digests (`hash_pair`, `tree_from_leaves`). -/
def pairBytes (a b : Digest) : List UInt8 := a.toList ++ b.toList

/-- The digest of a cell (`hash_cells`). -/
def cellDigest (x : Cell) : Digest := H (cellBytes x)

/-- `⌈log₂ r⌉`: the padded row count `2^⌈log₂ r⌉` is `r.next_power_of_two()`. -/
def logPad (r : ℕ) : ℕ := Nat.clog 2 r

/-- The padded row count. -/
def nPad (r : ℕ) : ℕ := 2 ^ logPad r

/-- Cell `j` of row `i` of the padded matrix: zero below the `r` rows. -/
def paddedCell {r : ℕ} (c : Fin (r * 128) → Cell) (i j : ℕ) : Cell :=
  if h : i < r ∧ j < 128 then c (pos ⟨i, h.1⟩ ⟨j, h.2⟩) else 0

/-- One level up a Merkle tree: node `i` hashes nodes `2i` and `2i + 1`. -/
def up (f : ℕ → Digest) (i : ℕ) : Digest := H (pairBytes (f (2 * i)) (f (2 * i + 1)))

/-- The root of the Merkle tree over the leaves `f 0 … f (2^d - 1)` (`tree_from_leaves`). -/
def merkleRoot : ℕ → (ℕ → Digest) → Digest
  | 0, f => f 0
  | d + 1, f => merkleRoot d (up H f)

/-- The other node of the pair of node `idx`. -/
def sibling (idx : ℕ) : ℕ := if idx % 2 = 0 then idx + 1 else idx - 1

/-- The authentication path of leaf `idx`, siblings from the bottom. -/
def merklePath : ℕ → (ℕ → Digest) → ℕ → List Digest
  | 0, _, _ => []
  | d + 1, f, idx => f (sibling idx) :: merklePath d (up H f) (idx / 2)

/-- Climb from `node` at index `idx` along the siblings `path`. -/
def walk : ℕ → Digest → List Digest → Digest
  | _, node, [] => node
  | idx, node, s :: rest =>
    walk (idx / 2) (if idx % 2 = 0 then H (pairBytes node s) else H (pairBytes s node)) rest

/-- The row tree's leaves: each padded row's digest of its first `64` cell digests. -/
def rowLeaves {r : ℕ} (c : Fin (r * 128) → Cell) (i : ℕ) : Digest :=
  H ((List.ofFn fun j : Fin 64 ↦ cellDigest H (paddedCell c i j)).flatMap Vector.toList)

/-- The column tree's leaves: leaf `j · 2^⌈log₂ r⌉ + i` is cell `j` of padded row `i`. -/
def colLeaves {r : ℕ} (c : Fin (r * 128) → Cell) (l : ℕ) : Digest :=
  cellDigest H (paddedCell c (l % nPad r) (l / nPad r))

/-- The row root (`root_row`). -/
def rowRoot {r : ℕ} (c : Fin (r * 128) → Cell) : Digest := merkleRoot H (logPad r) (rowLeaves H c)

/-- The column root (`root_col`). -/
def colRoot {r : ℕ} (c : Fin (r * 128) → Cell) : Digest :=
  merkleRoot H (7 + logPad r) (colLeaves H c)

/-- **The root of a matrix** (`commit_codewords`): `H(rowRoot ‖ colRoot)`. -/
def commitCells {r : ℕ} (c : Fin (r * 128) → Cell) : Digest :=
  H (pairBytes (rowRoot H c) (colRoot H c))

/-! ## Openings -/

/-- The opening of a cell: the row root and the cell's path in the column tree. -/
structure Opening where
  /-- The row root. -/
  rowRoot : Digest
  /-- The siblings from the cell's leaf up to the column root. -/
  path : List Digest
deriving Inhabited

/-- The column tree index of a position: cell `j` of row `i` is leaf `j · 2^⌈log₂ r⌉ + i`. -/
def colIndex {r : ℕ} (p : Fin (r * 128)) : ℕ := (posCell p : ℕ) * nPad r + posRow p

/-- The honest opening of a position. -/
def openCell {r : ℕ} (c : Fin (r * 128) → Cell) (p : Fin (r * 128)) : Opening :=
  ⟨rowRoot H c, merklePath H (7 + logPad r) (colLeaves H c) (colIndex p)⟩

/-- **Verification of a cell opening**: a path of the column tree's height that climbs from the
cell's digest to a column root, which hashed after the row root gives the commitment. -/
def verifyCell (r : ℕ) (com : Digest) (p : Fin (r * 128)) (x : Cell) (τ : Opening) : Bool :=
  decide (τ.path.length = 7 + logPad r) &&
    decide (H (pairBytes τ.rowRoot (walk H (colIndex p) (cellDigest H x) τ.path)) = com)

/-! ## Membership (`membership.rs`, `verifier/src/da.rs`) -/

/-- The normalized subspace polynomial `Ŵ_j`, vanishing on the span of `e_0 … e_(j-1)` and one
at `e_j` (CompPoly's `normalizedW`; `subspace_evaluations` tabulates it on the basis). -/
noncomputable def normW (j : Fin 14) : K[X] :=
  AdditiveNTT.normalizedW (ZMod 2) basis (Fin.castLE (by omega) j)

/-- The tensor `⊗_j (1, z_j)`: coefficient `u` is the product of the `z_j` over the bits of `u`
(`dual_codeword`'s first loop). -/
def tensor (z : Fin 14 → E) (u : Fin (2 ^ 14)) : E :=
  ∏ j : Fin 14, if (u : ℕ).testBit j then z j else 1

/-- **The dual codeword of challenges `z`** (`dual_codeword`): `L(x) = ∏_j (1 + z_j Ŵ_j(x))` on
the domain, the encoding of `tensor z` (`dual_eq_encode_tensor`). -/
noncomputable def dual (z : Fin 14 → E) (b : Fin (2 ^ 15)) : E :=
  ∏ j : Fin 14, (1 + z j * ι ((normW j).eval (point b)))

/-- The inner product of the dual codeword with a row: `Σ_x L(x) w(x)` (`check_membership`). -/
noncomputable def dot (L : Fin (2 ^ 15) → E) (w : Row) : E := ∑ b, L b * ι (w b)

/-- **The membership check**: every row is orthogonal to the dual codeword. -/
noncomputable def membershipCheck {r : ℕ} (z : Fin 14 → E) (c : Fin (r * 128) → Cell) : Bool :=
  decide (∀ i : Fin r, dot (dual z) (rowOf c i) = 0)

/-! ## The deployed commitment (`commit.rs:55-145`)

The commitment as the crate computes it, on codewords given as lists of symbols: the leaves in
the crate's order, each tree built level by level. It is `commitCells` of the matrix the rows
form (`commitCodewords_eq_commitCells`, `LeanDa.Commitment`). -/

/-- One level of a Merkle tree: the digests of neighbouring pairs (`tree_from_leaves`). -/
def treeLevel (nodes : List Digest) : List Digest :=
  (List.range (nodes.length / 2)).map (up H fun i ↦ nodes.getD i default)

/-- The root of the Merkle tree over a power-of-two number of digests (`tree_from_leaves`; on
other lengths, which `commitCodewords` never passes, the crate panics). -/
def treeRoot (nodes : List Digest) : Digest :=
  if nodes.length ≤ 1 then nodes.headD default else treeRoot (treeLevel H nodes)
termination_by nodes.length
decreasing_by simp only [treeLevel, List.length_map, List.length_range]; omega

/-- Cell `j` of a codeword. -/
def listCell (row : List K) (j : ℕ) : List K := (row.drop (j * cellSymbols)).take cellSymbols

/-- The digest of cell `j` of a codeword (`hash_cells`). -/
def listCellDigest (row : List K) (j : ℕ) : Digest := H ((listCell row j).flatMap kBytes)

/-- A row's digest: the hash of its payload cells' digests. -/
def rowDigest (row : List K) : Digest :=
  H ((List.range payloadCells).flatMap fun j ↦ (listCellDigest H row j).toList)

/-- The digest of the zero cell, which pads the columns (`padding_digests`). -/
def paddingCell : Digest := H ((List.replicate cellSymbols 0).flatMap kBytes)

/-- The digest of the zero row, which pads the row tree (`padding_digests`). -/
def paddingRow : Digest := H ((List.replicate payloadCells (paddingCell H)).flatMap Vector.toList)

/-- **The root of a matrix of codewords, as the crate computes it** (`commit_codewords`): the
rows padded to a power of two, the hash of the row tree's root and the column tree's. -/
def commitCodewords (rows : List (List K)) : Digest :=
  let n := nPad rows.length
  let rowTree := treeRoot H
    (rows.map (rowDigest H) ++ List.replicate (n - rows.length) (paddingRow H))
  let columnTree := treeRoot H ((List.range cellsPerRow).flatMap fun j ↦ (List.range n).map fun i ↦
    if h : i < rows.length then listCellDigest H rows[i] j else paddingCell H)
  H (pairBytes rowTree columnTree)

/-- The cells of the matrix whose rows are `rows`: cell `j` of row `i` at position `128 i + j`. -/
def cellsOfRows (rows : List (List K)) : Fin (rows.length * 128) → Cell :=
  fun p s ↦ (rows.getD (p / 128) []).getD (256 * (p % 128) + s) 0

/-! ## The deployed membership vector (`verifier/src/da.rs:14-101`)

The challenges, drawn from the root by the BLAKE2s chain the security game models as a random
oracle, and the dual codeword as the crate computes it, by the additive NTT. That the NTT computes
`dual` is not proved here (Annex D, Proposition prop:ntt). -/

/-- `leanDA/rs-membership/v1`, the label of the challenges' transcript (`LABEL`). -/
def label : List UInt8 := "leanDA/rs-membership/v1".toUTF8.toList

/-- The symbol of eight little-endian bytes (`u64::from_le_bytes`). -/
def ofBytes (bytes : List UInt8) : K := K.ofBits (bytes.foldr (fun b acc ↦ b.toNat + 256 * acc) 0)

/-- Word `i` of a digest, its bytes `8 i … 8 i + 7` (`Hash::words`). -/
def word (d : Digest) (i : ℕ) : K := ofBytes ((d.toList.drop (8 * i)).take 8)

/-- The element `c0 + c1·y + c2·y²` (`E::new`). -/
def ofLimbs (c0 c1 c2 : K) : E := CompPoly.Extension.Ext.ofVector #v[c0, c1, c2]

/-- Limb `i` of an element, the coefficient of `y^i`. -/
def limb (x : E) (i : Fin 3) : K := CompPoly.Extension.Ext.coeff x i

/-- A transcript step: the hash of the state's bytes and four words' (`transcript.rs:37-44`,
`compress`). -/
def compressWords (state : Digest) (words : List K) : Digest := H (state.toList ++ words.flatMap kBytes)

/-- `n` challenges squeezed from the state (`sample`, tag `DS_SQUEEZE = 2`). -/
def squeezes : ℕ → Digest → List E
  | 0, _ => []
  | n + 1, state =>
    let state := compressWords H state [0, 0, 0, K.ofBits 2]
    ofLimbs (word state 0) (word state 1) (word state 2) :: squeezes n state

/-- **The challenges `z_0 … z_13` of a root** (`membership_challenges`): from the label's hash,
the root's two halves observed (tag `DS_OBSERVE = 1`), then `14` squeezes. -/
def membershipChallenges (root : Digest) : List E :=
  let state := H label
  let state := compressWords H state [word root 0, word root 1, 0, K.ofBits 1]
  let state := compressWords H state [word root 2, word root 3, 0, K.ofBits 1]
  squeezes H logK state

/-- Row `i` of the subspace evaluations before scaling: `s_i` at the basis elements `x^j`,
`j ≥ i`. -/
def subspaceRow : ℕ → List K
  | 0 => (List.range logM).map fun j ↦ K.ofBits (2 ^ j)
  | i + 1 =>
    let previous := subspaceRow i
    (previous.drop 1).map fun value ↦ value * (value + previous.headD 0)

/-- Row `i` of the subspace evaluations, scaled so that its first entry is one
(`subspace_evaluations`). -/
def subspaceEvaluations (i : ℕ) : List K :=
  (subspaceRow i).map (· * ((subspaceRow i).headD 0)⁻¹)

/-- One butterfly block: `u += v·t`, then `v += u`. -/
def butterfly (twiddle : K) (block : List E) : List E :=
  let top := block.take (block.length / 2)
  let bottom := block.drop (block.length / 2)
  let top := List.zipWith (fun u v ↦ u + v * CompPoly.Extension.Ext.ofBase twiddle) top bottom
  top ++ List.zipWith (· + ·) bottom top

/-- Layer `layer` of the additive NTT: blocks of `2^(logM - layer)` points, block `b`'s twiddle
the subset sum of the row's entries that `b`'s bits pick. -/
def encodeLayer (layer : ℕ) (codeword : List E) : List E :=
  let row := (subspaceEvaluations (logM - layer - 1)).drop 1
  let size := 2 ^ (logM - layer)
  (List.range (codeword.length / size)).flatMap fun b ↦
    let twiddle := ((List.range layer).filter b.testBit).foldl (fun t bit ↦ t + row.getD bit 0) 0
    butterfly twiddle ((codeword.drop (b * size)).take size)

/-- The codeword of the `2^14` novel-basis coefficients `message`: the message twice, then the
layers `1 … 14` (`encode`). -/
def encode (message : List E) : List E :=
  (List.range' 1 (logM - 1)).foldl (fun codeword layer ↦ encodeLayer layer codeword)
    (message ++ message)

/-- The dual codeword, the tensor of the `(1, z_j)` encoded (`dual_codeword`). -/
def dualCodeword (z : List E) : List E :=
  encode (z.foldl (fun t challenge ↦ t ++ t.map (· * challenge)) [1])

/-- **The membership vector of a root** (`membership_vector`). -/
def membershipVector (root : Digest) : List E := dualCodeword (membershipChallenges H root)

/-- The hash of a vector's limbs, three little-endian symbols an entry (`vector_digest`). -/
def vectorDigest (vector : List E) : Digest :=
  H ((vector.flatMap fun e ↦ [limb e 0, limb e 1, limb e 2]).flatMap kBytes)

end

end LeanDa
