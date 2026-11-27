module

public import Statement.Field
public import Statement.Verifier.Transcript
public import Statement.RandomPermutation
public import CompPoly.Fields.Binary.AdditiveNTT.NovelPolynomialBasis
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.LinearAlgebra.Lagrange

/-!
# LeanDA

LeanDA as `crates/lean_da` computes it, and what it guarantees in the random-permutation model:
its commitment is complete and position binding, and its membership test is sound.

**Credit.** The notions these statements come from are Benedikt Wagner's framework for erasure
code commitments, https://github.com/b-wagn/fv-pq-da (his post:
https://ethresear.ch/t/formally-verified-security-for-pq-das-leanda/25746), under the Apache
License 2.0. Position binding is his vector commitment's. The membership test's soundness is his
committed soundness, the non-interactive game of his code-binding proof (the adversary outputs a
commitment and a vector, and wins if the vector is not a codeword, passes the code check on the
randomness derived from the commitment, and commits to it); the grind and the bound are LeanDA's.
Both are moved to the random-permutation model and proved in `lean_da`, on the definitions of his
that it keeps (`lean_da/PqDas/Defs.lean`, `lean_da/NOTICE`); his theorems and proofs are in his
repository. His code binding composes them with an argument of knowledge for the relation. It is
not stated here: the deployed argument is leanVM, whose relation is over the deployed
Keccak-f[1600], not `relationWith` over the model's permutation, so it cannot be that argument.

The file: LeanDA (`LeanDa`: the code, the commitment, the membership test, the deployed
algorithms), its relation (the root's challenge drawn by the deployed duplex), the games in the
random-permutation model (the hash Keccak-256 over `π`, the membership challenge the deployed
duplex over `π`; no random oracle, no argument), and the end statements (last section).
-/

@[expose] public section

open Polynomial OracleComp ENNReal Common

/-! ## LeanDA's fields -/

namespace LeanDa

export LeanVM.Parameters (K E K.ofBits K.ofLane K.lane)
open LeanVM.Parameters (E.toBytes)
open LeanVM.Semantics (KeccakState)
open LeanVM.Protocol (Digest)
open LeanVM.Protocol.KeccakHash (keccak256With digestBytes)
open LeanVM.Protocol.Compile (Sponge absorbNonce squeeze seedInput climb)

/-- An enumeration of `K` through its bits, for proofs only: compiled, it would list `2^64`
elements when a program starts. -/
noncomputable instance : Fintype K := Fintype.ofEquiv (Fin (2 ^ 64)) BF64.equivFin.symm

/-- `K` is a `GF(2)`-algebra, being of characteristic two. -/
instance : Algebra (ZMod 2) K := ZMod.algebra K 2

/-- The embedding `K ↪ E` as the `y^0` limb. -/
abbrev ι : K →+* E := algebraMap K E

/-- The point of index `b` of an additive domain: `Σ_c b_c e_c` with `e_c = x^c`. -/
def point (b : ℕ) : K := K.ofBits b

/-- `e_c = x^c` for `c < 16`, the start of the basis of Annex D. -/
def basis (c : Fin 16) : K := K.ofBits (2 ^ (c : ℕ))

/-!
## LeanDA

The erasure code commitment of `crates/lean_da`,
specified in `doc/leanvm/body/10-ethereum.tex`
§sec:leanda, for a matrix of `r` rows.

* **The code** (`encode.rs`). A row's payload is `2^13` symbols of `E`, the evaluations on the
  domain points `0 … 2^13 - 1` (in `K`) of the polynomial of `E[X]` of degree below `2^13` they
  determine. Its codeword is that polynomial's evaluations on all `2^14` points (`encodeRow`): the
  inverse additive NTT interpolates, the forward one evaluates, so the payload is the codeword's
  first half. The points and the novel basis lie in `K`, so the crate runs both transforms on the
  symbols' two limbs apart, as two lanes. The transforms compute these maps (Annex D, Proposition
  prop:ntt); they are not transcribed here.
* **Cells** (`lib.rs`). A codeword is `128` cells of `128` symbols; cell `j` of row `i` is at
  position `128 i + j`, the positions of the erasure code commitment.
* **The commitment** (`commit.rs`). The rows are padded to `maxRows` with zero codewords. A
  cell's digest is the hash of its symbols' bytes, each symbol its two limbs' little-endian bytes,
  `y^0` first (`blob_merkle_nodes`). Each
  padded row, a blob, has the Merkle root of its `128` cell digests (`blobRootWith`), a padding
  row's that of the zero codeword (`root_of_padding_blob`). A tree hashes neighbours in pairs, level
  by level (`fill_levels`). The commitment hashes the root of the tree over the padded rows' blob
  roots with the row count, a 32-byte little-endian word (`BlobMatrix::commitment`, `mix_in_count`,
  `countDigest`).
* **Openings.** A cell is opened by its authentication path in its blob's tree, then its blob
  root's in the tree over the blob roots: the path of leaf `128 i + j` in the one tree of depth
  `7 + logMaxRows` that the two make (`BlobMatrix::merkle_path_for_cell`, `openCellWith`), checked
  by `verify_cell` (`verifyCellWith`), which climbs it and then hashes in the row count.
* **Membership** (`verifier/src/da.rs`, the guest program's `da_vector`). One challenge `z ∈ E` gives
  the dual codeword `L(x) = ∏_j (1 + z^(2^j) Ŵ_j(x))` on the domain (Annex D, eq. dual-product,
  at the challenges `z^(2^j)`), with `Ŵ_j` the normalized subspace polynomial of the span of
  `e_0 … e_(j-1)`. A matrix passes when every row is orthogonal to `L` (the guest program's
  `da_verify`). The challenge is drawn
  from the root by leanVM's transcript (`membership_challenge`, `verifier/src/da.rs`): its
  sponge over Keccak-f[1600] seeded with the label's hash as its IV and the root as its public
  input (`verifier/src/transcript.rs`, `Verifier/Transcript.lean`'s `Sponge`), then a `10`-bit grind
  whose nonce is the smallest valid one, not sent, and the ground challenge it draws
  (`absorbNonce`, `transcript.rs`); the end statements draw it by this duplex over the
  permutation (`membershipChallengeWith`). A root none of whose `2^64` nonces is valid has no
  challenge (the Rust search never ends); the relation then asks every row to be a codeword
  (`membershipCheckOpt`), which keeps an honest matrix's relation true for every function `π`.

The row count `r` is a parameter: the crate takes `1 ≤ r ≤ maxRows` (`BlobMatrix::build` rejects any
other count with a `BlobCountError`, `commit.rs`, `lib.rs`);
position binding holds for every `r`, completeness for `r ≤ maxRows`, the membership test's
soundness for `r ≤ maxRows`. The algorithms take a permutation `π` of the Keccak state as a parameter and hash with
Keccak-256 over it (`keccak256With`, the hash `H` below): the crate's is Keccak-f[1600], the
hash Keccak-256 (`verifier/src/hash.rs`); in the end statements `π` is the random
permutation. A digest is leanVM's (`Digest`, four 64-bit words), hashed and climbed as its 32
little-endian bytes (`digestBytes`, `fiat_shamir_prover::merkle::Hash`).
-/

/-! ### Shapes (`lib.rs`) -/

/-- Payload symbols per row, as a logarithm (`LOG_BLOB_SYMBOLS`). -/
def logK : ℕ := 13

/-- Codeword symbols per row, as a logarithm: rate one half (`LOG_CODEWORD_SYMBOLS`). -/
def logM : ℕ := 14

/-- Symbols per cell (`CELL_SYMBOLS`). -/
def cellSymbols : ℕ := 128

/-- Cells per codeword (`CELLS_PER_ROW`). -/
def cellsPerRow : ℕ := 128

/-- The log of the most rows the crate commits to (`DA_MAX_ROWS.ilog2()`). -/
def logMaxRows : ℕ := 5

/-- The most rows the crate commits to (`DA_MAX_ROWS`), a power of two. -/
def maxRows : ℕ := 2 ^ logMaxRows

/-- A row's payload: symbols of `E` (`Symbol`, a 128-bit word whose low and high halves are the
limbs `c0`, `c1` of `c0 + c1·y`). -/
abbrev Payload := Fin (2 ^ 13) → E

/-- A codeword, in domain order. -/
abbrev Row := Fin (2 ^ 14) → E

/-- A sampling cell. -/
abbrev Cell := Fin 128 → E

/-! ### The code (`encode.rs`) -/

/-- The polynomial of `E[X]` of degree below `2^13` taking the payload's values on the points
`0 … 2^13 - 1` (`inverse_transform`, on each limb). -/
noncomputable def interpolate (p : Payload) : E[X] :=
  Lagrange.interpolate Finset.univ (fun a : Fin (2 ^ 13) ↦ ι (point a)) p

/-- **The systematic encoding of a payload** (`encode_rows`): its polynomial's values on all
`2^14` points (`encode_interleaved_in_place`, on each limb). -/
noncomputable def encodeRow (p : Payload) : Row := fun b ↦ (interpolate p).eval (ι (point b))

/-- Cell `j` of a codeword: its symbols `128 j … 128 j + 127`. -/
def rowCell (row : Row) (j : Fin 128) : Cell := fun s ↦ row ⟨128 * j + s, by omega⟩

/-- The position of cell `j` of row `i`. -/
def cellPosition {r : ℕ} (i : Fin r) (j : Fin 128) : Fin (r * 128) := ⟨128 * i + j, by omega⟩

/-- The row of a position. -/
def positionRow {r : ℕ} (p : Fin (r * 128)) : Fin r := ⟨p / 128, by omega⟩

/-- The cell of a position within its row. -/
def positionCell {r : ℕ} (p : Fin (r * 128)) : Fin 128 := ⟨p % 128, by omega⟩

/-- The cells of a matrix of encoded payloads. -/
noncomputable def encodeMatrix {r : ℕ} (message : Fin r → Payload) : Fin (r * 128) → Cell :=
  fun p ↦ rowCell (encodeRow (message (positionRow p))) (positionCell p)

/-- Row `i` of a matrix given by its cells. -/
def matrixRow {r : ℕ} (cells : Fin (r * 128) → Cell) (i : Fin r) : Row :=
  fun b ↦ cells (cellPosition i ⟨b / 128, by omega⟩) ⟨b % 128, by omega⟩

/-- The cells of the matrix whose rows are `rows`, codewords as lists of symbols: cell `j` of row
`i` at position `128 i + j`. -/
def cellsOfRows (rows : List (List E)) : Fin (rows.length * 128) → Cell :=
  fun p s ↦ (rows.getD (p / 128) []).getD (128 * (p % 128) + s) 0

/-! ### The commitment (`commit.rs`)

The commitment, the openings and their check, and the membership challenge over a permutation `π`
in any monad, the hash Keccak-256 over `π`: the games' oracles, or over `Id` the deployed
algorithms (`commitCells`, `openCell`). -/

/-- A cell's bytes: its symbols' sixteen bytes in order, each symbol its two limbs' little-endian
bytes, `y^0` first (`as_bytes`). -/
def cellBytes (cell : Cell) : List UInt8 := (List.ofFn cell).flatMap E.toBytes

/-- The row count as the commitment hashes it: a 32-byte little-endian word (`mix_in_count`), as
the digest of those bytes. -/
def countDigest (r : ℕ) : Digest := Vector.ofFn fun i : Fin 4 ↦ UInt64.ofNat (r / 2 ^ (64 * (i : ℕ)))

/-- Cell `j` of row `i` of the matrix padded to `maxRows` rows: zero below the `r` rows. -/
def paddedCell {r : ℕ} (cells : Fin (r * 128) → Cell) (i j : ℕ) : Cell :=
  if h : i < r ∧ j < 128 then cells (cellPosition ⟨i, h.1⟩ ⟨j, h.2⟩) else 0

/-- The other node of the pair of node `index`. -/
def sibling (index : ℕ) : ℕ := if index % 2 = 0 then index + 1 else index - 1

/-- The opening of a cell: its path in its blob's tree, then its blob root's in the tree over the
blob roots. -/
structure CellOpening where
  /-- The siblings from the cell's leaf up to the commitment, `7 + logMaxRows` of them (`MERKLE_PATH_LEN`). -/
  path : List Digest
deriving Inhabited

/-- `leanDA/rs-membership/v1`, the label of the challenge's transcript (`LABEL`). -/
def membershipLabel : List UInt8 := "leanDA/rs-membership/v1".toUTF8.toList

section Monadic

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

/-- One level up a Merkle tree: node `i` hashes nodes `2i` and `2i + 1`, their 64 bytes
(`hash_pair`, `fill_levels`). -/
def merkleLevelUpWith (nodeAt : ℕ → m Digest) (i : ℕ) : m Digest := do
  let a ← nodeAt (2 * i)
  let b ← nodeAt (2 * i + 1)
  keccak256With π (digestBytes a ++ digestBytes b)

/-- The root of the Merkle tree over the leaves `nodeAt 0 … nodeAt (2^d - 1)`
(`merkle_nodes_from_leaves`, `fill_levels`). -/
def merkleRootWith : ℕ → (ℕ → m Digest) → m Digest
  | 0, nodeAt => nodeAt 0
  | d + 1, nodeAt => merkleRootWith d (merkleLevelUpWith π nodeAt)

/-- The authentication path of leaf `index`, siblings from the bottom. -/
def merklePathWith : ℕ → (ℕ → m Digest) → ℕ → m (List Digest)
  | 0, _, _ => pure []
  | d + 1, nodeAt, index => do
    let s ← nodeAt (sibling index)
    let rest ← merklePathWith d (merkleLevelUpWith π nodeAt) (index / 2)
    pure (s :: rest)

/-- The leaves of padded row `i`'s tree: its `128` cell digests, `e_{i,j} = H(W_{i,j})`
(`blob_merkle_nodes`). -/
def cellLeavesWith {r : ℕ} (cells : Fin (r * 128) → Cell) (i j : ℕ) : m Digest :=
  keccak256With π (cellBytes (paddedCell cells i j))

/-- **The blob root of padded row `i`**: the Merkle root of its cell digests (`blob_merkle_nodes`; a
padding row's is `root_of_padding_blob`). -/
def blobRootWith {r : ℕ} (cells : Fin (r * 128) → Cell) (i : ℕ) : m Digest :=
  merkleRootWith π 7 (cellLeavesWith π cells i)

/-- **The commitment to a matrix** (`BlobMatrix::commitment`): the Merkle root of the padded rows'
blob roots, hashed with the row count (`mix_in_count`). -/
def commitCellsWith {r : ℕ} (cells : Fin (r * 128) → Cell) : m Digest := do
  let tree ← merkleRootWith π logMaxRows (blobRootWith π cells)
  keccak256With π (digestBytes tree ++ digestBytes (countDigest r))

/-- The honest opening of a position (`BlobMatrix::merkle_path_for_cell`): the cell's path in its blob's tree, then
its blob root's in the tree over the blob roots. -/
def openCellWith {r : ℕ} (cells : Fin (r * 128) → Cell) (p : Fin (r * 128)) : m CellOpening := do
  let low ← merklePathWith π 7 (cellLeavesWith π cells (positionRow p)) (positionCell p)
  let high ← merklePathWith π logMaxRows (blobRootWith π cells) (positionRow p)
  pure ⟨low ++ high⟩

/-- **Verification of a cell opening** (`verify_cell`): a path of `7 + logMaxRows` siblings, then
the row count's word, climbs (`climb`, the verifier's Merkle climb) from the cell's digest, at index
`128 i + j` (the position: `j` in its blob's tree, then `i` in the tree over the blob roots), to the
commitment. For `r ≤ maxRows` rows the last step is at index `0`, the crate's `mix_in_count`. The
crate also refuses `r > maxRows` rows. -/
def verifyCellWith (r : ℕ) (commitment : Digest) (position : Fin (r * 128)) (cell : Cell)
    (opening : CellOpening) : m Bool := do
  let d ← keccak256With π (cellBytes cell)
  let root ← climb π d position (opening.path ++ [countDigest r])
  pure (decide (opening.path.length = 7 + logMaxRows) && decide (root = commitment))

/-! ### The membership challenge (`verifier/src/da.rs`)

Drawn from the root by the duplex sponge of the leanVM verifier (`Verifier/Transcript.lean`: `Sponge`,
`seedInput`, `absorbNonce`, `squeeze`), over the permutation `π`
(`verifier/src/transcript.rs`), after a grind whose nonce is not sent: the smallest valid
one, which anyone deriving the challenge finds. -/

/-- `MEMBERSHIP_GRINDING_BITS` (`verifier/src/da.rs`): `grinding_bits(2^13 - 1)`, the bits
that bring the membership test's error `(2^13 - 1) / 2^128` to `2^-125`,
`⌈log₂ (2^13 - 1)⌉ - (128 - 125) = 10` (`transcript.rs`). -/
def membershipGrindingBits : ℕ := 10

/-- A nonce's proof of work is valid when its low `membershipGrindingBits` bits are zero
(`& mask == 0`, `verifier/src/da.rs`). -/
def powValid (pow : UInt64) : Bool := pow.toNat % 2 ^ membershipGrindingBits = 0

/-- The nonces the search tries: the `u64` values (`E::new(nonce, 0)`, `verifier/src/da.rs`). -/
def nonceCount : ℕ := 2 ^ 64

section Search

variable (sponge : Sponge)

/-- **The nonce search** from `nonce`, `fuel` nonces left (`verifier/src/da.rs`): absorb the
nonce into a copy of the seeded sponge and permute (`absorbNonce`); a valid proof of work stops
the search with the ground challenge (`squeeze`). Past the last nonce the Rust search never ends
(`(0..)` over `u64`, wrapping): there is no challenge (`none`). -/
def grindWith : ℕ → ℕ → m (Option E)
  | _, 0 => pure none
  | nonce, fuel + 1 => do
    let (pow, ground) ← absorbNonce π sponge (LeanVM.Protocol.Verifier.eOfNat nonce)
    if powValid pow then
      let (z, _) ← squeeze π ground
      pure (some z)
    else grindWith (nonce + 1) fuel

end Search

/-- **The challenge `z` of a root** (`membership_challenge`, `verifier/src/da.rs`): the
transcript's sponge seeded with the label's hash as its IV and the root as its public input
(`Sponge::new`), then the challenge of the smallest nonce `0, 1, …` whose proof of work is valid
(`grindWith`), or none if no `u64` nonce is valid. -/
def membershipChallengeWith (root : Digest) : m (Option E) := do
  let iv ← keccak256With π membershipLabel
  let state ← π (seedInput iv root)
  grindWith π ⟨state, [], none⟩ 0 nonceCount

end Monadic

/-- **The commitment to a matrix** over a permutation `π` (`commitCellsWith` over `Id`). -/
def commitCells (π : KeccakState → KeccakState) {r : ℕ} (cells : Fin (r * 128) → Cell) :
    Digest :=
  Id.run (commitCellsWith (fun x ↦ pure (π x)) cells)

/-- The honest opening of a position over a permutation `π` (`openCellWith` over `Id`). -/
def openCell (π : KeccakState → KeccakState) {r : ℕ} (cells : Fin (r * 128) → Cell)
    (p : Fin (r * 128)) : CellOpening :=
  Id.run (openCellWith (fun x ↦ pure (π x)) cells p)

/-! ### Membership (`verifier/src/da.rs`, the guest program's `da_vector`) -/

/-- The normalized subspace polynomial `Ŵ_j`, vanishing on the span of `e_0 … e_(j-1)` and one
at `e_j` (CompPoly's `normalizedW`; `vhat` in `aggregation`'s `placeholders.rs` tabulates it, the NTT's twiddles). -/
noncomputable def normalizedSubspacePolynomial (j : Fin 13) : K[X] :=
  AdditiveNTT.normalizedW (ZMod 2) basis (Fin.castLE (by omega) j)

/-- **The dual codeword of the challenge `z`** (the guest program's
`da_vector`): `L(x) = ∏_j (1 + z^(2^j) Ŵ_j(x))` on the domain. -/
noncomputable def dualCodewordAt (z : E) (b : Fin (2 ^ 14)) : E :=
  ∏ j : Fin 13, (1 + z ^ 2 ^ (j : ℕ) * ι ((normalizedSubspacePolynomial j).eval (point b)))

/-- The inner product of the dual codeword with a row: `Σ_x L(x) row(x)` (the guest program's `da_verify`). -/
noncomputable def innerProduct (L : Fin (2 ^ 14) → E) (row : Row) : E := ∑ b, L b * row b

/-- **The membership check**: every row is orthogonal to the dual codeword of `z`. -/
noncomputable def membershipCheck {r : ℕ} (z : E) (cells : Fin (r * 128) → Cell) : Bool :=
  decide (∀ i : Fin r, innerProduct (dualCodewordAt z) (matrixRow cells i) = 0)

/-- **The membership check of a root's challenge**: the check on the challenge, or, for a root
with no valid nonce (where the deployed verifier never returns), the check on every challenge,
which only codewords pass. -/
noncomputable def membershipCheckOpt {r : ℕ} (z : Option E) (cells : Fin (r * 128) → Cell) : Bool :=
  match z with
  | some z => membershipCheck z cells
  | none => @decide (∀ z : E, membershipCheck z cells = true) (Classical.propDecidable _)

/-! ## The relation: a matrix commits to a root and passes the root's membership test -/

/-- **A matrix of codewords**: the cells of `r` encoded payloads. -/
def IsCodewordMatrix {r : ℕ} (cells : Fin (r * 128) → Cell) : Prop :=
  ∃ message : Fin r → Payload, cells = encodeMatrix message

/-- **LeanDA's relation**, over a permutation `π` in any monad: the cells commit to the root and
pass the membership test on the root's challenge, drawn by the deployed duplex
(`membershipChallengeWith`), the hash Keccak-256 over `π`. In the games `π` is the model's
(`queryPermutation`). -/
noncomputable def relationWith {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState) {r : ℕ}
    (root : Digest) (cells : Fin (r * 128) → Cell) : m Bool := do
  let z ← membershipChallengeWith π root
  let d ← commitCellsWith π cells
  pure (decide (d = root) && membershipCheckOpt z cells)

/-! ## The games in the random-permutation model

The adversary queries coins, `π` and `π⁻¹` (`RandomPermutationOracles`), and LeanDA's verifier
hashes with Keccak-256 over `π` (`keccak256With queryPermutation`). A game is run against the
lazily sampled permutation (`runWithRandomPermutation`). No argument system appears: these are the
guarantees of LeanDA's commitment and of its membership test. An argument that proves the relation
with knowledge, over the same `π`, composes them into Wagner's code binding, which is not stated
here; leanVM's, whose relation uses the deployed Keccak-f[1600], does not. -/

/-- A position-binding adversary: a commitment, a position, and two cells with their openings. -/
abbrev PositionBindingAdversary (r : ℕ) :=
  OracleComp RandomPermutationOracles
    (Digest × Fin (r * 128) × Cell × CellOpening × Cell × CellOpening)

/-- **The position-binding game**: the adversary, then the two openings' verifications; it wins
when both verify, at two different cells. -/
def positionBindingGame (r : ℕ) (adversary : PositionBindingAdversary r) :
    OracleComp RandomPermutationOracles Bool := do
  let (commitment, position, cell, opening, cell', opening') ← adversary
  let b ← verifyCellWith queryPermutation r commitment position cell opening
  let b' ← verifyCellWith queryPermutation r commitment position cell' opening'
  pure (decide (cell ≠ cell') && b && b')

/-- A membership adversary: a root and a matrix. -/
abbrev MembershipAdversary (r : ℕ) :=
  OracleComp RandomPermutationOracles (Digest × (Fin (r * 128) → Cell))

/-- **The membership game**: the adversary, then the relation's check of its root and matrix
(`relationWith` over `π`: the commitment and the membership test on the root's challenge); the
verdict and the matrix. -/
noncomputable def membershipGame (r : ℕ) (adversary : MembershipAdversary r) :
    OracleComp RandomPermutationOracles (Bool × (Fin (r * 128) → Cell)) := do
  let (root, cells) ← adversary
  let accepted ← relationWith queryPermutation root cells
  pure (accepted, cells)

/-! ### The end statements -/

/-- **LeanDA is complete, for every function `π`.** For at most `maxRows` rows and every function
`π` on the Keccak state, the hash Keccak-256 over `π`: every position of the commitment to a matrix
opens and verifies, and the matrix of encoded payloads satisfies the relation at its commitment
(it passes the membership test on its root's challenge, whatever that is). No probability: holding
for each `π`, it holds for every outcome of the binding statements' random permutation. Proved by
`LeanDa.leanDa_complete`. -/
abbrev LeanDaComplete : Prop :=
  ∀ (r : ℕ) (π : KeccakState → KeccakState), r ≤ maxRows →
    (∀ (cells : Fin (r * 128) → Cell) (position : Fin (r * 128)),
      Id.run (verifyCellWith (fun x ↦ pure (π x)) r (commitCells π cells) position (cells position)
        (openCell π cells position)) = true) ∧
    ∀ message : Fin r → Payload,
      Id.run (relationWith (fun x ↦ pure (π x)) (commitCells π (encodeMatrix message))
        (encodeMatrix message)) = true

/-- **LeanDA is position binding in the random-permutation model.** For every adversary whose game,
the two verifications included, makes at most `Q` calls of `π` and `π⁻¹` on every path
(`permutationCallCost`; a hash of `n` bytes, Keccak-256 over `π`, makes `⌊n / 136⌋ + 1`), the
probability of opening a position to two different cells is at most `(Q + 1)² · 2^-256`, for every
`Q` (past `2^128` the bound exceeds one). Proved by `LeanDa.leanDa_positionBinding_rpm`. -/
abbrev LeanDaPositionBinding : Prop :=
  ∀ (r : ℕ) (adversary : PositionBindingAdversary r) (Q : ℕ),
    QueryCostAtMost (positionBindingGame r adversary) permutationCallCost Q →
      Pr{let b ← runWithRandomPermutation (positionBindingGame r adversary)}[b = true] ≤
        ((Q : ℝ≥0∞) + 1) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256

/-- **LeanDA's membership test is sound in the random-permutation model** (Wagner's committed
soundness, with LeanDA's grind): for at most `maxRows` rows and every adversary that itself makes
at most `Q` calls of `π` and `π⁻¹` on every path (the relation's check, the game's, is not
charged), its matrix satisfies the relation at its root and yet is not a matrix of codewords with
probability at most `(Q + 2^10) · 2^-125 + (Q + 2^19)² · 2^-247` (`statement.tex` explains both
terms). Proved by `LeanDa.leanDa_membershipSound_rpm`. -/
abbrev LeanDaMembershipSound : Prop :=
  ∀ (r : ℕ), r ≤ maxRows → ∀ (adversary : MembershipAdversary r) (Q : ℕ),
    QueryCostAtMost adversary permutationCallCost Q →
      Pr{let out ← runWithRandomPermutation (membershipGame r adversary)}[
          out.1 = true ∧ ¬ IsCodewordMatrix out.2] ≤
        ((Q : ℝ≥0∞) + 2 ^ 10) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
          ((Q : ℝ≥0∞) + 2 ^ 19) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 247

end LeanDa

end
