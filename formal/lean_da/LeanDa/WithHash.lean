module

public import Statement.LeanDa
public import Common.WithHash

/-!
# LeanDA with a hash of its own

The statement's LeanDA (`Statement/LeanDa.lean`) hashes with Keccak-256 over the permutation it is
given (`LeanDa.keccakDigestBytes`). Benedikt Wagner's framework and its proofs reason with the hash
a parameter of its own, `H`, beside the sponge's permutation `P`: these are LeanDA's algorithms in
that form, each the statement's definition with the hash a parameter (the commitment, the openings,
the membership challenge's duplex, the relation), and LeanDA's games and end
statements with the hash Keccak-256 over `π` as a call of its own (`keccak256OverPermutation`).
`LeanDa.WithHashBridge` proves the statement's these with the hash Keccak-256 over the permutation.

The framework, the games and the end statements are Benedikt Wagner's
(https://github.com/b-wagn/fv-pq-da, Apache-2.0, `lean_da/NOTICE`), moved to the
random-permutation model.
-/

@[expose] public section

open Polynomial OracleComp OracleSpec ENNReal Common MeasureTheory

set_option linter.unusedSectionVars false

namespace LeanDa

open PqDas
open LeanVM.Parameters (K.toBytes E.toBytes)
open LeanVM.Semantics (KeccakState)
open LeanVM.Protocol.KeccakHash (keccak256With littleEndianLane)

/-! ## The challenge's sponge as the proofs read it

`lean_da`'s proofs read the membership challenge's duplex (`verifier/src/transcript.rs:34-90`)
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

/-- `DS_POW_NONCE`, the tag of a grinding nonce (`transcript.rs:18`). -/
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
(`membership_challenge`, `verifier/src/da.rs:28-33`): the first nonce whose answer's lane `2` has
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
def listCell (row : List K) (j : ℕ) : List K := (row.drop (j * cellSymbols)).take cellSymbols

section Pure

variable (H : List UInt8 → DigestBytes)

/-- The digest of a cell (`hash_cells`). -/
def cellDigestWithHash (x : Cell) : DigestBytes := H (cellBytes x)

/-- One level up a Merkle tree: node `i` hashes nodes `2i` and `2i + 1`. -/
def upWithHash (f : ℕ → DigestBytes) (i : ℕ) : DigestBytes :=
  H (pairBytes (f (2 * i)) (f (2 * i + 1)))

/-- The root of the Merkle tree over the leaves `f 0 … f (2^d - 1)` (`tree_from_leaves`). -/
def merkleRootWithHash : ℕ → (ℕ → DigestBytes) → DigestBytes
  | 0, f => f 0
  | d + 1, f => merkleRootWithHash d (upWithHash H f)

/-- The authentication path of leaf `idx`, siblings from the bottom. -/
def merklePathWithHash : ℕ → (ℕ → DigestBytes) → ℕ → List DigestBytes
  | 0, _, _ => []
  | d + 1, f, idx => f (sibling idx) :: merklePathWithHash d (upWithHash H f) (idx / 2)

/-- The leaves of padded row `i`'s tree: its `128` cell digests (`blob_trees`). -/
def cellLeavesWithHash {r : ℕ} (c : Fin (r * 128) → Cell) (i j : ℕ) : DigestBytes :=
  cellDigestWithHash H (paddedCell c i j)

/-- The blob root of padded row `i`: the Merkle root of its cell digests (`blob_trees`). -/
def blobRootWithHash {r : ℕ} (c : Fin (r * 128) → Cell) (i : ℕ) : DigestBytes :=
  merkleRootWithHash H 7 (cellLeavesWithHash H c i)

/-- **The root of a matrix** (`commit_codewords`): the Merkle root of the padded rows' blob roots. -/
def commitCellsWithHash {r : ℕ} (c : Fin (r * 128) → Cell) : DigestBytes :=
  merkleRootWithHash H (logPaddedRowCount r) (blobRootWithHash H c)

/-- The honest opening of a position: the cell's path in its blob's tree, then its blob root's in
the tree over the blob roots. -/
def openCellWithHash {r : ℕ} (c : Fin (r * 128) → Cell) (p : Fin (r * 128)) : CellOpening :=
  ⟨merklePathWithHash H 7 (cellLeavesWithHash H c (positionRow p)) (positionCell p) ++
    merklePathWithHash H (logPaddedRowCount r) (blobRootWithHash H c) (positionRow p)⟩

/-- One level of a Merkle tree: the digests of neighbouring pairs (`tree_from_leaves`). -/
def treeLevelWithHash (nodes : List DigestBytes) : List DigestBytes :=
  (List.range (nodes.length / 2)).map (upWithHash H fun i ↦ nodes.getD i default)

/-- The root of the Merkle tree over a power-of-two number of digests (`tree_from_leaves`; on
other lengths, which `commitCodewords` never passes, the crate panics). -/
def treeRootWithHash (nodes : List DigestBytes) : DigestBytes :=
  if nodes.length ≤ 1 then nodes.headD default else treeRootWithHash (treeLevelWithHash H nodes)
termination_by nodes.length
decreasing_by simp only [treeLevelWithHash, List.length_map, List.length_range]; omega

/-- The digest of cell `j` of a codeword (`hash_cells`). -/
def listCellDigestWithHash (row : List K) (j : ℕ) : DigestBytes :=
  H ((listCell row j).flatMap K.toBytes)

/-- The blob root of a codeword: the Merkle root of its `128` cell digests, built level by level
(`blob_trees`, `fill_levels`). -/
def listBlobRootWithHash (row : List K) : DigestBytes :=
  treeRootWithHash H ((List.range cellsPerRow).map (listCellDigestWithHash H row))

/-- The digest of the zero cell (`padding_tree`'s leaves). -/
def paddingCellWithHash : DigestBytes := H ((List.replicate cellSymbols 0).flatMap K.toBytes)

/-- The blob root of the zero codeword, which pads the tree over the blob roots
(`padding_root`, `commit.rs:70-78`). -/
def paddingBlobRootWithHash : DigestBytes :=
  treeRootWithHash H (List.replicate cellsPerRow (paddingCellWithHash H))

/-- **The root of a matrix of codewords, as the crate computes it** (`commit_codewords`): the
rows padded to a power of two with zero codewords, the tree over their blob roots. -/
def commitCodewordsWithHash (rows : List (List K)) : DigestBytes :=
  treeRootWithHash H (rows.map (listBlobRootWithHash H) ++
    List.replicate (paddedRowCount rows.length - rows.length) (paddingBlobRootWithHash H))

end Pure

/-- **The root of a matrix of codewords, as the crate computes it** (`commit_codewords`,
`commit.rs:52-125`), over a permutation `π`: on codewords of `2^15` symbols it is the statement's
`commitCells π (cellsOfRows rows)` (`commitCodewords_eq_commitCells`, `LeanDa.Commitment`). The
blob roots in the crate's order, each tree built level by level, as compiled code computes it
fast. -/
def commitCodewords (π : KeccakState → KeccakState) (rows : List (List K)) : DigestBytes :=
  commitCodewordsWithHash (hashOver π) rows

section Monadic

variable {m : Type → Type} [Monad m] (H : List UInt8 → m DigestBytes)
  (P : KeccakState → m KeccakState)

/-- **The challenge `z` of a root** (`membership_challenge`, `verifier/src/da.rs:20-34`): the
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

/-- **Verification of a cell opening**: a path of `7 + ⌈log₂ r⌉` siblings that climbs from the
cell's digest, at index `128 i + j` (the position), to the commitment. -/
def verifyCellMWithHash (r : ℕ) (com : DigestBytes) (p : Fin (r * 128)) (x : Cell)
    (τ : CellOpening) : m Bool := do
  let d ← H (cellBytes x)
  let root ← walkMWithHash H (p : ℕ) d τ.path
  pure (decide (τ.path.length = 7 + logPaddedRowCount r) && decide (root = com))

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

/-- **The root of a matrix over an oracle** (`commitCells`): the tree over the blob roots. -/
def commitCellsMWithHash {r : ℕ} (c : Fin (r * 128) → Cell) : m DigestBytes :=
  merkleRootMWithHash H (logPaddedRowCount r) (blobRootMWithHash H c)

end Monadic

/-- **The relation the argument proves**, with a hash `H` and the sponge's permutation `P` in any
monad: the cells commit to the root and pass the membership test on the root's challenge, drawn
by the deployed duplex (`membershipChallengeWith`). In the games `H` is Keccak-256 over `π`
(`keccak256OverPermutation`) and `P` is `π` (`queryPermutation`). -/
noncomputable def relationMWithHash {m : Type → Type} [Monad m] (H : List UInt8 → m DigestBytes)
    (P : KeccakState → m KeccakState) {r : ℕ} (root : DigestBytes) (c : Fin (r * 128) → Cell) :
      m Bool := do
  let z ← membershipChallengeMWithHash H P root
  let d ← commitCellsMWithHash H c
  pure (decide (d = root) && membershipCheckOpt z c)

/-- **Keccak-256 over a permutation `π`** (`keccak256With`), its digest's bytes: the hash `H` of
the games when the permutation is `π` (`runWithRandomPermutation`). -/
def keccak256WithPermutation (π : KeccakState → KeccakState) (a : List UInt8) : DigestBytes :=
  (Id.run (keccak256With (fun x ↦ pure (π x)) a)).toBytes

/-- **LeanDA's relation for a permutation `π`**: `relationWith` with Keccak-256 over `π` and `π`. -/
noncomputable def relationForPermutationWithHash (r : ℕ) (π : Equiv.Perm KeccakState)
    (root : DigestBytes)
    (c : Fin (r * 128) → Cell) : Bool :=
  Id.run (relationMWithHash (fun a ↦ pure (keccak256WithPermutation π a))
    (fun x ↦ pure (π x)) root c)

variable (r : ℕ) {Crs Proof : Type} (ps : LeanDaArgument r Crs Proof)
  (ext : StraightLineExtractor DigestBytes (Fin (r * 128) → Cell) Crs Proof)

/-- **The position-binding game**: the argument's setup, the adversary, then the verifications:
the argument's of the root's proof and the two openings'; it wins when all verify, at two
different cells. -/
def positionBindingGameWithHash (A : PositionBindingAdversary r Crs Proof) :
    OracleComp RandomPermutationOracles Bool := do
  let crs ← liftM ps.setup
  let (com, p, x, τ, x', τ') ← A ((), crs)
  let ok ← ps.verify crs com.1 com.2
  let b ← verifyCellMWithHash keccak256OverPermutation r com.1 p x τ
  let b' ← verifyCellMWithHash keccak256OverPermutation r com.1 p x' τ'
  pure (decide (x ≠ x') && ok && b && b')

/-- **The code-binding game**: the argument's setup, the adversary, then the verifications; it wins
when the root's proof and every opening verify and no codeword agrees with the opened cells. -/
noncomputable def codeBindingGameWithHash (A : CodeBindingAdversary r Crs Proof) :
    OracleComp RandomPermutationOracles Bool := do
  let crs ← liftM ps.setup
  let (com, opened) ← A ((), crs)
  let ok ← ps.verify crs com.1 com.2
  let verdicts ← opened.mapM fun o ↦
    verifyCellMWithHash keccak256OverPermutation r com.1 o.1 o.2.1 o.2.2
  pure (ok && verdicts.all id && !decide ((leanDaErasureCode r).Consistent (opened.map fun o ↦ (o.1,
      o.2.1))))

/-- **The argument's knowledge-soundness game** (Wagner's, Foundations Definition 18, in the
random-permutation model with a straight-line extractor): the argument's setup, the adversary with
its queries logged, the argument's verification, then the relation's check on the cells the
extractor reads off the proof and the adversary's transcript; it wins when the proof verifies and
the extracted cells do not satisfy the relation (`relationWith` over Keccak-256 over `π`, and `π`).
-/
noncomputable def knowledgeSoundnessGameWithHash (B : KnowledgeSoundnessAdversary Crs Proof) :
    OracleComp RandomPermutationOracles Bool := do
  let crs ← liftM ps.setup
  let ((root, proof), log) ← (simulateQ loggedOracles (B crs)).run []
  let v ← ps.verify crs root proof
  let ok ← relationMWithHash keccak256OverPermutation queryPermutation root (ext crs root proof log)
  pure (v && !ok)

/-- **The completeness experiment for a permutation `π`** (Wagner's, Foundations Definition 8,
with the hash and the oracles answered by `π`): the argument's setup; the honest commitment to the
message `msg`, the root of its encoding's cells hashed with Keccak-256 over `π`; the argument's
honest proof for the root and its verification, both with the oracles answered by `π`; and the
verification of the encoding's cell at `p` with its honest opening. -/
noncomputable def completenessExperimentWithHash (π : Equiv.Perm KeccakState)
    (ps : LeanDaArgument r Crs Proof)
    (msg : Fin r → Payload) (p : Fin (r * 128)) : ProbComp Bool := do
  let crs ← ps.setup
  let c := (leanDaErasureCode r).encode msg
  let root := commitCellsWithHash (keccak256WithPermutation π) c
  let ok ← simulateQ (oraclesFromPermutation π) (ps.prove crs root c >>= ps.verify crs root)
  pure (ok && Id.run
    (verifyCellMWithHash (fun a ↦ pure (keccak256WithPermutation π a)) r root p (c p)
    (openCellWithHash (keccak256WithPermutation π) c p)))

/-- **LeanDA is perfectly complete in the random-permutation model, for every permutation.**
For any number `r` of rows, every permutation `π` of the Keccak state, and every argument `ps`
perfectly complete for LeanDA's relation for every permutation (`relationForPermutation`, the hash
Keccak-256 over `π` and the challenge the deployed duplex over `π`; the argument's prover and
verifier answered by `π`): every position `p` of the honest commitment to every message `msg`
opens and verifies with probability one (`completenessExperiment`). Holding for each `π`, it holds
for every outcome of the binding statements' uniformly random permutation. The proof is Wagner's
completeness proof, transferred. Proved by `LeanDa.leanDa_perfectlyComplete_rpm`. -/
abbrev PerfectlyCompleteRpmWithHash : Prop :=
  ∀ (r : ℕ) (π : Equiv.Perm KeccakState) {Crs Proof : Type} (ps : LeanDaArgument r Crs Proof),
    ps.PerfectlyComplete (relationForPermutationWithHash r) →
      ∀ (msg : Fin r → Payload) (p : Fin (r * 128)),
        Pr{let b ← completenessExperimentWithHash r π ps msg p}[b = true] = 1

/-- **LeanDA is position binding in the random-permutation model.** For every argument `ps` (any
prover and verifier) and every adversary whose game, verifications included, makes at most `Q`
calls of `π` and `π⁻¹` on every path (`permutationCallCost`; a hash of `n` bytes, Keccak-256 over
`π`, makes `⌊n / 136⌋ + 1`; the argument's verifier's included), the probability of opening a
position to two different cells is at most `(Q + 1)² · 2^-256`, for every `Q` (past `2^128` the
bound exceeds one). Proved by
`LeanDa.leanDa_positionBinding_rpm`. -/
abbrev PositionBindingRpmWithHash : Prop :=
  ∀ (r : ℕ) {Crs Proof : Type} (ps : LeanDaArgument r Crs Proof)
    (A : PositionBindingAdversary r Crs Proof)
    (Q : ℕ), QueryCostAtMost (positionBindingGameWithHash r ps A) permutationCallCost Q →
      Pr{let b ← runWithRandomPermutation (positionBindingGameWithHash r ps A)}[b = true] ≤
        ((Q : ℝ≥0∞) + 1) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256

/-- **LeanDA is code binding in the random-permutation model, for an argument knowledge sound in
it** (Benedikt Wagner's framework and games, moved to the random-permutation model, with a
straight-line argument in place of his forking lemma). For `1 ≤ r ≤ 1024` rows (`maxRows`, the
crate's bound), every argument `ps` (its prover and verifier querying the model's oracles) and
straight-line extractor `ext` (reading the adversary's transcript): if every adversary whose
knowledge-soundness game (`knowledgeSoundnessGame`, the argument's verifier and the relation's check
included) makes at most `q ≤ 2^128` permutation calls (`permutationCallCost`) wins it with
probability at most `(q + c) · 2^-k`, then every adversary whose code-binding game, verifications
included, makes at most `Q` calls breaks code binding with probability at most

`(Q + c + 2^65) · 2^-k + (Q + 2^11) · 2^-125 + (Q + 2^22)² · 2^-247`.

The first term is the argument's knowledge soundness against the code-binding adversary itself,
its transcript handed to the extractor (at most `Q + 2^65` calls with the relation's check, the
nonce search's `2^64 + 2` on the worst path among them). The second is the membership test with its
grind: `2^-11 · (2^14 - 1) / 2^128 ≤ 2^-125` for each of the adversary's calls, and
`(2^14 - 1) / 2^128` for the verifier's one search. The third gathers the transfer to the
two-oracle model and the duplex lemma, of the two games, and the hash's bad events among at most
`2 Q + 2^20` hash queries: a collision, or a fresh answer that is a digest an earlier input or a
root with a drawn challenge already carries; it exceeds one before `Q = 2^124`.

The argument queries the oracles the adversary does, so its knowledge soundness here is the
usual one of an argument in the random-permutation model, with a straight-line extractor reading
the adversary's queries, as leanVM's (`LeanVM.KnowledgeSoundness`); an argument may satisfy it and
be perfectly complete for every permutation (`LeanDaPerfectlyComplete`). Proved by
`LeanDa.leanDa_codeBinding_rpm_bound`. -/
abbrev CodeBindingRpmWithHash : Prop :=
  ∀ (r : ℕ) {Crs Proof : Type} (ps : LeanDaArgument r Crs Proof)
    (ext : StraightLineExtractor DigestBytes (Fin (r * 128) → Cell) Crs Proof) (c k : ℕ),
    (∀ (B : KnowledgeSoundnessAdversary Crs Proof) (q : ℕ),
      QueryCostAtMost (knowledgeSoundnessGameWithHash r ps ext B) permutationCallCost q →
      q ≤ 2 ^ 128 →
        Pr{let b ← runWithRandomPermutation (knowledgeSoundnessGameWithHash r ps ext B)}[b = true] ≤
        ((q : ℝ≥0∞) + c) * (2 : ℝ≥0∞)⁻¹ ^ k) →
    1 ≤ r → r ≤ maxRows →
    ∀ (A : CodeBindingAdversary r Crs Proof) (Q : ℕ),
      QueryCostAtMost (codeBindingGameWithHash r ps A) permutationCallCost Q →
        Pr{let b ← runWithRandomPermutation (codeBindingGameWithHash r ps A)}[b = true] ≤
          ((Q : ℝ≥0∞) + c + 2 ^ 65) * (2 : ℝ≥0∞)⁻¹ ^ k + ((Q : ℝ≥0∞) + 2 ^ 11) *
            (2 : ℝ≥0∞)⁻¹ ^ 125 +
            ((Q : ℝ≥0∞) + 2 ^ 22) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 247

end LeanDa

end
