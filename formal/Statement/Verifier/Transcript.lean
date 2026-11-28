module

public import Statement.Field

/-!
# The verifier's transcript (`transcript.rs`, `merkle.rs`)

The verifier touches the proof through seven operations of its `Transcript`
(`crates/verifier/src/transcript.rs`): `next_scalar`, `next_scalars_packed`, `sample`,
`samples_packed`, `grind_check`, a root read as two scalars, and `merkle`. It computes everything
else from their results; `VerifierProgram α` is the free monad over them, run (`run`, `runProof`)
as the deployed non-interactive verifier: the challenges squeezed out of a duplex sponge and the
rows authenticated by Merkle paths.

The sponge is the duplex below (`Sponge`, `absorb`, `squeeze`, `absorbNonce`, `observePacked`,
`samplesPacked`, `seedInput`), which LeanDA's membership challenges use too, over Keccak-f[1600] in
the deployed verifier. A proof of work absorbs its nonce with the tag `4` and permutes at once; the
permutation's third lane is the proof of work, and its first two lanes the challenge the next
`sample` returns (`ground`); a packed draw right after it takes that challenge and then the
permutation's cells `2..8`. A packed message permutes whatever waits, then takes eight untagged
scalars a permutation, two lanes each, the rate zero past them; a packed draw permutes once per
eight challenges, its rate two lanes to a challenge. The Rust asserts that nothing is absorbed
while that challenge waits (`Sponge::absorb`, `transcript.rs`); `run` rejects there.
Merkle openings come from a separate channel that the sponge does not absorb: each query's
opening is its position, the leaf's words, hashed as bytes, then one sibling per level, the
position's bit at the level choosing the side.

The proof is the Rust verifier's `Proof` (`transcript.rs`): the scalar stream, and the Merkle
openings grouped in phases, one phase per opened commitment, each query's opening (`MerklePath`,
`crates/verifier/src/merkle.rs`: position, leaf, siblings) in the order the verifier samples
the queries; the proof's wire encoding (`wire.rs`, a compression layer formalized in `lean_vm`)
needs the phases. A phase is checked as `Transcript::merkle` checks it (`transcript.rs`):
its shape, then its positions, then its roots.
-/

@[expose] public section

/-! ## The duplex sponge

The Fiat-Shamir sponge of the leanVM verifier and of LeanDA's membership challenges, the Rust's
(`crates/verifier/src/transcript.rs`, `Sponge`; the prover's `crates/fiat_shamir_prover/src/lib.rs`):
a duplex over a permutation `π` of the Keccak state (deployed: Keccak-f[1600]) in overwrite mode,
the rate lanes `0..16`, the capacity lanes `16..25`, and up to four absorbed scalars waiting, each
with a tag, `1` for a scalar the prover sent (`DS_OBSERVE`) and `4` for a proof-of-work nonce
(`DS_POW_NONCE`). A permutation writes waiting scalar `i` over lanes `4i..4i+4` (its two limbs, a
zero lane, then its tag), zeroes the rest of the rate, keeps the capacity, and empties the queue;
absorbing a fifth scalar permutes the four waiting first. A challenge is the first two lanes of a
permutation of its own, except after a grind: a nonce is absorbed and permuted at once, that
permutation's third lane is the proof of work and its first two the next challenge, kept until it is
squeezed (`ground`). The sponge starts at `π` of the IV's and the public input's words, the other
lanes zero (`Sponge::new`, `transcript.rs`). -/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Semantics

/-- `DS_OBSERVE`: the tag of a scalar the prover sent (`transcript.rs`). -/
def dsObserve : ℕ := 1

/-- `DS_POW_NONCE`: the tag of a proof-of-work nonce (`transcript.rs`). -/
def dsPowNonce : ℕ := 4

/-- `RATE_SCALARS`: the scalars that wait to be absorbed, four lanes each
(`transcript.rs`). -/
def rateScalars : ℕ := 4

/-- The duplex sponge: the Keccak state, the scalars waiting to be absorbed (at most
`rateScalars`), each with its tag, and the challenge a grind drew (`Sponge`'s `state`, `pending`
and `ground`, `transcript.rs`). -/
structure Sponge where
  /-- The Keccak state the last permutation left. -/
  state : KeccakState
  /-- The scalars waiting to be absorbed, each with its tag, in order. -/
  pending : List (E × ℕ)
  /-- The challenge a grind's permutation drew, which the next squeeze returns. -/
  ground : Option E := none

/-- The rate lanes of the waiting scalars: each its two limbs, a zero lane, then its tag
(`transcript.rs`). -/
def pendingLanes (pending : List (E × ℕ)) : List UInt64 :=
  pending.flatMap fun (x, tag) ↦ [(x.limb 0).lane, (x.limb 1).lane, 0, tag.toUInt64]

/-- The input of a permutation: the waiting scalars' lanes, zeros up to lane `16`, then the
capacity, lanes `16..25` of the state (`Sponge::duplex`, `transcript.rs`). -/
def duplexInput (sponge : Sponge) : KeccakState :=
  Vector.ofFn fun i ↦
    if i.val < 16 then (pendingLanes sponge.pending).getD i 0 else Keccak.lane sponge.state i

/-- The challenge squeezed into a state: its first two lanes (`Sponge::sample`,
`transcript.rs`). -/
def challengeOf (state : KeccakState) : E :=
  E.ofLimbs (K.ofLane (Keccak.lane state 0)) (K.ofLane (Keccak.lane state 1))

/-- The initial state's input: the IV's four words, the public input's four words, then zeros
(`Sponge::new`, `transcript.rs`). -/
def seedInput (iv publicInput : Digest) : KeccakState :=
  Vector.ofFn fun i ↦
    if h : i.val < 4 then iv[i.val] else if h' : i.val < 8 then publicInput[i.val - 4] else 0

section Duplex

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

/-- A permutation: the waiting scalars over the rate, the capacity kept, then `π`; the queue
empties (`Sponge::duplex`, `transcript.rs`). -/
def duplex (sponge : Sponge) : m Sponge := do
  let state ← π (duplexInput sponge)
  pure ⟨state, [], sponge.ground⟩

/-- Absorb a scalar with a tag: a full queue is permuted first (`Sponge::absorb`,
`transcript.rs`). The Rust asserts no ground challenge waits; the verifier's runs
(`run`, below) reject there instead. -/
def absorb (sponge : Sponge) (x : E) (tag : ℕ) : m Sponge := do
  let sponge ← if sponge.pending.length = rateScalars then duplex π sponge else pure sponge
  pure { sponge with pending := sponge.pending ++ [(x, tag)] }

/-- Squeeze a challenge: the ground one if a grind drew it, otherwise a permutation and then the
new state's first two lanes (`Sponge::sample`, `transcript.rs`). -/
def squeeze (sponge : Sponge) : m (E × Sponge) := do
  match sponge.ground with
  | some c => pure (c, { sponge with ground := none })
  | none => do
    let sponge ← duplex π sponge
    pure (challengeOf sponge.state, sponge)

/-- Absorb a grinding nonce and permute: the output's first two lanes are the next challenge, kept
for `squeeze`, and its third lane, the proof of work, is returned (`Sponge::absorb_nonce`,
`transcript.rs`). -/
def absorbNonce (sponge : Sponge) (nonce : E) : m (UInt64 × Sponge) := do
  let sponge ← absorb π sponge nonce dsPowNonce
  let sponge ← duplex π sponge
  pure (Keccak.lane sponge.state 2, { sponge with ground := some (challengeOf sponge.state) })

/-- Challenge `i` of a packed draw: lanes `2i` and `2i + 1` of the state (`Sponge::samples_packed`,
`transcript.rs`). -/
def packedChallengeOf (state : KeccakState) (i : ℕ) : E :=
  E.ofLimbs (K.ofLane (Keccak.lane state (2 * i))) (K.ofLane (Keccak.lane state (2 * i + 1)))

/-- The input of a packed permutation: the chunk's scalars over the rate, two lanes each, zeros up
to lane `16`, then the capacity, lanes `16..25` of the state (`Sponge::observe_packed`,
`transcript.rs`). -/
def packedInput (state : KeccakState) (chunk : List E) : KeccakState :=
  Vector.ofFn fun i ↦
    if i.val < 16 then (chunk.flatMap fun x ↦ [(x.limb 0).lane, (x.limb 1).lane]).getD i 0
    else Keccak.lane state i

/-- The loop of `observe_packed`: one permutation per chunk of eight scalars. `fuel` bounds the
recursion; every step drops at least one scalar, so the scalars' count is enough. -/
def absorbPackedChunks : ℕ → KeccakState → List E → m KeccakState
  | 0, state, _ => pure state
  | _ + 1, state, [] => pure state
  | fuel + 1, state, values@(_ :: _) => do
    let state ← π (packedInput state (values.take 8))
    absorbPackedChunks fuel state (values.drop 8)

/-- Absorb scalars eight to a permutation, untagged, after a permutation taking whatever waits
(`Sponge::observe_packed`, `transcript.rs`). The Rust asserts no ground challenge waits; the
verifier's runs reject there instead. -/
def observePacked (sponge : Sponge) (values : List E) : m Sponge := do
  let sponge ← if sponge.pending.isEmpty then pure sponge else duplex π sponge
  let state ← absorbPackedChunks π values.length sponge.state values
  pure { sponge with state := state }

/-- The loop of `samples_packed`: while challenges are missing, a permutation, and its rate's first
`min(8, missing)` challenges. `fuel` bounds the recursion; every step draws at least one. -/
def squeezePackedChunks : ℕ → Sponge → ℕ → m (List E × Sponge)
  | 0, sponge, _ => pure ([], sponge)
  | _ + 1, sponge, 0 => pure ([], sponge)
  | fuel + 1, sponge, missing + 1 => do
    let sponge ← duplex π sponge
    let take := min 8 (missing + 1)
    let drawn := (List.range take).map (packedChallengeOf sponge.state)
    let (rest, sponge) ← squeezePackedChunks fuel sponge (missing + 1 - take)
    pure (drawn ++ rest, sponge)

/-- Squeeze `count` challenges eight to a permutation (`Sponge::samples_packed`, `transcript.rs`):
right after a grind, the ground challenge, then up to six more of the grind's permutation, from
cells `2..8` (cell `1` holds the proof of work); then whole permutations, as `squeeze`'s. -/
def samplesPacked (sponge : Sponge) (count : ℕ) : m (List E × Sponge) := do
  let (first, sponge) := match count, sponge.ground with
    | 0, _ => (([] : List E), sponge)
    | _ + 1, none => ([], sponge)
    | c + 1, some ground =>
      (ground :: ((List.range 6).take c).map (packedChallengeOf sponge.state ∘ (· + 2)),
        { sponge with ground := none })
  let (rest, sponge) ← squeezePackedChunks π (count - first.length) sponge (count - first.length)
  pure (first ++ rest, sponge)

end Duplex

end LeanVM.Protocol.Compile

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash

/-- The verifier language: a program returns a value of type `α` after reading scalars,
sampling challenges, checking proofs of work, reading commitments and opening rows, or fails. -/
inductive VerifierProgram (α : Type) : Type where
  /-- Return `a`. -/
  | ret (a : α)
  /-- Reject. -/
  | fail
  /-- Read the next prover scalar, absorbed into the sponge (`next_scalar`). -/
  | read (k : E → VerifierProgram α)
  /-- Sample a challenge, squeezed from the sponge (`sample`). -/
  | sample (k : E → VerifierProgram α)
  /-- Read the next `n` prover scalars, absorbed eight to a permutation, untagged
  (`next_scalars_packed`, `Sponge::observe_packed`). -/
  | readPacked (n : ℕ) (k : List E → VerifierProgram α)
  /-- Sample `n` challenges, squeezed eight to a permutation; right after a grind, the first seven
  from the grind's permutation (`samples_packed`, `Sponge::samples_packed`). -/
  | samplePacked (n : ℕ) (k : List E → VerifierProgram α)
  /-- Check a proof of work of `bits` bits, the nonce read, absorbed and permuted (`grind_check`).
  The programs build it with `bits ≥ 1` only (`grindProofOfWork`). -/
  | grind (bits : ℕ) (k : VerifierProgram α)
  /-- Read a Merkle root as two scalars (`Digest::from_halves` of `next_scalars(2)`), the committed
  matrix being `2^height` rows of `width` words. -/
  | commit (height width : ℕ) (k : VerifierProgram α)
  /-- Open rows of the `i`-th commitment at `positions`, each with its authentication path
  (`merkle`); continue with the rows. -/
  | query (i : ℕ) (positions : List ℕ) (k : List (List K) → VerifierProgram α)

namespace VerifierProgram

variable {α β γ : Type}

/-- Sequencing. -/
def bind : VerifierProgram α → (α → VerifierProgram β) → VerifierProgram β
  | ret a, f => f a
  | fail, _ => fail
  | read k, f => read fun x ↦ (k x).bind f
  | sample k, f => sample fun x ↦ (k x).bind f
  | readPacked n k, f => readPacked n fun xs ↦ (k xs).bind f
  | samplePacked n k, f => samplePacked n fun xs ↦ (k xs).bind f
  | grind b k, f => grind b (k.bind f)
  | commit h w k, f => commit h w (k.bind f)
  | query i ps k, f => query i ps fun r ↦ (k r).bind f

instance : Monad VerifierProgram where
  pure := ret
  bind := bind

/-- Read one prover scalar. -/
def readScalar : VerifierProgram E := read ret

/-- Read `n` prover scalars, in order. -/
def readScalars : ℕ → VerifierProgram (List E)
  | 0 => ret []
  | n + 1 => do
    let x ← readScalar
    let xs ← readScalars n
    return x :: xs

/-- Sample one challenge. -/
def sampleChallenge : VerifierProgram E := sample ret

/-- Sample `n` challenges, in order. -/
def sampleChallenges : ℕ → VerifierProgram (List E)
  | 0 => ret []
  | n + 1 => do
    let x ← sampleChallenge
    let xs ← sampleChallenges n
    return x :: xs

/-- Read `n` prover scalars as one packed message (`Transcript::next_scalars_packed`,
`transcript.rs`). -/
def readScalarsPacked (n : ℕ) : VerifierProgram (List E) := readPacked n ret

/-- Sample `n` challenges as one packed draw (`Transcript::samples_packed`, `transcript.rs`). -/
def sampleChallengesPacked (n : ℕ) : VerifierProgram (List E) := samplePacked n ret

/-- Check a proof of work of `bits` bits (`Transcript::grind_check`, `transcript.rs`). A
grind of zero bits is nothing: no nonce, no permutation, no step of the program. -/
def grindProofOfWork (bits : ℕ) : VerifierProgram Unit :=
  if bits = 0 then ret () else grind bits (ret ())

/-- Read a commitment to a matrix of `2^height` rows of `width` words. -/
def readCommitment (height width : ℕ) : VerifierProgram Unit := commit height width (ret ())

/-- Open rows of the `i`-th commitment. -/
def queryOpenings (i : ℕ) (positions : List ℕ) : VerifierProgram (List (List K)) := query i
    positions ret

/-- Reject unless `c` holds (`require`, `lib.rs`). -/
def require (c : Prop) [Decidable c] : VerifierProgram Unit := if c then ret () else fail

end VerifierProgram

/-- Byte strings, the hash's inputs. -/
abbrev Bytes : Type := List UInt8

/-! ## Proofs and the run -/

/-- The proof-of-work predicate on the third lane of the permutation that absorbed the nonce: its
low `bits` bits are zero (`Transcript::grind_check`, `transcript.rs`, the mask all ones
from `64` bits on). -/
def powOk (bits : ℕ) (pow : UInt64) : Bool := decide (pow.toNat % 2 ^ bits = 0)

/-- One Merkle opening (`MerklePath`, `crates/verifier/src/merkle.rs`): the position it
opens, the leaf's words and the siblings from the leaf up. -/
structure Opening where
  /-- The position of the leaf (`leaf_index`). -/
  leafIndex : ℕ
  /-- The leaf's words. -/
  leaf : List K
  /-- The siblings from the leaf up. -/
  path : List Digest

/-- A proof (`Proof`, `crates/verifier/src/transcript.rs`): the scalar stream, and the Merkle
openings, one phase per commitment opened, each query's opening in the order the verifier samples
the queries. -/
structure Proof where
  /-- The scalars the prover sends, in order. -/
  stream : List E
  /-- The Merkle openings, one list per phase, in order. -/
  openings : List (List Opening)

/-- The compiled verifier's state: the sponge, the scalars and openings not yet read, and the
roots read so far, each with its height and width. -/
structure VerifierProgramState where
  /-- The Fiat-Shamir sponge. -/
  sponge : Sponge
  /-- The scalars not yet read. -/
  stream : List E
  /-- The phases of openings not yet read. -/
  openings : List (List Opening)
  /-- The roots read so far, each with its tree's height and width. -/
  roots : List (Digest × ℕ × ℕ)

section Run

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

/-- Climb a Merkle path from `node` at position `q`: at each level the position's low bit says
whether `node` is the left child (`MerklePath::root`, `merkle.rs`). -/
def climb : Digest → ℕ → List Digest → m Digest
  | node, _, [] => pure node
  | node, q, s :: ss => do
    let parent ← if q % 2 = 0 then keccak256With π (digestBytes node ++ digestBytes s)
      else keccak256With π (digestBytes s ++ digestBytes node)
    climb parent (q / 2) ss

/-- Check one opening against a root of the given shape at position `position`: its shape
(`transcript.rs`), then its leaf hashed and climbed to the root (`hash_leaf` and
`MerklePath::root`, `merkle.rs`). -/
def openOne (root : Digest) (height width position : ℕ) (opening : Opening) : m Bool :=
  if opening.leaf.length = width ∧ opening.path.length = height then do
    let leafDigest ← keccak256With π (opening.leaf.flatMap K.toBytes)
    let top ← climb π leafDigest position opening.path
    pure (decide (top.toList = root.toList))
  else pure false

/-- Open every position in order, consuming one opening each; the leaves, and the openings
left. -/
def openAll (root : Digest) (height width : ℕ) :
    List ℕ → List Opening → m (Option (List (List K) × List Opening))
  | [], os => pure (some ([], os))
  | _ :: _, [] => pure none
  | q :: qs, o :: os => do
    if ← openOne π root height width q o then
      let rest ← openAll root height width qs os
      pure (rest.map fun r ↦ (o.leaf :: r.1, r.2))
    else pure none

/-- Open one phase of a commitment of the given shape at `positions` (`Transcript::merkle`,
`crates/verifier/src/transcript.rs`): reject unless every leaf is `width` words and every
path `height` siblings, then unless the phase's positions are `positions`, in order, then unless
each path climbs to `root`, in order (at its position, which is the query's). The leaves. -/
def openPhase (root : Digest) (height width : ℕ) (positions : List ℕ) (phase : List Opening) :
    m (Option (List (List K))) :=
  if (∀ opening ∈ phase, opening.leaf.length = width ∧ opening.path.length = height) ∧
      phase.map Opening.leafIndex = positions then do
    match ← openAll π root height width positions phase with
    | some (rows, _) => pure (some rows)
    | none => pure none
  else pure none

/-- The compiled reading of a program: run it on the state, every challenge squeezed out of the
sponge and every opening authenticated; `none` on rejection. What absorbs (a read, a packed read, a
commitment's two halves, a proof of work's nonce) rejects while a grind's challenge waits, where the
Rust's `Sponge::absorb` and `Sponge::observe_packed` assert (`transcript.rs`); a sample, or a packed
draw, returns that challenge first. A packed read takes its `n` scalars only if the stream holds
them, as `next_scalars_packed` reads them all before it absorbs. A proof of work
reads its nonce (`next`, unobserved), absorbs it with its tag and permutes (`absorbNonce`), and
checks the permutation's third lane (`grind_check`, `transcript.rs`). A commitment's root
is its two halves' digest (`Digest::from_halves`, `crates/verifier/src/hash.rs`). -/
def run {α : Type} : VerifierProgram α → VerifierProgramState → m (Option (α ×
    VerifierProgramState))
  | .ret a, s => pure (some (a, s))
  | .fail, _ => pure none
  | .read k, s => match s.stream, s.sponge.ground with
    | x :: xs, none => do
      let sponge ← absorb π s.sponge x dsObserve
      run (k x) { s with sponge := sponge, stream := xs }
    | _, _ => pure none
  | .sample k, s => do
    let (c, sponge) ← squeeze π s.sponge
    run (k c) { s with sponge := sponge }
  | .readPacked n k, s =>
    if s.sponge.ground.isNone ∧ n ≤ s.stream.length then do
      let xs := s.stream.take n
      let sponge ← observePacked π s.sponge xs
      run (k xs) { s with sponge := sponge, stream := s.stream.drop n }
    else pure none
  | .samplePacked n k, s => do
    let (cs, sponge) ← samplesPacked π s.sponge n
    run (k cs) { s with sponge := sponge }
  | .grind bits k, s => match s.stream, s.sponge.ground with
    | n :: xs, none => do
      let (pow, sponge) ← absorbNonce π s.sponge n
      if powOk bits pow then run k { s with sponge := sponge, stream := xs } else pure none
    | _, _ => pure none
  | .commit height width k, s => match s.stream, s.sponge.ground with
    | x0 :: x1 :: xs, none => do
      let sponge ← absorb π s.sponge x0 dsObserve
      let sponge ← absorb π sponge x1 dsObserve
      let root := digestFromHalves (x0, x1)
      run k { s with sponge := sponge, stream := xs, roots := s.roots ++ [(root, height, width)] }
    | _, _ => pure none
  | .query i ps k, s => match s.roots[i]?, s.openings with
    | some (root, height, width), phase :: rest => do
      match ← openPhase π root height width ps phase with
      | some rows => run (k rows) { s with openings := rest }
      | none => pure none
    | _, _ => pure none

/-- Run a program on a proof from a seed state, and accept when it returns `true` with the
stream and the openings fully consumed (`Transcript::finish`, `transcript.rs`). -/
def runProof (program : VerifierProgram Bool) (seed : KeccakState) (proof : Proof) : m Bool := do
  match ← run π program ⟨⟨seed, [], none⟩, proof.stream, proof.openings, []⟩ with
  | some (true, s) => pure (s.stream.isEmpty && s.openings.isEmpty)
  | _ => pure false

end Run

end LeanVM.Protocol.Compile

end
