module

public import Statement.Verifier.Sponge

/-!
# The verifier's transcript (`transcript.rs`, `merkle.rs`)

The verifier touches the proof through five operations of its `Transcript`
(`crates/verifier/src/transcript.rs`): `next_scalar`, `sample`, `grind_check`, a root read
as two scalars, and `merkle`. It computes everything else from their results; `VerifierProgram α`
is the free monad over them, run (`run`, `runProof`) as the deployed non-interactive verifier: the
challenges squeezed out of a duplex sponge and the rows authenticated by Merkle paths.

The sponge is the duplex of `Sponge.lean` (`Sponge`, `absorb`, `squeeze`, `absorbNonce`,
`seedInput`), over Keccak-f[1600] in the deployed verifier. A proof of work absorbs its nonce with
the tag `4` and permutes at once; the permutation's third lane is the proof of work, and its first
two lanes the challenge the next `sample` returns (`ground`). The Rust asserts that nothing is
absorbed while that challenge waits (`Sponge::absorb`, `transcript.rs`); `run` rejects there.
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
sponge and every opening authenticated; `none` on rejection. What absorbs (a read, a commitment's
two halves, a proof of work's nonce) rejects while a grind's challenge waits, where the Rust's
`Sponge::absorb` asserts (`transcript.rs`); a sample returns that challenge. A proof of work
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
