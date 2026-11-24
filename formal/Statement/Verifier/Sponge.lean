module

public import Statement.Field

/-!
# The duplex sponge (`transcript.rs`)

The Fiat-Shamir sponge of the leanVM verifier (`Transcript.lean`) and of LeanDA's membership
challenges (`Statement/LeanDa.lean`), the Rust's (`crates/verifier/src/transcript.rs`, `Sponge`; the
prover's `crates/fiat_shamir_prover/src/lib.rs`): a duplex over a permutation `π` of the Keccak
state (deployed: Keccak-f[1600]) in overwrite mode, the rate lanes `0..16`, the capacity lanes
`16..25`, and up to four absorbed scalars waiting, each with a tag, `1` for a scalar the prover sent
(`DS_OBSERVE`) and `4` for a proof-of-work nonce (`DS_POW_NONCE`). A permutation writes waiting
scalar `i` over lanes `4i..4i+4` (its two limbs, a zero lane, then its tag), zeroes the rest of the
rate, keeps the capacity, and empties the queue; absorbing a fifth scalar permutes the four waiting
first. A challenge is the first two lanes of a permutation of its own, except after a grind: a nonce
is absorbed and permuted at once, that permutation's third lane is the proof of work and its first
two the next challenge, kept until it is squeezed (`ground`). The sponge starts at `π` of the IV's
and the public input's words, the other lanes zero (`Sponge::new`, `transcript.rs`).
-/

@[expose] public section

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

end Duplex

end LeanVM.Protocol.Compile

end
