module

public import NativeVm.Model.Field
public import Native.Keccak.Words
public import Statement.Verifier.Transcript
public import Statement.LeanVmVerifier

/-!
# The transcript

The compiled reading of the verifier language (`LeanVM.Protocol.Compile.run`,
`Statement/Verifier/Transcript.lean`) as a state threaded through the verifier: the duplex sponge
(`SpongeW`: the 25 lanes, the waiting scalars with their tags, the ground challenge), the stream and
its cursor, the openings and the cursor of the next phase, and the roots read so far (`TState`).
A step that rejects is `none` (`VM`). Each operation models the language's constructor of the same
role:

| model | language | spec of the step |
|---|---|---|
| `readScalar` | `read` | `absorb` with `dsObserve` |
| `sampleChallenge` | `sample` | `squeeze` |
| `grind` | `grindProofOfWork` | `absorbNonce`, `powOk` |
| `readCommitment` | `commit` | two absorbs, `digestFromHalves` |
| `queryOpenings` | `query` | `openPhase` |
| `require` | `require` | |

Keccak-256 is `keccak256` of the bytes of words in memory (`Native.Keccak.wordsBytes`), as
`Native.Keccak.hash` computes it: a leaf's words, or two digests' eight words. The sumcheck
rounds (`sumcheckRoundPoly`, `sumcheck`) are here too, as every phase runs them.
-/

@[expose] public section

namespace NativeVm.Model

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile

/-- One Merkle opening as the decoded proof holds it (`NativeVm.Decoded`): the leaf index, the
leaf's words, the siblings from the leaf up. -/
structure OpeningW where
  leafIndex : UInt64
  leaf : Array UInt64
  path : Array Digest
  deriving Inhabited

/-- A root read, with the shape of its tree: `2^height` leaves of `width` words. -/
structure RootW where
  digest : Digest
  height : Nat
  width : Nat
  deriving Inhabited

/-- The duplex sponge (`Sponge`): the Keccak state, the waiting scalars with their tags (at most
`rateScalars`), and the challenge a grind drew. -/
structure SpongeW where
  state : KeccakState
  pending : Array (EW × UInt64)
  ground : Option EW
  deriving Inhabited

/-- The transcript's state (`VerifierProgramState`): the sponge, the whole stream and the cursor
of the next scalar, the whole openings and the cursor of the next phase, the roots read. -/
structure TState where
  sponge : SpongeW
  stream : Array EW
  cursor : Nat
  openings : Array (Array OpeningW)
  phase : Nat
  roots : Array RootW
  deriving Inhabited

/-- The verifier's monad: the transcript threaded, `none` on rejection. -/
abbrev VM := StateT TState Option

/-! ## The sponge -/

namespace SpongeW

/-- `duplexInput`: the waiting scalars' lanes (two limbs, a zero lane, the tag) over the rate,
zeros up to lane `16`, the capacity kept. -/
def duplexInput (sp : SpongeW) : KeccakState :=
  Vector.ofFn fun i ↦
    if i.val < 16 then
      match sp.pending[i.val / 4]? with
      | some (x, tag) =>
        if i.val % 4 = 0 then x.c0 else if i.val % 4 = 1 then x.c1
        else if i.val % 4 = 2 then 0 else tag
      | none => 0
    else sp.state[i]

/-- `duplex`: permute, the queue emptied. -/
def duplex (sp : SpongeW) : SpongeW := ⟨keccakF1600 sp.duplexInput, #[], sp.ground⟩

/-- `absorb`: a full queue is permuted first. -/
def absorb (sp : SpongeW) (x : EW) (tag : UInt64) : SpongeW :=
  let sp := if sp.pending.size = rateScalars then sp.duplex else sp
  { sp with pending := sp.pending.push (x, tag) }

/-- `challengeOf`: a state's first two lanes. -/
def challengeOf (state : KeccakState) : EW := ⟨state[0], state[1]⟩

/-- `squeeze`: the ground challenge, or a permutation's first two lanes. -/
def squeeze (sp : SpongeW) : EW × SpongeW :=
  match sp.ground with
  | some c => (c, { sp with ground := none })
  | none =>
    let sp := sp.duplex
    (challengeOf sp.state, sp)

/-- `absorbNonce`: absorb the nonce with `dsPowNonce` and permute; the third lane, and the
sponge with the next challenge ground. -/
def absorbNonce (sp : SpongeW) (nonce : EW) : UInt64 × SpongeW :=
  let sp := (sp.absorb nonce dsPowNonce.toUInt64).duplex
  (sp.state[2], { sp with ground := some (challengeOf sp.state) })

end SpongeW

/-! ## Merkle paths -/

/-- Keccak-256 of the bytes of words. -/
def hashWords (ws : Array UInt64) : Digest := keccak256 (Native.Keccak.wordsBytes ws.toList)

/-- `hash_pair`: Keccak-256 of two digests' eight words. -/
def hashPair (left right : Digest) : Digest := hashWords (left.toArray ++ right.toArray)

/-- `climb`: from `node` at position `q`, each level's low bit choosing the side. -/
def climb (node : Digest) (q : UInt64) (path : Array Digest) : Digest :=
  (path.foldl (fun (acc : Digest × UInt64) s ↦
    (if acc.2 % 2 = 0 then hashPair acc.1 s else hashPair s acc.1, acc.2 / 2)) (node, q)).1

/-- `openPhase`: every opening of `width` leaf words and `height` siblings, the positions the
queried ones in order, and each path climbing from its hashed leaf to `root`; the leaves. -/
def openPhase (root : Digest) (height width : Nat) (positions : Array UInt64)
    (phase : Array OpeningW) : Option (Array (Array UInt64)) :=
  if phase.all (fun o ↦ o.leaf.size == width && o.path.size == height) &&
      phase.map (·.leafIndex) == positions then
    if phase.all fun o ↦ climb (hashWords o.leaf) o.leafIndex o.path == root then
      some (phase.map (·.leaf))
    else none
  else none

/-! ## The operations -/

/-- Reject. -/
def reject {α : Type} : VM α := fun _ ↦ none

/-- Reject unless `c`. -/
def require (c : Bool) : VM Unit := if c then pure () else reject

/-- Fail on `none` (`liftOption`). -/
def liftOpt {α : Type} : Option α → VM α
  | some a => pure a
  | none => reject

/-- The next stream element, unobserved, rejecting at the stream's end or while a grind's
challenge waits. -/
def nextScalar : VM EW := do
  let s ← get
  if s.sponge.ground.isSome then reject
  else match s.stream[s.cursor]? with
    | some x => do
      set { s with cursor := s.cursor + 1 }
      pure x
    | none => reject

/-- `read`: the next scalar, absorbed with `dsObserve`. -/
def readScalar : VM EW := do
  let x ← nextScalar
  modify fun s ↦ { s with sponge := s.sponge.absorb x dsObserve.toUInt64 }
  pure x

/-- `readScalars n`. -/
def readScalars (n : Nat) : VM (Array EW) :=
  (List.range n).foldlM (fun acc _ ↦ do pure (acc.push (← readScalar))) #[]

/-- `sample`. -/
def sampleChallenge : VM EW := do
  let s ← get
  let (c, sp) := s.sponge.squeeze
  set { s with sponge := sp }
  pure c

/-- `sampleChallenges n`. -/
def sampleChallenges (n : Nat) : VM (Array EW) :=
  (List.range n).foldlM (fun acc _ ↦ do pure (acc.push (← sampleChallenge))) #[]

/-- `powOk`: the low `bits` bits of the proof of work are zero. -/
def powOkW (bits : Nat) (pow : UInt64) : Bool :=
  if 64 ≤ bits then pow == 0 else pow &&& ((1 <<< bits.toUInt64) - 1) == 0

/-- `grindProofOfWork bits`: nothing at `0` bits; otherwise the nonce read, absorbed with its tag
and permuted, and the third lane checked. -/
def grind (bits : Nat) : VM Unit := do
  if bits = 0 then pure ()
  else
    let nonce ← nextScalar
    let s ← get
    let (pow, sp) := s.sponge.absorbNonce nonce
    set { s with sponge := sp }
    require (powOkW bits pow)

/-- `readCommitment height width`: a root as two absorbed scalars (`digestFromHalves`). -/
def readCommitment (height width : Nat) : VM Unit := do
  let x0 ← readScalar
  let x1 ← readScalar
  modify fun s ↦
    { s with roots := s.roots.push ⟨#v[x0.c0, x0.c1, x1.c0, x1.c1], height, width⟩ }

/-- `queryOpenings i positions`: the next phase opened against root `i`; the leaves. -/
def queryOpenings (i : Nat) (positions : Array UInt64) : VM (Array (Array UInt64)) := do
  let s ← get
  match s.roots[i]?, s.openings[s.phase]? with
  | some r, some phase =>
    match openPhase r.digest r.height r.width positions phase with
    | some rows => do
      set { s with phase := s.phase + 1 }
      pure rows
    | none => reject
  | _, _ => reject

/-! ## Sumcheck rounds (`transcript.rs`) -/

/-- `grindingBits`, on the statement's constant. -/
abbrev grindingBits (numerator : Nat) : Nat := LeanVM.Protocol.Compile.grindingBits numerator

/-- `sumcheckRoundPoly count claim eq`: the round polynomial, the coefficient the claim fixes
derived, after its grind; constant first. -/
def sumcheckRoundPoly (count : Nat) (claim : EW) : Option EW → VM (Array EW)
  | none => do
    let constant ← readScalar
    let tail ← readScalars (count - 2)
    grind (grindingBits (count - 1))
    pure (#[constant, claim + sumE tail] ++ tail)
  | some eqFactor => do
    let tail ← readScalars (count - 1)
    grind (grindingBits (count - 1 + 1))
    pure (#[claim + eqFactor * sumE tail] ++ tail)

/-- `sumcheck claim count equalities`: a round per entry; the challenges and the final claim. -/
def sumcheck (claim : EW) (count : Nat) (equalities : Array (Option EW)) :
    VM (Array EW × EW) :=
  equalities.foldlM (fun (acc : Array EW × EW) equality ↦ do
    let message ← sumcheckRoundPoly count acc.2 equality
    let challenge ← sampleChallenge
    pure (acc.1.push challenge, polyEval message challenge)) (#[], claim)

/-- `sumcheck` in plain mode, `rounds` rounds. -/
def sumcheckPlain (claim : EW) (count rounds : Nat) : VM (Array EW × EW) :=
  sumcheck claim count (Array.replicate rounds none)

end NativeVm.Model
