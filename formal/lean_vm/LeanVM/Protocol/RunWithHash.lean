/-
  LeanVM.Protocol.RunWithHash

  The compiled verifier with Keccak-256 a call of its own, beside the permutation: the run, the
  seed and the verifier with a hash `H` (`LeanVM.Protocol.WithHash` adds the honest prover and the
  experiments). Imported by the executables (`leanvm-verify`) without the proofs.
-/

module

public import Statement.LeanVmVerifier

/-!
# The verifier with a hash of its own

Each definition here is the statement's with a hash `H : Bytes → m Digest` beside the permutation
`F`, where the statement hashes with `keccak256With F`: the compiled verifier (`runWithHash`,
`runProofWithHash`, `verifyWithHash`, `verifyDeferredWithHash`) and its seed (`seedWithHash`).
-/

@[expose] public section

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash

section Run

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KeccakState → m KeccakState)

/-- Climb a Merkle path from `node` at position `q`: at each level the position's low bit says
whether `node` is the left child (`MerklePath::root`, `crates/verifier/src/merkle.rs:28-38`). -/
def climbWithHash : Digest → ℕ → List Digest → m Digest
  | node, _, [] => pure node
  | node, q, s :: ss => do
    let parent ← if q % 2 = 0 then H (digestBytes node ++ digestBytes s)
      else H (digestBytes s ++ digestBytes node)
    climbWithHash parent (q / 2) ss

/-- Check one opening against a root of the given shape at position `q`
(`crates/verifier/src/transcript.rs:197-210`). -/
def openOneWithHash (root : Digest) (height width q : ℕ) (o : Opening) : m Bool :=
  if o.leaf.length = width ∧ o.path.length = height then do
    let leafDigest ← H (o.leaf.flatMap K.toBytes)
    let top ← climbWithHash H leafDigest q o.path
    pure (decide (top.toList = root.toList))
  else pure false

/-- Open every position in order, consuming one opening each; the leaves, and the openings
left. -/
def openAllWithHash (root : Digest) (height width : ℕ) :
    List ℕ → List Opening → m (Option (List (List K) × List Opening))
  | [], os => pure (some ([], os))
  | _ :: _, [] => pure none
  | q :: qs, o :: os => do
    if ← openOneWithHash H root height width q o then
      let rest ← openAllWithHash root height width qs os
      pure (rest.map fun r ↦ (o.leaf :: r.1, r.2))
    else pure none

/-- Open one phase of a commitment of the given shape at `positions` (`Transcript::merkle`,
`crates/verifier/src/transcript.rs:179-212`): reject unless every leaf is `width` words and every
path `height` siblings, then unless the phase's positions are `positions`, in order, then unless
each path climbs to `root`, in order. The leaves. -/
def openPhaseWithHash (root : Digest) (height width : ℕ) (positions : List ℕ)
    (phase : List Opening) : m (Option (List (List K))) :=
  if (∀ opening ∈ phase, opening.leaf.length = width ∧ opening.path.length = height) ∧
      phase.map Opening.leafIndex = positions then do
    match ← openAllWithHash H root height width positions phase with
    | some (rows, _) => pure (some rows)
    | none => pure none
  else pure none

/-- The compiled reading of a program: run it on the state, every challenge squeezed out of the
sponge and every opening authenticated; `none` on rejection. As the statement's `run`: what absorbs
rejects while a grind's challenge waits, and a proof of work absorbs its nonce and permutes
(`absorbNonce`). -/
def runWithHash {α : Type} : VerifierProgram α → VerifierProgramState → m (Option (α ×
    VerifierProgramState))
  | .ret a, s => pure (some (a, s))
  | .fail, _ => pure none
  | .read k, s => match s.stream, s.sponge.ground with
    | x :: xs, none => do
      let sp ← absorb F s.sponge x dsObserve
      runWithHash (k x) { s with sponge := sp, stream := xs }
    | _, _ => pure none
  | .sample k, s => do
    let (c, sp) ← squeeze F s.sponge
    runWithHash (k c) { s with sponge := sp }
  | .grind bits k, s => match s.stream, s.sponge.ground with
    | n :: xs, none => do
      let (pow, sp) ← absorbNonce F s.sponge n
      if powOk bits pow then runWithHash k { s with sponge := sp, stream := xs } else pure none
    | _, _ => pure none
  | .commit height width k, s => match s.stream, s.sponge.ground with
    | x0 :: x1 :: xs, none => do
      let sp ← absorb F s.sponge x0 dsObserve
      let sp ← absorb F sp x1 dsObserve
      let roots := s.roots ++ [(digestFromHalves (x0, x1), height, width)]
      runWithHash k { s with sponge := sp, stream := xs, roots := roots }
    | _, _ => pure none
  | .query i ps k, s => match s.roots[i]?, s.openings with
    | some (root, height, width), phase :: rest => do
      match ← openPhaseWithHash H root height width ps phase with
      | some rows => runWithHash (k rows) { s with openings := rest }
      | none => pure none
    | _, _ => pure none

/-- Run a program on a proof from a seed state, and accept when it returns `true` with the
stream and the openings fully consumed (`finish`, `transcript.rs:239-249`). -/
def runProofWithHash (P : VerifierProgram Bool) (seed : KeccakState) (π : Proof) : m Bool := do
  match ← runWithHash H F P ⟨⟨seed, [], none⟩, π.stream, π.openings, []⟩ with
  | some (true, s) => pure (s.stream.isEmpty && s.openings.isEmpty)
  | _ => pure false

end Run

/-! ### Reading a `query` in `Id` -/

section RunId

variable (H : Bytes → Id Digest) (F : KeccakState → Id KeccakState)

/-- Opening a list of positions consumes one opening per position. -/
theorem openAllWithHash_length (root : Digest) (height width : ℕ) :
    ∀ (ps : List ℕ) (os : List Opening) {rows : List (List K)} {rest : List Opening},
      openAllWithHash (m := Id) H root height width ps os = some (rows, rest) →
        os = os.take ps.length ++ rest ∧ rows = (os.take ps.length).map Opening.leaf
  | [], os, rows, rest, h => by
    simp only [openAllWithHash, pure] at h
    cases h
    simp
  | _ :: _, [], _, _, h => by simp [openAllWithHash, pure] at h
  | q :: qs, o :: os, rows, rest, h => by
    simp only [openAllWithHash, bind, pure] at h
    split at h
    · obtain ⟨⟨rows', rest'⟩, h', he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨h1, h2⟩ := openAllWithHash_length root height width qs os h'
      refine ⟨?_, ?_⟩
      · simp only [List.length_cons, List.take_succ_cons, List.cons_append]
        exact congrArg (o :: ·) h1
      · simp [h2]
    · simp at h

/-- **A `query` runs** exactly when its commitment is read, a phase of openings is left, the phase
is opened, and the continuation runs on the rest. -/
theorem runWithHash_query_eq_some_iff {α : Type} (i : ℕ) (ps : List ℕ)
    (k : List (List K) → VerifierProgram α) (s : VerifierProgramState)
    (r : α × VerifierProgramState) :
    runWithHash (m := Id) H F (.query i ps k) s = some r ↔
      ∃ root height width phase rest rows, s.roots[i]? = some (root, height, width) ∧
        s.openings = phase :: rest ∧
        openPhaseWithHash (m := Id) H root height width ps phase = some rows ∧
        runWithHash (m := Id) H F (k rows) { s with openings := rest } = some r := by
  simp only [runWithHash]
  rcases hr : s.roots[i]? with _ | ⟨root, height, width⟩ <;>
    rcases ho : s.openings with _ | ⟨phase, rest⟩
  · simp [pure]
  · simp [pure]
  · simp [pure]
  · constructor
    · intro h
      simp only [bind] at h
      split at h
      · next rows hp => exact ⟨root, height, width, phase, rest, rows, rfl, rfl, hp, h⟩
      · simp [pure] at h
    · rintro ⟨root', height', width', phase', rest', rows, h1, h2, hp, h⟩
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq] at h1 h2
      obtain ⟨rfl, rfl, rfl⟩ := h1
      obtain ⟨rfl, rfl⟩ := h2
      simp only [bind]
      rw [hp]
      exact h

end RunId

end LeanVM.Protocol.Compile

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters
open LeanVM.Semantics LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile

section Hash

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KeccakState → m KeccakState)

/-- The IV with the hash `H`: the hash of the tag, then the bytecode as its little-endian words
(`Bytecode::new`, `crates/verifier/src/bytecode.rs:45-53`). -/
def fiatShamirIvWithHash (bytecode : List K) : m Digest :=
  H (versionTag ++ bytecode.flatMap K.toBytes)

/-- The sponge's initial state with the hash `H` and the permutation `F`: `F` of the IV's and the
public input's words, the other lanes zero (`Sponge::new`, `transcript.rs:36-49`). -/
def seedWithHash (bytecode : List K) (publicInput : Digest) : m KeccakState := do
  let fiatShamirIv ← fiatShamirIvWithHash H bytecode
  F (seedInput fiatShamirIv publicInput)

/-- The compiled verifier with the hash `H` and the permutation `F`: the program run on the proof
from the seed. -/
def verifyWithHash (bytecode : List K) (publicInput : Digest) (π : Proof) : m Bool := do
  let seed ← seedWithHash H F bytecode publicInput
  runProofWithHash H F (leanVmVerifierProgram bytecode publicInput) seed π

/-- **The deferring verifier** with the hash `H` and the permutation `F`, as an aggregate runs it
on a child's proof (`verify_sub`): the IV is given rather than hashed from the bytecode, and the
fixed polynomial's point and value are held to `c`. Only the bytecode's length is read. -/
def verifyDeferredWithHash (bytecode : List K) (iv publicInput : Digest) (c : BytecodeClaim)
    (π : Proof) : m Bool := do
  let seed ← F (seedInput iv publicInput)
  runProofWithHash H F (deferringVerifierProgram c bytecode publicInput) seed π

end Hash

end LeanVM.Protocol.Verifier

end
