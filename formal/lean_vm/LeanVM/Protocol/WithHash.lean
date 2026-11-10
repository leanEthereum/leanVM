/-
  LeanVM.Protocol.WithHash

  The verifier, the honest prover and the random-permutation experiments with Keccak-256 a call of
  its own, beside the permutation: the form the proofs reason in. The statement's are over the
  permutation alone (`Statement/LeanVmVerifier.lean`, `Statement/LeanVm.lean`), Keccak-256 the
  sponge over it; `LeanVM.Protocol.WithHashBridge` proves them these with the sponge for the hash.
-/

module

public import LeanVM.Protocol.Extraction.Extractor

/-!
# The verifier, the prover and the experiments with a hash of their own

Each definition here is the statement's with a hash `H : Bytes → m Digest` beside the permutation
`F`, where the statement hashes with `keccak256With F`: the compiled verifier (`runWithHash`,
`runProofWithHash`, `verifyWithHash`, `verifyDeferredWithHash`), the honest prover
(`proveWithHash`), and the experiments in which Keccak-256 and Keccak-f[1600] are two oracle calls
(`KeccakCalls`) that the model answers (`keccakCallsOverRandomPermutation`: Keccak-256 the sponge
over the lazily sampled permutation, Keccak-f[1600] the permutation), with the adversary's
transcript of permutation queries (`PermutationTranscript`). The random-oracle steps of the proofs
replace the answers to the two calls; the statement's experiments are these, the sponge expanded
(`LeanVM.Protocol.WithHashBridge`).
-/

@[expose] public section

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash

section Run

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KeccakState → m KeccakState)

/-- Climb a Merkle path from `node` at position `q`: at each level the position's low bit says
whether `node` is the left child (`MerklePath::root`, `crates/verifier/src/merkle.rs:30-35`). -/
def climbWithHash : Digest → ℕ → List Digest → m Digest
  | node, _, [] => pure node
  | node, q, s :: ss => do
    let parent ← if q % 2 = 0 then H (digestBytes node ++ digestBytes s)
      else H (digestBytes s ++ digestBytes node)
    climbWithHash parent (q / 2) ss

/-- Check one opening against a root of the given shape at position `q`
(`crates/verifier/src/transcript.rs:171-184`). -/
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
`crates/verifier/src/transcript.rs:153-186`): reject unless every leaf is `width` words and every
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
sponge and every opening authenticated; `none` on rejection. -/
def runWithHash {α : Type} : VerifierProgram α → VerifierProgramState → m (Option (α ×
    VerifierProgramState))
  | .ret a, s => pure (some (a, s))
  | .fail, _ => pure none
  | .read k, s => match s.stream with
    | [] => pure none
    | x :: xs => do
      let sp ← absorb F s.sponge x dsObserve
      runWithHash (k x) { s with sponge := sp, stream := xs }
  | .sample k, s => do
    let (c, sp) ← squeeze F s.sponge
    runWithHash (k c) { s with sponge := sp }
  | .grind bits k, s => match s.stream with
    | [] => pure none
    | n :: xs => do
      let sp ← absorb F s.sponge n dsPowNonce
      let (c, sp) ← squeeze F sp
      if powOk bits n c then runWithHash k { s with sponge := sp, stream := xs } else pure none
  | .commit height width k, s => match s.stream with
    | x0 :: x1 :: xs => do
      let sp ← absorb F s.sponge x0 dsObserve
      let sp ← absorb F sp x1 dsObserve
      match digestFromHalves (x0, x1) with
      | some root =>
        runWithHash k
          { s with sponge := sp, stream := xs, roots := s.roots ++ [(root, height, width)] }
      | none => pure none
    | _ => pure none
  | .query i ps k, s => match s.roots[i]?, s.openings with
    | some (root, height, width), phase :: rest => do
      match ← openPhaseWithHash H root height width ps phase with
      | some rows => runWithHash (k rows) { s with openings := rest }
      | none => pure none
    | _, _ => pure none

/-- Run a program on a proof from a seed state, and accept when it returns `true` with the
stream and the openings fully consumed (`finish`, `transcript.rs:206-216`). -/
def runProofWithHash (P : VerifierProgram Bool) (seed : KeccakState) (π : Proof) : m Bool := do
  match ← runWithHash H F P ⟨⟨seed, []⟩, π.stream, π.openings, []⟩ with
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

/-- **A phase is opened** exactly when every opening has the commitment's shape, the positions are
the queried ones, in order, and every path climbs to the root; the rows are the leaves. -/
theorem openPhaseWithHash_eq_some_iff (root : Digest) (height width : ℕ) (ps : List ℕ)
    (phase : List Opening) (rows : List (List K)) :
    openPhaseWithHash (m := Id) H root height width ps phase = some rows ↔
      (∀ opening ∈ phase, opening.leaf.length = width ∧ opening.path.length = height) ∧
        phase.map Opening.leafIndex = ps ∧
          openAllWithHash (m := Id) H root height width ps phase = some (rows, []) := by
  unfold openPhaseWithHash
  by_cases hc : (∀ opening ∈ phase, opening.leaf.length = width ∧ opening.path.length = height) ∧
      phase.map Opening.leafIndex = ps
  · rw [ite_eq_left hc]
    simp only [bind]
    refine ⟨fun h ↦ ⟨hc.1, hc.2, ?_⟩, fun h ↦ ?_⟩
    · split at h
      · next rows' rest ho =>
        simp only [pure] at h
        cases h
        have hl := (openAllWithHash_length H root height width ps phase ho).1
        have hlen : (phase.map Opening.leafIndex).length = ps.length := by rw [hc.2]
        rw [List.length_map] at hlen
        rw [hlen.symm, List.take_length] at hl
        have : rest = [] := by simpa using hl
        rw [ho, this]
      · simp [pure] at h
    · rw [h.2.2]
      rfl
  · rw [ite_eq_right hc]
    simp only [pure, reduceCtorEq, false_iff]
    exact fun h ↦ hc ⟨h.1, h.2.1⟩

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
(`Bytecode::new`, `crates/verifier/src/bytecode.rs:46-53`). -/
def fiatShamirIvWithHash (bytecode : List K) : m Digest :=
  H (versionTag ++ bytecode.flatMap K.toBytes)

/-- The sponge's initial state with the hash `H` and the permutation `F`: `F` of the IV's and the
public input's words, the other lanes zero (`Sponge::new`, `transcript.rs:33-46`). -/
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
fixed polynomial's value is the one claimed by `c`. Only the bytecode's length is read. -/
def verifyDeferredWithHash (bytecode : List K) (iv publicInput : Digest) (c : BytecodeClaim)
    (π : Proof) : m Bool := do
  let seed ← F (seedInput iv publicInput)
  runProofWithHash H F (deferringVerifierProgram c bytecode publicInput) seed π

end Hash

end LeanVM.Protocol.Verifier

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
  LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

section Monadic

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest)

/-- The leaf digests of the `2^height` rows of a matrix (`hash_words`). -/
def leafDigestsWithHash (height : ℕ) (word : Word) : m (Array Digest) :=
  (Array.range (2 ^ height)).mapM fun i ↦ H ((word i).flatMap K.toBytes)

/-- The first `n` parents of a level: parent `j` hashes nodes `2j` and `2j + 1`
(`hash_pair`). -/
def parentsWithHash (level : Array Digest) (n : ℕ) : m (Array Digest) :=
  (Array.range n).mapM fun j ↦
    H (digestBytes (level.getD (2 * j) default) ++ digestBytes (level.getD (2 * j + 1) default))

/-- The levels of a tree from a level of `2^k` nodes up to the root. -/
def levelsWithHash : ℕ → Array Digest → m (List (Array Digest))
  | 0, level => pure [level]
  | k + 1, level => do
    let up ← parentsWithHash H level (2 ^ k)
    let rest ← levelsWithHash k up
    pure (level :: rest)

/-- The Merkle tree of the `2^height` rows of a matrix. -/
def buildTreeWithHash (height : ℕ) (word : Word) : m Tree := do
  let leaves ← leafDigestsWithHash H height word
  let levels ← levelsWithHash H height leaves
  pure ⟨height, word, levels.toArray⟩

end Monadic

section Run

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KeccakState → m KeccakState)

/-- **The script `S` against the program `P`**, from the sponge `sp` and the trees `cs` committed
so far: the scalars and the openings the proof holds from there on, or `none` if a proof-of-work
search finds no nonce below `fuel`. A rejection, and an opening of a missing commitment, end the
proof. -/
def runFromWithHash (fuel : ℕ) {α β : Type} :
    VerifierProgram α → Option (Script β) → Sponge → List Tree →
      m (Option (List E × List (List Opening)))
  | .ret _, _, _, _ => pure (some ([], []))
  | .fail, _, _, _ => pure (some ([], []))
  | .read k, S, sp, cs => do
    let sp' ← absorb F sp (Script.msgOf S) dsObserve
    let r ← runFromWithHash fuel (k (Script.msgOf S)) (Script.afterSend S) sp' cs
    pure (r.map fun t ↦ (Script.msgOf S :: t.1, t.2))
  | .sample k, S, sp, cs => do
    let r ← squeeze F sp
    runFromWithHash fuel (k r.1) (Script.afterSample r.1 S) r.2 cs
  | .grind bits k, S, sp, cs => do
    match ← findNonceM F bits sp fuel with
    | none => pure none
    | some n => do
      let r ← powStepM F sp n
      let t ← runFromWithHash fuel k (Script.afterGrind S) r.2 cs
      pure (t.map fun t ↦ (n :: t.1, t.2))
  | .commit ht _ k, S, sp, cs => do
    let tree ← buildTreeWithHash H ht (Script.wordOf S)
    let sp0 ← absorb F sp (digestHalves tree.root).1 dsObserve
    let sp1 ← absorb F sp0 (digestHalves tree.root).2 dsObserve
    let r ← runFromWithHash fuel k (Script.afterCommit S) sp1 (cs ++ [tree])
    pure (r.map fun t ↦ ((digestHalves tree.root).1 :: (digestHalves tree.root).2 :: t.1, t.2))
  | .query i ps k, S, sp, cs => match cs[i]? with
    | none => pure (some ([], []))
    | some tree => do
      let rows := ps.map fun q ↦ tree.word (q % 2 ^ tree.height)
      let r ← runFromWithHash fuel (k rows) (Script.afterQuery rows S) sp cs
      pure (r.map fun t ↦ (t.1, ps.map tree.opening :: t.2))

/-- **A proof from a script**: the script run against the program from the seed, or `none` if a
proof-of-work search finds no nonce below `fuel`. -/
def runScriptWithHash (P : VerifierProgram Bool) {β : Type} (S : Script β) (seed : KeccakState)
    (fuel : ℕ) :
    m (Option Proof) := do
  let r ← runFromWithHash H F fuel P (some S) ⟨seed, []⟩ []
  pure (r.map fun t ↦ (⟨t.1, t.2⟩ : Proof))

end Run

/-- **leanVM's honest prover.** The proof of the execution `t` of `prog` on `input` at the rate
`2^-ρ`, trying `fuel` nonces per proof of work; `none` for a trace that is no valid execution
within the cap, an invalid rate, or a proof-of-work search that finds no nonce. -/
def proveWithHash {m : Type → Type} [Monad m] (H : Bytes → m Digest)
    (F : KeccakState → m KeccakState)
    (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ fuel : ℕ) : m (Option
        Proof) :=
  match witness? prog input t with
  | none => pure none
  | some W =>
    if 1 ≤ ρ ∧ ρ ≤ 4 then do
      let seed ← seedWithHash H F (bytecodeWords prog) (publicInputDigest input)
      runScriptWithHash H F (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
        (honestScript W ρ (publicInputDigest input)) seed fuel
    else pure none

end LeanVM.Prover

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open Common (permutationOracleSpec PermutationEdges)
open scoped ENNReal

/-! ### The verifier with a hash, and the oracle calls -/

/-- **The leanVM verifier**, for a hash function `H` and a permutation `F` in any monad `m`: does
`proof` show that `prog` runs on `input`? -/
def verifierWithHash {m : Type → Type} [Monad m] (H : Bytes → m Digest)
    (F : KeccakState → m KeccakState)
    (prog : LeanIsaProgram) (input : PublicInput) (proof : Proof) : m Bool :=
  verifyWithHash H F (bytecodeWords prog) (publicInputDigest input) proof

/-! ### The oracle calls -/

/-- The verifier's and the honest prover's calls: Keccak-256, a function from byte strings to
digests (queries `.inl x`), and Keccak-f[1600], a function from states to states (queries
`.inr s`). What answers them is the model's (`keccakCallsOverRandomPermutation`, below: the sponge
over a random permutation, and the permutation). -/
abbrev KeccakCalls : OracleSpec (Bytes ⊕ KeccakState) :=
  (Bytes →ₒ Digest) + (KeccakState →ₒ KeccakState)

/-- A call to the hash. -/
def callKeccak256 (x : Bytes) : OracleComp KeccakCalls Digest := liftM (KeccakCalls.query (.inl x))

/-- A call to the permutation. -/
def callKeccakF1600 (s : KeccakState) : OracleComp KeccakCalls KeccakState :=
  liftM (KeccakCalls.query (.inr s))


/-- An honest prover: from a statement, an execution, the commitment's rate exponent `ρ` and a
fuel of nonces per proof of work, a proof, or `none` when it makes none, computed with calls to
Keccak-256 and Keccak-f[1600] (`KeccakCalls`), which the model answers. -/
abbrev HonestProverWithHash : Type :=
  (prog : LeanIsaProgram) → (input : PublicInput) → Execution prog → (ρ fuel : ℕ) →
    OracleComp KeccakCalls (Option Proof)

/-- **The honest prover**: `LeanVM.Prover.prove` (`Statement/Prover/Prove.lean`) with Keccak-256 and
Keccak-f[1600] the oracle calls. From the execution `t` it computes the witness (`witness?`, no
proof unless `t` is a valid execution within `2^28` committed cells), and, at a valid rate,
runs the honest script against the verifier's own program `leanVmVerifierProgram`, trying `fuel`
nonces per proof of work. -/
def proverWithHash : HonestProverWithHash :=
  fun prog input t ρ fuel ↦ Prover.proveWithHash callKeccak256 callKeccakF1600 prog input t ρ fuel

/-! ### The random permutation -/

/-- `π x`: a forward query to the lazily sampled uniform permutation
(`Common.lazyRandomPermutation`), whose state is the edges `(x, π x)` fixed so far, newest first.
The model's oracle is `permutationOracleSpec KeccakState`: `π` and `π⁻¹` on Keccak states, a query
`.forward x` or `.inverse y`. -/
noncomputable def lazyPermutationForward (x : KeccakState) :
    StateT (PermutationEdges KeccakState) ProbComp KeccakState :=
  Common.lazyRandomPermutation (.forward x)

/-- **The verifier's calls (`KeccakCalls`) in the random-permutation model**: Keccak-256 is the
sponge over the random permutation, Keccak-f[1600] is the random permutation. -/
noncomputable def keccakCallsOverRandomPermutation :
    QueryImpl KeccakCalls (StateT (PermutationEdges KeccakState) ProbComp)
  | .inl x => keccak256With lazyPermutationForward x
  | .inr s => lazyPermutationForward s

/-! ### The experiment -/

/-- A transcript: queries to `π` and `π⁻¹` with their answers, oldest first. -/
abbrev PermutationTranscript : Type := List (Common.PermutationQuery KeccakState × KeccakState)

/-- The adversary's oracles: a coin is uniform and not recorded; `π` and `π⁻¹` are the lazily
sampled permutation, each query and its answer appended to the transcript. -/
noncomputable def loggedRandomPermutationOracles :
    QueryImpl Common.RandomPermutationOracles
      (StateT (PermutationEdges KeccakState × PermutationTranscript) ProbComp)
  | .inl n => liftM (unifSpec.query n : ProbComp (Fin (n + 1)))
  | .inr q => StateT.mk fun s ↦
    (fun r ↦ (r.1, (r.2, s.2 ++ [(q, r.1)]))) <$> (Common.lazyRandomPermutation q).run s.1

/-- An outcome of the experiment: the statement (`program`, `input`) and the `proof`, the
verdict (`accepted`), and the adversary's `transcript`. -/
abbrev ExperimentOutcomeWithHash : Type :=
  ((ProgramAndInput × Proof) × Bool) × PermutationTranscript

abbrev ExperimentOutcomeWithHash.program (z : ExperimentOutcomeWithHash) : LeanIsaProgram :=
    z.1.1.1.1
abbrev ExperimentOutcomeWithHash.input (z : ExperimentOutcomeWithHash) : PublicInput := z.1.1.1.2
abbrev ExperimentOutcomeWithHash.proof (z : ExperimentOutcomeWithHash) : Proof := z.1.1.2
abbrev ExperimentOutcomeWithHash.accepted (z : ExperimentOutcomeWithHash) : Prop := z.1.2 = true
abbrev ExperimentOutcomeWithHash.transcript (z : ExperimentOutcomeWithHash) :
    PermutationTranscript := z.2

/-- **The random-permutation experiment of an adversary and a computation**: the adversary
against the lazily sampled permutation from no edge, its queries recorded; then a computation `V`
over the verifier's calls on its output, with Keccak-256 the sponge over the same permutation and
Keccak-f[1600] the permutation. The outputs, and the transcript. -/
noncomputable def Rpm.runAdversaryThen {α β : Type}
    (A : OracleComp Common.RandomPermutationOracles α)
    (V : α → OracleComp KeccakCalls β) : ProbComp ((α × β) × PermutationTranscript) := do
  let (z, perms, transcript) ← (simulateQ loggedRandomPermutationOracles A).run ([], [])
  let v ← (simulateQ keccakCallsOverRandomPermutation (V z)).run' perms
  return ((z, v), transcript)

/-- **The random-permutation experiment**: the verifier on the adversary's statement and proof. -/
noncomputable abbrev soundnessExperimentWithHash (A : RandomPermutationAdversary) :
    ProbComp ExperimentOutcomeWithHash :=
  Rpm.runAdversaryThen A fun z ↦ verifierWithHash callKeccak256 callKeccakF1600 z.1.1 z.1.2 z.2


/-- **The extractor in the random-permutation model**: from the statement, the adversary's
transcript and the proof, an execution of the program: the extractor of `Extractor.lean`
(`LeanVM.Extraction.extract`) on the Keccak-256 evaluations of the transcript
(`lookupEvaluation (keccakEvaluationsOfTranscript T)`), the byte strings they answer being those of
the transcript's paths. The paths are computed once. -/
def transcriptExtractorWithHash (prog : LeanIsaProgram) (input : PublicInput) (T :
    PermutationTranscript)
    (proof : Proof) : Option (Execution prog) :=
  let paths := keccakEvaluationsOfTranscript T
  Extraction.extract prog input (bytecodeWords prog) (lookupEvaluation paths)
    (paths.map (·.1)) proof

/-! ### Knowledge soundness -/

/-- **The adversary breaks soundness**: the verifier accepts its statement and proof, and the
execution `transcriptExtractor` extracts from the transcript and the proof is not a valid execution
of the program on the public input. -/
def BreaksKnowledgeSoundnessWithHash (z : ExperimentOutcomeWithHash) : Prop :=
  z.accepted ∧ ¬ ∃ t, transcriptExtractorWithHash z.program z.input z.transcript z.proof = some t ∧
    ValidExecution z.program z.input t

/-- **Knowledge soundness in the random-permutation model**, for the extractor
`transcriptExtractor`: an adversary of at most `Q ≤ 2^128` queries to `π` and `π⁻¹` (its coins free)
breaks soundness with probability at most `(Q + 2^15) · 2^-128 + 5 (Q + 2^15)² · 2^-256`, the `2^14`
covering the verifier's own `18538` oracle calls and two terms of `2^-128` (a guessed stack root,
the transfer from two random oracles to one permutation). -/
def KnowledgeSoundnessWithHash : Prop :=
  ∀ (A : RandomPermutationAdversary) (Q : ℕ),
    Common.QueryCostAtMost A Common.permutationCallCost Q → Q ≤ 2 ^ 128 →
    Pr{let z ← soundnessExperimentWithHash A}[BreaksKnowledgeSoundnessWithHash z] ≤
      (Q + 2 ^ 15 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128 +
        5 * (Q + 2 ^ 15 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256

/-! ### Completeness -/

/-- **The completeness experiment in the random-permutation model**: the honest prover's proof,
then the verifier's verdict on it, both with Keccak-256 the sponge over the lazily sampled
permutation and Keccak-f[1600] the permutation. -/
noncomputable def verifierCompletenessExperimentWithHash (proverWithHash : HonestProverWithHash)
    (prog : LeanIsaProgram)
    (input : PublicInput) (t : Execution prog) (ρ fuel : ℕ) : ProbComp Bool :=
  (simulateQ keccakCallsOverRandomPermutation (do
    match ← proverWithHash prog input t ρ fuel with
    | none => pure false
    | some proof => verifierWithHash callKeccak256 callKeccakF1600 prog input proof)).run' []

/-- **Completeness in the random-permutation model**: trying `2^26` nonces per proof of work, the
honest prover's (`prover`) proof of an execution within the verifier's size cap is rejected with
probability at most `2^-256`. -/
def CompletenessWithHash : Prop :=
  ∀ (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ : ℕ),
    ValidExecution prog input t → t.committedSize ≤ 2 ^ 28 → 1 ≤ ρ ∧ ρ ≤ 4 →
    Pr{let v ← verifierCompletenessExperimentWithHash proverWithHash prog input t ρ
          (2 ^ 26)}[v = false] ≤
      (2 : ℝ≥0∞)⁻¹ ^ 256

end LeanVM

end
