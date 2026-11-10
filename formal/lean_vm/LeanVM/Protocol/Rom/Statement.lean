/-
  LeanVM.Protocol.Rom.Statement

  Knowledge soundness and completeness of the leanVM verifier in the two-oracle random-oracle
  model: a step of the proofs of the statements of `Statement/LeanVm.lean`, not a statement of the
  specification.
-/

module

public import Statement.LeanVm
public import LeanVM.Protocol.Errors
public import LeanVM.Facts.Verifier
public import LeanVM.Protocol.Extraction.Defs
public import Statement.Fast.Keccak
public import Statement.Fast.CubicExt
public import Statement.Fast.FieldWords
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.EvalDist.ProbabilityNotation
public import LeanVM.Protocol.WithHash

/-!
# The two-oracle random-oracle model, a step of the proofs

The statements are in the random-permutation model (`Statement/LeanVm.lean`: `KnowledgeSoundness`,
`Completeness`). Their proofs (`LeanVM/Protocol/LeanVMRpm.lean`) go through the model defined here,
in which Keccak-256 is a lazily sampled random function from byte strings to digests and
Keccak-f[1600] an independent lazily sampled random function from states to states (the calls
`HashSpec` of `Statement/LeanVm.lean`, answered by `HashSpec.randomOracle`): `common`'s
sponge indifferentiability moves an event of the random-permutation experiment to this model at
a cost of `q² / 2^508` for `q` permutation calls (`Common.keccak256_transfer2`).

An adversary here is any computation with access to both oracles that outputs a statement and a
proof (`Adversary`). The experiment runs the adversary, then the verifier on its output, against
one oracle, and records the verdict, the oracle's answers at the end, and the oracle's answers to
the adversary's queries, as they stood when the adversary output its proof (`experiment`).

* `KnowledgeSoundnessRom`: for every adversary of at most `Q` queries, the probability that the
  verifier accepts while the extractor (`extractor`: `LeanVM.Extraction.extract` of
  `LeanVM/Protocol/Extraction/Extractor.lean` on the adversary's cached Keccak-256 answers, the byte strings they
  answer enumerated classically, `Extraction.supportKeys`) does not return a valid execution of the
  program on the public input is at most `soundnessError Q`. Proved:
  `LeanVM.knowledgeSoundnessRom_holds` (`LeanVM/Protocol/LeanVMSound.lean`).
* `CompletenessRom`: there is an honest prover which, given a valid execution whose committed size
  is at most `2^32`, at an inverse rate `2^ρ` with `1 ≤ ρ ≤ 4`, trying at most `fuel ≤ 2^64` nonces
  per proof of work, makes the verifier reject with probability at most `completenessError fuel`.
  Proved: `LeanVM.completenessRom_holds` (`LeanVM/Protocol/LeanVM.lean`).
-/

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

/-! ## The experiment -/

/-- An adversary of the random-oracle model: a computation with oracle access to the two random
oracles that outputs a statement and a proof. -/
abbrev Adversary : Type := OracleComp KeccakCalls (ProgramAndInput × Proof)

/-- An outcome of the experiment: the statement and the proof, the verdict, the oracle's answers
at the end (to the adversary's queries and the verifier's), and the oracle's answers when the
adversary returned (to the adversary's queries). -/
abbrev Outcome : Type :=
  ((ProgramAndInput × Proof) × Bool) × KeccakCalls.QueryCache × KeccakCalls.QueryCache

/-- The outcome's program. -/
abbrev Outcome.program (z : Outcome) : LeanIsaProgram := z.1.1.1.1

/-- The outcome's public input. -/
abbrev Outcome.input (z : Outcome) : PublicInput := z.1.1.1.2

/-- The outcome's proof. -/
abbrev Outcome.proof (z : Outcome) : Proof := z.1.1.2

/-- The verifier accepted. -/
abbrev Outcome.accepted (z : Outcome) : Prop := z.1.2 = true

/-- The verifier rejected. -/
abbrev Outcome.rejected (z : Outcome) : Prop := z.1.2 = false

/-- The oracle's answers to the adversary's queries: the cache when the adversary returned,
before the verifier ran. -/
abbrev Outcome.adversaryCache (z : Outcome) : KeccakCalls.QueryCache := z.2.2

/-- **The random-oracle experiment**: the adversary from the empty cache, then the verifier on its
statement and proof, continuing from the cache the adversary left: one lazily sampled random
oracle. -/
noncomputable def experiment (A : Adversary) : ProbComp Outcome := do
  let (z, adversaryCache) ← (simulateQ KeccakCalls.randomOracle A).run ∅
  let (verdict, cache) ←
    (simulateQ KeccakCalls.randomOracle (verifierWithHash callKeccak256 callKeccakF1600 z.1.1 z.1.2 z.2)).run adversaryCache
  return ((z, verdict), cache, adversaryCache)

/-! ## Knowledge soundness -/

/-- An extractor of the random-oracle model: from the oracle's answers to the adversary's queries
and the proof, an execution of the program. -/
abbrev Extractor : Type :=
  (prog : LeanIsaProgram) → PublicInput → KeccakCalls.QueryCache → Proof → Option (Execution prog)

/-- **The extractor of the random-oracle model** (`LeanVM.Extraction.extract`,
`LeanVM/Protocol/Extraction/Extractor.lean`) on the adversary's cached Keccak-256 answers, with the byte strings
they answer as its keys (a classical enumeration, `Extraction.supportKeys`, of a support that is
finite on every reachable cache; the extraction does not depend on which covering keys it is
given, `ExtractProofs.extract_keys_congr`). -/
noncomputable def extractor : Extractor := fun prog input answers proof ↦
  Extraction.extract prog input (bytecodeWords prog) (fun x ↦ answers (.inl x))
    (Extraction.supportKeys fun x ↦ answers (.inl x)) proof

/-- **The adversary breaks soundness**: the verifier accepts its statement and proof, and the
execution extracted from the adversary's answers and the proof is not a valid execution of the
program on the public input. -/
def Breaks (extract : Extractor) (z : Outcome) : Prop :=
  z.accepted ∧ ¬ ∃ t, extract z.program z.input z.adversaryCache z.proof = some t ∧
    ValidExecution z.program z.input t

/-- **Knowledge soundness in the two-oracle random-oracle model**, for the extractor
`extractor`. -/
def KnowledgeSoundnessRom : Prop :=
  ∀ (A : Adversary) (Q : ℕ), A.IsTotalQueryBound Q →
    Pr{let z ← experiment A}[Breaks extractor z] ≤ soundnessError Q

/-! ## Completeness -/

/-- **Completeness in the two-oracle random-oracle model.** The experiment takes a proof: no
proof (`none`) enters it as the empty proof, which the verifier rejects. -/
def CompletenessRom : Prop :=
  ∃ prover : HonestProverWithHash, ∀ (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ fuel : ℕ),
    ValidExecution prog input t →
    t.committedSize ≤ 2 ^ 32 → 1 ≤ ρ ∧ ρ ≤ 4 → fuel ≤ 2 ^ 64 →
    Pr{let z ← experiment
        ((fun proof ↦ ((prog, input), proof.getD ⟨[], []⟩)) <$> prover prog input t ρ fuel)}[
      z.rejected] ≤ completenessError fuel

end
end LeanVM
