/-
  LeanVM.Protocol.Rom.Statement

  Knowledge soundness of the leanVM verifier in the two-oracle random-oracle model: a step of the
  proof of `LeanVM.KnowledgeSoundness` (`Statement/LeanVm.lean`), not a statement of the
  specification.
-/

module

public import Statement.LeanVm
public import LeanVM.Protocol.WithHash
public import LeanVM.Protocol.Verifier.Cost
public import LeanVM.Protocol.Extraction.Defs
public import LeanVM.Protocol.Relation.ExtractorDef
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
public import VCVio.EvalDist.ProbabilityNotation

/-!
# The two-oracle random-oracle model, a step of the proof

The end statement is in the random-permutation model (`Statement/LeanVm.lean`,
`KnowledgeSoundness`). Its proof goes through the model defined here, in which Keccak-256 is a
lazily sampled random function from byte strings to digests and Keccak-f[1600] an independent
lazily sampled random function from states to states (the calls `KeccakCalls`, answered by
`KeccakCalls.randomOracle`): `common`'s sponge indifferentiability moves an event of the
random-permutation experiment to this model at a cost of `q² / 2^508` for `q` permutation calls
(`Common.keccak256_transfer2`; `LeanVM/Protocol/LeanVMRpmAS.lean`).

An adversary here is any computation with access to both oracles that outputs a statement and a
proof (`Adversary`). The experiment runs the adversary, then the verifier on its output, against
one oracle, and records the verdict, the oracle's answers at the end, and the oracle's answers to
the adversary's queries, as they stood when the adversary output its proof (`experiment`).

* `Breaks extract`: the verifier accepts while the extractor `extract` (from the adversary's cached
  answers and the proof) does not return a valid execution of the program on the public input.
* `KnowledgeSoundnessRom extract ε`: an adversary of at most `Q` queries breaks it with
  probability at most `ε Q`.
* `extractorAS`: the agreement-set extractor (`Relation.extractAS`) on the adversary's cached
  answers, and `soundnessErrorAS`, its error: the random-oracle theorem's
  `(Q + V) · (2^-125 + 5 (Q + V) / 2^256)` at `V = leanVmQueryBound`, a fresh hit of the final
  query's proof of work (`2^-127`, once), and a fresh hash answer of the verifier that is a root
  the replay reads (`romRootCap · 2^-256` per verifier query). `knowledgeSoundnessRomAS`, the
  statement `KnowledgeSoundnessRom extractorAS soundnessErrorAS`, is the random-oracle step.
-/

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol
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

/-- The oracle's answers to the adversary's queries: the cache when the adversary returned,
before the verifier ran. -/
abbrev Outcome.adversaryCache (z : Outcome) : KeccakCalls.QueryCache := z.2.2

/-- **The random-oracle experiment**: the adversary from the empty cache, then the verifier on its
statement and proof, continuing from the cache the adversary left: one lazily sampled random
oracle. -/
noncomputable def experiment (A : Adversary) : ProbComp Outcome := do
  let (z, adversaryCache) ← (simulateQ KeccakCalls.randomOracle A).run ∅
  let (verdict, cache) ← (simulateQ KeccakCalls.randomOracle
    (verifierWithHash callKeccak256 callKeccakF1600 z.1.1 z.1.2 z.2)).run adversaryCache
  return ((z, verdict), cache, adversaryCache)

/-! ## Knowledge soundness -/

/-- An extractor of the random-oracle model: from the oracle's answers to the adversary's queries
and the proof, an execution of the program. -/
abbrev Extractor : Type :=
  (prog : LeanIsaProgram) → PublicInput → KeccakCalls.QueryCache → Proof → Option (Execution prog)

/-- **The adversary breaks soundness**: the verifier accepts its statement and proof, and the
execution extracted from the adversary's answers and the proof is not a valid execution of the
program on the public input. -/
def Breaks (extract : Extractor) (z : Outcome) : Prop :=
  z.accepted ∧ ¬ ∃ t, extract z.program z.input z.adversaryCache z.proof = some t ∧
    ValidExecution z.program z.input t

/-- **Knowledge soundness in the two-oracle random-oracle model**, for the extractor `extract`
with the error `ε`: an adversary of at most `Q` oracle queries breaks soundness with probability
at most `ε Q`. -/
def KnowledgeSoundnessRom (extract : Extractor) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (A : Adversary) (Q : ℕ), A.IsTotalQueryBound Q →
    Pr{let z ← experiment A}[Breaks extract z] ≤ ε Q

/-! ## The agreement-set extractor and its error -/

/-- **The agreement-set extractor of the random-oracle model** (`Relation.extractAS`), on the
adversary's cached answers: the hash answers, their inputs enumerated (`supportKeys`), and the
permutation answers. -/
noncomputable def extractorAS : Extractor := fun prog input answers π ↦
  Relation.extractAS prog input (fun x ↦ answers (.inl x))
    (Extraction.supportKeys fun x ↦ answers (.inl x)) (fun t ↦ answers (.inr t)) π

/-- The roots the extractor's replay may read, at most: one per two quarters of the verifier
program's cost (`leanVmCost`), a commitment costing more. -/
def romRootCap : ℕ := leanVmCost / 2

/-- **The knowledge-soundness error for the agreement-set extractor**: the random-oracle theorem's
at `leanVmQueryBound` verifier queries, a fresh hit of the final proof of work (`2^-127`, once),
and a fresh hash answer of the verifier that is a root the replay reads (`romRootCap · 2^-256` per
verifier query). -/
noncomputable def soundnessErrorAS (Q : ℕ) : ℝ≥0∞ :=
  ((Q + leanVmQueryBound : ℕ) : ℝ≥0∞) *
      ((2 : ℝ≥0∞)⁻¹ ^ 125 + ((5 * (Q + leanVmQueryBound) : ℕ) : ℝ≥0∞) / 2 ^ 256) +
    (2 : ℝ≥0∞)⁻¹ ^ 127 + (leanVmQueryBound : ℝ≥0∞) * (romRootCap * (2 ^ 256 : ℝ≥0∞)⁻¹)

end
end LeanVM
