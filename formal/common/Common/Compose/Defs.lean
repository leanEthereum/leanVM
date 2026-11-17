module

public import Statement.Corollaries
public import Common.MultiKey.Defs

@[expose] public section

/-!
# The composed system: leanVM's aggregation over the signatures of honest keys

An aggregator proves with leanVM that a guest program accepted signatures; the composition asks
what an accepted proof says of signatures under keys whose signers are honest. The adversary
(`ComposedAdversary`) gets `k` honest public keys of one signature scheme, flips coins, queries
the proof system's permutation `π` and `π⁻¹`, the scheme's permutation `π_h` and `π_h⁻¹`, and asks
any key to sign; it outputs a statement and a proof.

**Two permutations.** The straight-line extractor of `AggregateSound` reads the knowledge-soundness
adversary's transcript. If the honest keys and signers hashed over the proof system's `π`, their
queries would be in that transcript and no forger against the signature scheme (which sees
neither the honest key generation's and signers' queries nor their seeds) could recompute the
extraction. So the scheme hashes over a second, independent random permutation `π_h`.

**What this idealises beyond the statement.** The statement models the proof system's hash and
each scheme's hash as the one permutation `π`; here they are two independent random permutations,
while deployed both are built from the same Keccak-f[1600]. The theorem is about soundness only:
an honest signature over `π_h` generally fails the deployed verification, so nothing here says an
honest aggregate is accepted. It speaks of the raw signatures the node holds directly; claims held
through children stay with soundness across recursion levels, which is not proved.

**The experiment** (`composedExperiment`) is the knowledge-soundness experiment of the wrapped
adversary `honest scheme k A`, whose `π_h` is lazily sampled with coins inside the computation:
the keys are generated, the adversary's `π_h` queries and requests answered over that `π_h`, every
coin it draws for them landing in the transcript as a coin. The extractor reads the transcript
only through its permutation queries (`ExtractorReadsPermutationQueries`, which
`LeanVM.extractorComputedBy` satisfies: `extractorComputedBy_readsPermutationQueries`), so those
coins are not read. Then the verifier, the decoded witness's raw signature under an honest key
(`candidate`) and its verification over `π_h` (`verdictRun`).

**The hypothesis on the deployed Keccak.** The node's relation checks a raw signature with the
deployed Keccak (`deployedVerify`), the scheme's game with `π_h`. "The deployed verification
behaves like the ideal one" for all adversaries is false (an unbounded adversary computes the
deployed Keccak, a fixed function), so it is a hypothesis about one adversary
(`KeccakVerificationLikeIdeal`): the probability that the decoded witness holds a fresh raw
signature under an honest key, accepted by the deployed verification, that the verification over
`π_h` rejects. Only raw signatures the decoded witness holds directly are read, not claims held
through children.
-/

open OracleComp OracleSpec
open scoped ENNReal
open LeanVM LeanVM.Node LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile
open Common.SufCma

namespace Common.Compose

variable {Seed PK SK Req Resp F : Type}

/-! ## The adversary -/

/-- **The composed system's oracles**: coins, `π` and `π⁻¹` (the proof system's), `π_h` and
`π_h⁻¹` (the signature scheme's), and signing requests `(j, r)` to key `j`. -/
abbrev ComposedOracles (k : ℕ) (Req Resp : Type) :=
  RandomPermutationOracles + permutationOracleSpec KeccakState + (Fin k × Req →ₒ Resp)

/-- **An adversary of the composed system**: from `k` honest public keys, a computation over the
composed oracles that outputs a statement and a proof. -/
abbrev ComposedAdversary (k : ℕ) (PK Req Resp : Type) : Type :=
  (Fin k → PK) → OracleComp (ComposedOracles k Req Resp) (ProgramAndInput × Proof)

/-- The queries of the composed system: coins, `π` and `π⁻¹`, `π_h` and `π_h⁻¹`, requests. -/
abbrev ComposedQuery (k : ℕ) (Req : Type) :=
  (RandomPermutationOracles.Domain ⊕ PermutationQuery KeccakState) ⊕ (Fin k × Req)

/-- A call of `π` or `π⁻¹` costs one; a coin, a call of `π_h` and a request nothing. -/
def piCost {k : ℕ} : ComposedQuery k Req → ℕ
  | .inl (.inl t) => permutationCallCost t
  | _ => 0

/-- A call of `π_h` or `π_h⁻¹` costs one; a coin, a call of `π` and a request nothing. -/
def piHCost {k : ℕ} : ComposedQuery k Req → ℕ
  | .inl (.inr _) => 1
  | _ => 0

/-- A request to key `j` costs one; anything else nothing. -/
def requestToKey {k : ℕ} (j : Fin k) : ComposedQuery k Req → ℕ
  | .inr r => if r.1 = j then 1 else 0
  | _ => 0

/-! ## The honest side, over `π_h` sampled with coins -/

variable (scheme : Scheme Seed PK SK Req Resp F) (k : ℕ)

/-- **The honest keys**: a seed per key, then the keys generated over `π_h`, lazily sampled from no
edge; with `π_h`'s edges. -/
noncomputable def honestKeys :
    ProbComp (((Fin k → PK) × (Fin k → SK)) × PermutationEdges KeccakState) := do
  let seeds ← (scheme.multiKey k).sampleSeed
  (simulateQ lazyRandomPermutationOracles ((scheme.multiKey k).generateKeys seeds)).run []

/-- **The honest side's answers** to the adversary, inside the proof system's world, the state
`π_h`'s edges and the request log: coins and `π` forwarded; a query of `π_h` answered by the lazy
permutation on `π_h`'s edges, a request `(j, r)` by key `j`'s signer over `π_h` (and logged), each
run with the world's coins. -/
noncomputable def honestOracles (sks : Fin k → SK) :
    QueryImpl (ComposedOracles k Req Resp)
      (StateT (PermutationEdges KeccakState × QueryLog (Fin k × Req →ₒ Resp))
        (OracleComp RandomPermutationOracles))
  | .inl (.inl t) => StateT.lift (liftM (RandomPermutationOracles.query t))
  | .inl (.inr q) => StateT.mk fun s ↦
      (fun z ↦ (z.1, (z.2, s.2))) <$>
        (liftM ((lazyRandomPermutation q).run s.1) : OracleComp RandomPermutationOracles _)
  | .inr r => StateT.mk fun s ↦
      (fun z ↦ (z.1, (z.2, s.2 ++ [⟨r, z.1⟩]))) <$>
        (liftM ((simulateQ lazyRandomPermutationOracles (scheme.sign (sks r.1) r.2)).run s.1) :
          OracleComp RandomPermutationOracles _)

/-- **The wrapped adversary**: the honest keys, then the adversary answered by the honest side;
its output, the public keys, the request log and `π_h`'s edges. -/
noncomputable def honest (A : ComposedAdversary k PK Req Resp) :
    OracleComp RandomPermutationOracles
      ((ProgramAndInput × Proof) × (Fin k → PK) × QueryLog (Fin k × Req →ₒ Resp) ×
        PermutationEdges KeccakState) :=
  (liftM (honestKeys scheme k) : OracleComp RandomPermutationOracles _) >>= fun keys ↦
    (fun y ↦ (y.1, keys.1.1, y.2.2, y.2.1)) <$>
      (simulateQ (honestOracles scheme k keys.1.2) (A keys.1.1)).run (keys.2, [])

/-- **The verdict over `π_h`** on a candidate forgery `(j, f)`: key `j`'s verification of `f`,
over `π_h` from its edges `edges`; `false` on no candidate. -/
noncomputable def verdictRun (pks : Fin k → PK) (c : Option (Fin k × F))
    (edges : PermutationEdges KeccakState) : ProbComp Bool :=
  match c with
  | none => pure false
  | some (j, f) => (simulateQ lazyRandomPermutationOracles (scheme.verify (pks j) f)).run' edges

/-! ## The decoded witness's raw signature under an honest key -/

variable (guest : LeanIsaProgram) (decoder : Cost.MachineProgram)
  (extractor : StraightLineExtractor) (raws : NodeWitness → List (PK × F))
  (deployedVerify : PK → F → Bool)

/-- **A raw signature of the decoded witness under honest key `j`, fresh**: the outcome's program
is the guest; the extractor extracts an execution from the outcome, on which the decoder program
outputs a decoding under the deployed seed, of a statement the public input commits to, whose
deferred claim holds and whose witness holds it (`NodeRelation`); and `(pks j, f)` is a raw
signature of that witness, accepted by the deployed verification, that wins against key `j`'s
transcript (`scheme.winningCondition`). -/
def IsCandidate (o : ExperimentOutcome) (pks : Fin k → PK) (log : QueryLog (Fin k × Req →ₒ Resp))
    (j : Fin k) (f : F) : Prop :=
  o.program = guest ∧ ∃ execution, ∃ decoding : SeedStatementAndWitness,
    extractor o.program o.input o.transcript o.proof = some execution ∧
    Cost.outputWithin decoder guestWitnessDecoderSizeBound (guestWitnessDecoderBudget execution)
      (Cost.encodeGuestWitnessDecoderInput o.program execution) =
        some (Cost.encodeValue decoding) ∧
    decoding.seed = deployedSeed guest ∧
    publicInputDigest o.input = statementDigest (deployedSeed guest) decoding.statement ∧
    decoding.statement.deferredClaim.HoldsWithShape (bytecodeWords guest) ∧
    NodeRelation (bytecodeWords guest) (deployedSeed guest) decoding.statement decoding.witness ∧
    (pks j, f) ∈ raws decoding.witness ∧ deployedVerify (pks j) f = true ∧
    scheme.winningCondition (keyLog j log) f = true

open Classical in
/-- **The candidate forgery**: a key `j` and a raw signature `f` with `IsCandidate`, chosen;
`none` when there is none. -/
noncomputable def candidate (o : ExperimentOutcome) (pks : Fin k → PK)
    (log : QueryLog (Fin k × Req →ₒ Resp)) : Option (Fin k × F) :=
  if h : ∃ j f, IsCandidate scheme k guest decoder extractor raws deployedVerify o pks log j f then
    some (h.choose, h.choose_spec.choose)
  else none

/-! ## The experiment and the hypothesis -/

/-- **The composed experiment**, in the knowledge-soundness world: the wrapped adversary
`honest scheme k A`, its queries recorded, then the verifier over `π` on its statement and proof,
the candidate forgery and its verdict over `π_h`, the whole run against the lazily sampled `π`
from no edge. The outcome, the public keys, the request log, the candidate and the verdict. -/
noncomputable def composedExperiment (A : ComposedAdversary k PK Req Resp) :
    ProbComp (ExperimentOutcome × (Fin k → PK) × QueryLog (Fin k × Req →ₒ Resp) ×
      Option (Fin k × F) × Bool) :=
  runWithRandomPermutation do
    let ((((program, input), proof), pks, log, edges), transcript) ←
      (simulateQ loggedOracles (honest scheme k A)).run []
    let accepted ← leanVmVerifier queryPermutation program input proof
    let o : ExperimentOutcome := ⟨program, input, proof, accepted, transcript⟩
    let c := candidate scheme k guest decoder extractor raws deployedVerify o pks log
    let verdict ← (liftM (verdictRun scheme k pks c edges) : OracleComp RandomPermutationOracles _)
    return (o, pks, log, c, verdict)

/-- **The deployed Keccak's verification behaves like the ideal one, for this adversary's raw
signatures, up to `δ`**: in the composed experiment, the probability that the decoded witness
holds a fresh raw signature under an honest key, accepted by the deployed verification
(`candidate`), that the verification over `π_h` rejects, is at most `δ`. -/
def KeccakVerificationLikeIdeal (A : ComposedAdversary k PK Req Resp) (δ : ℝ≥0∞) : Prop :=
  Pr{let z ← composedExperiment scheme k guest decoder extractor raws deployedVerify A}[
    z.2.2.2.1.isSome ∧ z.2.2.2.2 = false] ≤ δ

/-! ## The extractor reads permutation queries only -/

/-- **The extractor reads the transcript only through its permutation queries.** -/
def ExtractorReadsPermutationQueries (extractor : StraightLineExtractor) : Prop :=
  ∀ program input t t' proof, permutationQueries t = permutationQueries t' →
    extractor program input t proof = extractor program input t' proof

/-- The extractor a cost-machine program computes reads the transcript only through its
permutation queries. -/
theorem extractorComputedBy_readsPermutationQueries (P : Cost.MachineProgram) :
    ExtractorReadsPermutationQueries (extractorComputedBy P) := by
  intro program input t t' proof h
  simp only [extractorComputedBy, Cost.encodeLeanVmKnowledgeExtractorInput, h]

end Common.Compose
