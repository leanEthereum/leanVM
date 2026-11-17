module

public import Common.Compose.Main
public import XmssSecurity.MultiKey
public import Sphincs.MultiKey
public import Statement.Corollaries

@[expose] public section

/-!
# The conditional composition theorem for leanXMSS and leanSPHINCS

`Common.Compose.composed_sound` (`common/Common/Compose/Main.lean`) for the aggregation guest
(`guestProgram`), a decoder program `D` and the extractor a program `P` computes
(`extractorComputedBy P`), instantiated with each signature scheme the node checks raw signatures
of:

* `AggregateRawXmssSignaturesGenuineIfKeccakLikeIdeal`, proved from `AggregateSound` by
  `aggregate_raw_xmss_signatures_genuine_if_keccak_like_ideal_of_aggregateSound`: leanXMSS
  (`LeanXmss.RandomPermutationModel.sufCmaScheme`), its multi-key bound
  `XmssSecurity.leanXmss_multiKey`, the raw signatures `xmssRaws` and their deployed verification
  `xmssDeployedVerify`;
* `AggregateRawSphincsSignaturesGenuineIfKeccakLikeIdeal`, proved from `AggregateSound` by
  `aggregate_raw_sphincs_signatures_genuine_if_keccak_like_ideal_of_aggregateSound`: leanSPHINCS
  (`Sphincs.RandomPermutationModel.sufCmaScheme`), its multi-key bound
  `Sphincs.leanSphincs_multiKey`, the raw signatures `sphincsRaws` and their deployed verification
  `sphincsDeployedVerify`.

The propositions are conditional on the deployed Keccak's verification behaving like the ideal one
for the adversary at hand (`KeccakVerificationLikeIdeal`), and the theorems also on `AggregateSound`
for `guestProgram`, `D` and `extractorComputedBy P` (discharged in the root module). The
composition's model has two independent random permutations, the proof system's `π` and the
scheme's `π_h`, while deployed both are Keccak-f[1600]; the propositions are about soundness only,
and about the raw signatures the node holds directly, not the claims it holds through its children.

The extractor reads the transcript only through its permutation queries
(`Common.Compose.extractorComputedBy_readsPermutationQueries`), and every raw signature of a witness
holding a statement is accepted by the deployed verification (`xmssRaws_verify`,
`sphincsRaws_verify`): it is the first two conjuncts of `SignatureClaimsHeld`.
-/

open OracleComp OracleSpec
open scoped ENNReal
open LeanVM LeanVM.Node LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile
open Common.SufCma

namespace LeanVM.Guest.Compose

/-! ## leanXMSS -/

/-- **The raw leanXMSS signatures a witness holds directly**: each with its key, as a forgery of
the SUF-CMA game (the message it signs and the signature). -/
def xmssRaws (w : NodeWitness) : List (HashSig.PublicKey × LeanXmss.Forgery) :=
  w.xmssSignatures.map fun raw ↦ (raw.1.1, ⟨raw.1.2, raw.2⟩)

/-- **leanXMSS's deployed verification**: `verifyWithKeccak`, over the deployed Keccak-f[1600],
as `SignatureClaimsHeld` checks a raw signature. -/
def xmssDeployedVerify (pk : HashSig.PublicKey) (f : LeanXmss.Forgery) : Bool :=
  LeanXmss.verifyWithKeccak pk f.message f.signature

/-- Every raw leanXMSS signature of a witness holding a statement is accepted by the deployed
verification. -/
theorem xmssRaws_verify : ∀ bytecode seed s w, NodeRelation bytecode seed s w →
    ∀ r ∈ xmssRaws w, xmssDeployedVerify r.1 r.2 = true := by
  intro bytecode seed s w h r hr
  unfold NodeRelation SignatureClaimsHeld at h
  obtain ⟨raw, hraw, rfl⟩ := List.mem_map.1 hr
  exact h.1.1 raw hraw

/-- **Raw leanXMSS signatures the aggregation accepts are genuine, conditionally.** For any `k`,
`Q`, `q_h`, `δ` and adversary: the verifier accepts a proof of the guest program on the digest of a
statement whose deferred claim holds, and the extracted execution's decoding does not explain the
statement, or explains it with a witness holding directly a raw leanXMSS signature, under one of
`k ≤ 2^32` honest keys, that wins against that key's transcript (a fresh signature its honest signer
never returned), with probability at most the knowledge-soundness bound plus `δ` plus
`k · (q_h + 2^10 + k) · 2^-127`, for an adversary making at most `Q ≤ 2^128` calls of `π`, `q_h` of
`π_h` and `lifetime` requests to each key.

Stated without `AggregateSound`, which
`aggregate_raw_xmss_signatures_genuine_if_keccak_like_ideal_of_aggregateSound` assumes; it is
conditional on the named hypothesis `KeccakVerificationLikeIdeal`, about this adversary only: the
probability that the decoded witness holds a fresh raw signature under an honest key that the
deployed verification (`verifyWithKeccak`) accepts and the verification over `π_h` rejects is at
most `δ`. The model has two independent random permutations, the proof system's `π` and the scheme's
`π_h`, while deployed both are Keccak-f[1600]. It is about soundness only: an honest signature over
`π_h` generally fails `verifyWithKeccak`, so nothing here says an honest aggregate is accepted. It
speaks of the raw signatures the node holds directly only, not of the claims it holds through its
children. -/
def AggregateRawXmssSignaturesGenuineIfKeccakLikeIdeal (P D : Cost.MachineProgram) : Prop :=
  ∀ {k : ℕ}, 1 ≤ k → k ≤ 2 ^ 32 →
    ∀ (A : Common.Compose.ComposedAdversary k HashSig.PublicKey LeanXmss.SigningRequest
        (Option LeanXmss.Signature)) (Q qh : ℕ),
    (∀ pks, Common.QueryCostAtMost (A pks) Common.Compose.piCost Q) → Q ≤ 2 ^ 128 →
    (∀ pks, Common.QueryCostAtMost (A pks) Common.Compose.piHCost qh) →
    (∀ pks j, Common.QueryCostAtMost (A pks) (Common.Compose.requestToKey j)
        LeanXmss.lifetime) →
    ∀ {δ : ℝ≥0∞}, Common.Compose.KeccakVerificationLikeIdeal
        LeanXmss.RandomPermutationModel.sufCmaScheme k guestProgram D (extractorComputedBy P)
        xmssRaws xmssDeployedVerify A δ →
    Pr{let z ← Common.Compose.composedExperiment LeanXmss.RandomPermutationModel.sufCmaScheme k
        guestProgram D (extractorComputedBy P) xmssRaws xmssDeployedVerify A}[
      ∃ statement : NodeStatement,
        z.1.accepted ∧ z.1.program = guestProgram ∧
        publicInputDigest z.1.input = statementDigest (deployedSeed guestProgram) statement ∧
        statement.deferredClaim.HoldsWithShape (bytecodeWords guestProgram) ∧
        ((¬ ∃ execution, ∃ decoding : SeedStatementAndWitness,
            extractorComputedBy P z.1.program z.1.input z.1.transcript z.1.proof =
              some execution ∧
            Cost.outputWithin D guestWitnessDecoderSizeBound
              (guestWitnessDecoderBudget execution)
              (Cost.encodeGuestWitnessDecoderInput z.1.program execution) =
                some (Cost.encodeValue decoding) ∧
            ExplainsStatement guestProgram statement decoding) ∨
          ∃ execution, ∃ decoding : SeedStatementAndWitness,
            extractorComputedBy P z.1.program z.1.input z.1.transcript z.1.proof =
              some execution ∧
            Cost.outputWithin D guestWitnessDecoderSizeBound
              (guestWitnessDecoderBudget execution)
              (Cost.encodeGuestWitnessDecoderInput z.1.program execution) =
                some (Cost.encodeValue decoding) ∧
            decoding.seed = deployedSeed guestProgram ∧ decoding.statement = statement ∧
            NodeRelation (bytecodeWords guestProgram) (deployedSeed guestProgram) statement
              decoding.witness ∧
            ∃ r ∈ xmssRaws decoding.witness, ∃ j, r.1 = z.2.1 j ∧
              LeanXmss.RandomPermutationModel.sufCmaScheme.winningCondition
                (keyLog j z.2.2.1) r.2 = true)] ≤
      ((Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
          5 * (Q + 2 ^ 14 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256) + δ +
        (k : ℝ≥0∞) * ((qh : ℝ≥0∞) + 2 ^ 10 + k) * (2 : ℝ≥0∞)⁻¹ ^ 127

/-- **`AggregateRawXmssSignaturesGenuineIfKeccakLikeIdeal` from `AggregateSound`**: for the
guest, the decoder `D` and `extractorComputedBy P`. Conditional also on the hypothesis
`KeccakVerificationLikeIdeal` the proposition carries. -/
theorem aggregate_raw_xmss_signatures_genuine_if_keccak_like_ideal_of_aggregateSound
    {P D : Cost.MachineProgram}
    (hagg : AggregateSound guestProgram D (extractorComputedBy P)) :
    AggregateRawXmssSignaturesGenuineIfKeccakLikeIdeal P D := by
  intro k hk1 hk A Q qh hQ hQ' hqh hn δ hδ
  have : Inhabited LeanXmss.Forgery :=
    ⟨⟨0, ⟨⟨0, Nat.two_pow_pos _⟩, fun _ ↦ ⟨0, fun _ ↦ 0, fun _ ↦ 0⟩⟩⟩⟩
  have h := Common.Compose.composed_sound LeanXmss.RandomPermutationModel.sufCmaScheme k
    guestProgram D (extractorComputedBy P) xmssRaws xmssDeployedVerify hagg
    XmssSecurity.leanXmss_multiKey hk1 hk A Q qh hQ hQ' hqh hn
    (Common.Compose.extractorComputedBy_readsPermutationQueries P) xmssRaws_verify hδ
  rwa [show ((LeanXmss.RandomPermutationModel.securitySlack : ℕ) : ℝ≥0∞) = 2 ^ 10 by
    norm_num [LeanXmss.RandomPermutationModel.securitySlack]] at h

/-! ## leanSPHINCS -/

/-- **The raw leanSPHINCS signatures a witness holds directly**: each with its key, as a forgery of
the SUF-CMA game (the message it signs and the signature). -/
def sphincsRaws (w : NodeWitness) : List (Sphincs.PublicKey × Sphincs.Forgery) :=
  w.sphincsSignatures.map fun raw ↦ (raw.1.1, ⟨raw.1.2, raw.2⟩)

/-- **leanSPHINCS's deployed verification**: `verifyWithKeccak`, over the deployed Keccak-f[1600],
as `SignatureClaimsHeld` checks a raw signature. -/
def sphincsDeployedVerify (pk : Sphincs.PublicKey) (f : Sphincs.Forgery) : Bool :=
  Sphincs.verifyWithKeccak pk f.message f.signature

/-- Every raw leanSPHINCS signature of a witness holding a statement is accepted by the deployed
verification. -/
theorem sphincsRaws_verify : ∀ bytecode seed s w, NodeRelation bytecode seed s w →
    ∀ r ∈ sphincsRaws w, sphincsDeployedVerify r.1 r.2 = true := by
  intro bytecode seed s w h r hr
  unfold NodeRelation SignatureClaimsHeld at h
  obtain ⟨raw, hraw, rfl⟩ := List.mem_map.1 hr
  exact h.1.2.1 raw hraw

/-- **Raw leanSPHINCS signatures the aggregation accepts are genuine, conditionally.** For any `k`,
`Q`, `q_h`, `δ` and adversary: the verifier accepts a proof of the guest program on the digest of a
statement whose deferred claim holds, and the extracted execution's decoding does not explain the
statement, or explains it with a witness holding directly a raw leanSPHINCS signature, under one of
`k ≤ 2^32` honest keys, that wins against that key's transcript (a fresh signature its honest signer
never returned), with probability at most the knowledge-soundness bound plus `δ` plus
`k · (q_h + 2^19 + k) · 2^-127`, for an adversary making at most `Q ≤ 2^128` calls of `π`, `q_h` of
`π_h` and `signatureLimit` requests to each key.

Stated without `AggregateSound`, which
`aggregate_raw_sphincs_signatures_genuine_if_keccak_like_ideal_of_aggregateSound` assumes; it is
conditional on the named hypothesis `KeccakVerificationLikeIdeal`, about this adversary only: the
probability that the decoded witness holds a fresh raw signature under an honest key that the
deployed verification (`verifyWithKeccak`) accepts and the verification over `π_h` rejects is at
most `δ`. The model has two independent random permutations, the proof system's `π` and the scheme's
`π_h`, while deployed both are Keccak-f[1600]. It is about soundness only: an honest signature over
`π_h` generally fails `verifyWithKeccak`, so nothing here says an honest aggregate is accepted. It
speaks of the raw signatures the node holds directly only, not of the claims it holds through its
children. -/
def AggregateRawSphincsSignaturesGenuineIfKeccakLikeIdeal (P D : Cost.MachineProgram) : Prop :=
  ∀ {k : ℕ}, 1 ≤ k → k ≤ 2 ^ 32 →
    ∀ (A : Common.Compose.ComposedAdversary k Sphincs.PublicKey HashSig.Message
        (Option Sphincs.Signature)) (Q qh : ℕ),
    (∀ pks, Common.QueryCostAtMost (A pks) Common.Compose.piCost Q) → Q ≤ 2 ^ 128 →
    (∀ pks, Common.QueryCostAtMost (A pks) Common.Compose.piHCost qh) →
    (∀ pks j, Common.QueryCostAtMost (A pks) (Common.Compose.requestToKey j)
        Sphincs.signatureLimit) →
    ∀ {δ : ℝ≥0∞}, Common.Compose.KeccakVerificationLikeIdeal
        Sphincs.RandomPermutationModel.sufCmaScheme k guestProgram D (extractorComputedBy P)
        sphincsRaws sphincsDeployedVerify A δ →
    Pr{let z ← Common.Compose.composedExperiment Sphincs.RandomPermutationModel.sufCmaScheme k
        guestProgram D (extractorComputedBy P) sphincsRaws sphincsDeployedVerify A}[
      ∃ statement : NodeStatement,
        z.1.accepted ∧ z.1.program = guestProgram ∧
        publicInputDigest z.1.input = statementDigest (deployedSeed guestProgram) statement ∧
        statement.deferredClaim.HoldsWithShape (bytecodeWords guestProgram) ∧
        ((¬ ∃ execution, ∃ decoding : SeedStatementAndWitness,
            extractorComputedBy P z.1.program z.1.input z.1.transcript z.1.proof =
              some execution ∧
            Cost.outputWithin D guestWitnessDecoderSizeBound
              (guestWitnessDecoderBudget execution)
              (Cost.encodeGuestWitnessDecoderInput z.1.program execution) =
                some (Cost.encodeValue decoding) ∧
            ExplainsStatement guestProgram statement decoding) ∨
          ∃ execution, ∃ decoding : SeedStatementAndWitness,
            extractorComputedBy P z.1.program z.1.input z.1.transcript z.1.proof =
              some execution ∧
            Cost.outputWithin D guestWitnessDecoderSizeBound
              (guestWitnessDecoderBudget execution)
              (Cost.encodeGuestWitnessDecoderInput z.1.program execution) =
                some (Cost.encodeValue decoding) ∧
            decoding.seed = deployedSeed guestProgram ∧ decoding.statement = statement ∧
            NodeRelation (bytecodeWords guestProgram) (deployedSeed guestProgram) statement
              decoding.witness ∧
            ∃ r ∈ sphincsRaws decoding.witness, ∃ j, r.1 = z.2.1 j ∧
              Sphincs.RandomPermutationModel.sufCmaScheme.winningCondition
                (keyLog j z.2.2.1) r.2 = true)] ≤
      ((Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
          5 * (Q + 2 ^ 14 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256) + δ +
        (k : ℝ≥0∞) * ((qh : ℝ≥0∞) + 2 ^ 19 + k) * (2 : ℝ≥0∞)⁻¹ ^ 127

/-- **`AggregateRawSphincsSignaturesGenuineIfKeccakLikeIdeal` from `AggregateSound`**: for the
guest, the decoder `D` and `extractorComputedBy P`. Conditional also on the hypothesis
`KeccakVerificationLikeIdeal` the proposition carries. -/
theorem aggregate_raw_sphincs_signatures_genuine_if_keccak_like_ideal_of_aggregateSound
    {P D : Cost.MachineProgram}
    (hagg : AggregateSound guestProgram D (extractorComputedBy P)) :
    AggregateRawSphincsSignaturesGenuineIfKeccakLikeIdeal P D := by
  intro k hk1 hk A Q qh hQ hQ' hqh hn δ hδ
  have : Inhabited Sphincs.Forgery :=
    ⟨⟨0, ⟨0, fun _ ↦ ⟨0, fun _ ↦ 0⟩, fun _ ↦ ⟨0, fun _ ↦ 0, fun _ ↦ 0⟩⟩⟩⟩
  have h := Common.Compose.composed_sound Sphincs.RandomPermutationModel.sufCmaScheme k
    guestProgram D (extractorComputedBy P) sphincsRaws sphincsDeployedVerify hagg
    Sphincs.leanSphincs_multiKey hk1 hk A Q qh hQ hQ' hqh hn
    (Common.Compose.extractorComputedBy_readsPermutationQueries P) sphincsRaws_verify hδ
  rwa [show ((Sphincs.securitySlack : ℕ) : ℝ≥0∞) = 2 ^ 19 by
    norm_num [Sphincs.securitySlack]] at h

end LeanVM.Guest.Compose

/--
info: 'LeanVM.Guest.Compose.aggregate_raw_xmss_signatures_genuine_if_keccak_like_ideal_of_aggregateSound'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  LeanVM.Guest.Compose.aggregate_raw_xmss_signatures_genuine_if_keccak_like_ideal_of_aggregateSound

/--
info: 'LeanVM.Guest.Compose.aggregate_raw_sphincs_signatures_genuine_if_keccak_like_ideal_of_aggregateSound'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  LeanVM.Guest.Compose.aggregate_raw_sphincs_signatures_genuine_if_keccak_like_ideal_of_aggregateSound
