/-
  LeanVM.Guest.EndRpm

  The aggregation guest's theorems that involve an adversary, in the random-permutation model:
  `MemoryAggregateSound` (`AggregateSound` of `Statement/Corollaries.lean` for a decoder of
  memories) for the deployed bytecode and the decoder
  `decode`, and the guest's completeness composed with the protocol's.
-/

import LeanVM.Guest.EndFinal
import LeanVM.Guest.Complete
import LeanVM.Protocol.LeanVMRpm
import Statement.LeanVmGuest
import Statement.Corollaries
import Common.Transfer
import LeanXmss.Scheme
import Statement.LeanSphincs
import Statement.Fast.Schemes
import LeanDa.Scheme
import Statement.Fast.Keccak
import Statement.Fast.QuadExt
import Statement.Fast.FieldWords
import LeanVM.Facts.Verifier
import LeanVM.Protocol.WithHash
import LeanVM.Guest.AcceptableChild

/-!
# The guest in the random-permutation model

The guest's own theorems involve no oracle: `guest_knowledge` (every valid execution decodes),
`decode_binds` and `guest_complete` are about executions and the deployed Keccak. Here they are
composed with the protocol's theorems in the random-permutation model (`Statement/LeanVm.lean`,
`LeanVM/Protocol/LeanVMRpm.lean`):

* `aggregate_knowledge`: in the random-permutation experiment, the verifier accepts a proof of the
  guest from which no execution is extracted (`transcriptExtractor`, on the adversary's transcript), or
  the extracted one does not decode (`ExplainsPublicInput`), with probability at most
  `(Q + 2^14) · 2^-125 + 5 (Q + 2^14)² · 2^-256` for `Q ≤ 2^128`: `KnowledgeSoundness`
  (`knowledgeSoundness_holds`) and `guest_knowledge`.
* `aggregate_sound_outer : MemoryAggregateSound guest decode`: with `decode_binds`, an accepted
  aggregate's statement `s`, under the deployed seed and of the guest's shape, is the one the extracted execution decodes, with a witness holding it, or that
  execution's decoding and `s` give an explicit Keccak-256 collision, except with the same
  probability.
* `aggregate_complete_of`: a node within the budget has an execution of the guest whose honest
  proof the verifier rejects, in the random-permutation model, with probability at most
  `completenessError fuel + rpmError (completenessPermCalls fuel)` (`Rpm.completenessRpm`).
-/

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open scoped ENNReal

open OracleComp OracleSpec in
/-- **The outer verifier's acceptance explained, for a decoder of memories**: `AggregateSound`
(`Statement/Corollaries.lean`) with the decoding of the extracted execution read off its memory by
`decode` instead of output by a decoder program; `LeanVM/Guest/DecoderProgram.lean` relates the
two. -/
def MemoryAggregateSound (guest : LeanIsaProgram) (decode : MemoryDecoder)
    (extractor : StraightLineExtractor) : Prop :=
  ∀ (A : RandomPermutationAdversary) (Q : ℕ),
    Common.QueryCostAtMost A Common.permutationCallCost Q → Q ≤ 2 ^ 128 →
    Pr{let z ← knowledgeSoundnessExperiment A}[∃ s : NodeStatement, z.accepted ∧ z.program = guest ∧
      publicInputDigest z.input = statementDigest (deployedSeed guest) s ∧
      s.deferredClaim.HasBytecodeShape (bytecodeWords guest) ∧
      ¬ ∃ t, extractor z.program z.input z.transcript z.proof = some t ∧
        ExplainsStatement guest s (decode t.memory)] ≤
      (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
        5 * (Q + 2 ^ 14 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256

end LeanVM.Node

namespace LeanVM.Guest.End

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Check LeanVM.Node
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Guest.B1 LeanVM.Guest.B1.Digest
open LeanVM.Guest.Binding
open scoped ENNReal

variable {W : Val → Reader → FrameMap → NodeWitness}

/-- **The aggregate's soundness, its witness named**, for any decoder `dec` of which
`MemoryGuestKnowledge` holds: in the random-permutation experiment, the verifier accepts a proof of
the guest from which no execution is extracted, or the extracted one does not decode by `dec`
(`ExplainsPublicInput`), with probability at most the bound of `KnowledgeSoundness`. -/
theorem aggregate_knowledge_dec {dec : MemoryDecoder} (h : MemoryGuestKnowledge guestProgram dec)
    (A : RandomPermutationAdversary) (Q : ℕ)
    (hA : Common.QueryCostAtMost A Common.permutationCallCost Q) (hQ : Q ≤ 2 ^ 128) :
    Pr{let z ← knowledgeSoundnessExperiment A}[z.accepted ∧ z.program = guestProgram ∧
      ¬ ∃ t, transcriptExtractor z.program z.input z.transcript z.proof = some t ∧
        ExplainsPublicInput guestProgram z.input (dec t.memory)] ≤
      (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
        5 * (Q + 2 ^ 14 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 := by
  refine le_trans (prEvent_mono _ _ _ ?_) (knowledgeSoundness_holds A Q hA hQ)
  rintro ⟨prog, input, π, b, T⟩ ⟨hb, hprog, hno⟩
  dsimp only at hprog
  subst hprog
  refine ⟨hb, ?_⟩
  rintro ⟨t, hx, hv⟩
  exact hno ⟨t, hx, h input t hv⟩

/-- **The aggregate's soundness, its witness named**, for `main`'s witness function `W`. -/
theorem aggregate_knowledge_of (h : SoundHyps W) (A : RandomPermutationAdversary) (Q : ℕ)
    (hA : Common.QueryCostAtMost A Common.permutationCallCost Q) (hQ : Q ≤ 2 ^ 128) :
    Pr{let z ← knowledgeSoundnessExperiment A}[z.accepted ∧ z.program = guestProgram ∧
      ¬ ∃ t, transcriptExtractor z.program z.input z.transcript z.proof = some t ∧
        ExplainsPublicInput guestProgram z.input (decodeWith W t.memory)] ≤
      (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
        5 * (Q + 2 ^ 14 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 :=
  aggregate_knowledge_dec (guest_knowledge_of h) A Q hA hQ

/-- **What the outer verifier's acceptance establishes** (`MemoryAggregateSound`), in the
random-permutation model, for any decoder `dec` of which `MemoryGuestKnowledge` holds: except with
probability the bound of `KnowledgeSoundness`, an accepted aggregate's statement `s`, under the
deployed seed and of the guest's shape, is the one the execution the extractor reads off the proof
and the transcript decodes, with a witness holding it, or that execution's decoding and `s` give an
explicit Keccak-256 collision. -/
theorem aggregate_sound_outer_dec {dec : MemoryDecoder} (h : MemoryGuestKnowledge guestProgram dec) :
    MemoryAggregateSound guestProgram dec transcriptExtractor := by
  intro A Q hA hQ
  refine le_trans (prEvent_mono _ _ _ ?_) (aggregate_knowledge_dec h A Q hA hQ)
  rintro z ⟨s, hb, hprog, hpub, hs, hno⟩
  refine ⟨hb, hprog, ?_⟩
  rintro ⟨t, hx, hd, hrel⟩
  refine hno ⟨t, hx, ?_⟩
  rcases decoded_binds hs hrel.hasBytecodeShape hpub hd with ⟨h1, h2⟩ | hc
  · exact Or.inl ⟨h1, h2, h1 ▸ h2 ▸ hrel⟩
  · exact Or.inr hc

/-- **What the outer verifier's acceptance establishes** (`MemoryAggregateSound`), for `main`'s
witness function `W`. -/
theorem aggregate_sound_outer_of (h : SoundHyps W) :
    MemoryAggregateSound guestProgram (decodeWith W) transcriptExtractor :=
  aggregate_sound_outer_dec (guest_knowledge_of h)

/-- **What the outer verifier's acceptance establishes**, from B2 and `verify_sub`'s
statement. -/
theorem aggregate_sound_outer_V {piOf : Reader → Val → FrameMap → Protocol.Compile.Proof} (hb2 : B2SoundL)
    (hv : B1.Main.SubSoundW bytecode piOf) :
    MemoryAggregateSound guestProgram (decodeV piOf) transcriptExtractor :=
  aggregate_sound_outer_of (soundHyps_of_sub hb2 hv)

/-- **What the outer verifier's acceptance establishes**, from `verify_sub`'s statement. -/
theorem aggregate_sound_outer_sub (hP : EndPending)
    {piOf : Reader → Val → FrameMap → Protocol.Compile.Proof}
    (hv : B1.Main.SubSoundW bytecode piOf) :
    MemoryAggregateSound guestProgram (decodeV piOf) transcriptExtractor :=
  aggregate_sound_outer_V (b2SoundL hP) hv

/-- **The aggregate's soundness, its witness named**, for the deployed guest and its decoder: in
the random-permutation experiment, the verifier accepts a proof of the guest from which no
execution is extracted, or the extracted one does not decode (`ExplainsPublicInput`), with probability at
most `(Q + 2^14) · 2^-125 + 5 (Q + 2^14)² · 2^-256`, for `Q ≤ 2^128`. -/
theorem aggregate_knowledge (hP : EndPending) (A : RandomPermutationAdversary) (Q : ℕ)
    (hA : Common.QueryCostAtMost A Common.permutationCallCost Q) (hQ : Q ≤ 2 ^ 128) :
    Pr{let z ← knowledgeSoundnessExperiment A}[z.accepted ∧ z.program = guestProgram ∧
      ¬ ∃ t, transcriptExtractor z.program z.input z.transcript z.proof = some t ∧
        ExplainsPublicInput guestProgram z.input (decode t.memory)] ≤
      (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
        5 * (Q + 2 ^ 14 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 :=
  aggregate_knowledge_dec (guest_knowledge hP) A Q hA hQ

/-- **What the outer verifier's acceptance establishes** (`MemoryAggregateSound`), for the deployed
guest and its decoder, in the random-permutation model: except with probability
`(Q + 2^14) · 2^-125 + 5 (Q + 2^14)² · 2^-256` (for `Q ≤ 2^128`), an accepted aggregate's statement `s`, under
the deployed seed and of the guest's shape, is the one the execution the
extractor reads off the proof and the adversary's transcript (one is extracted) decodes, with a
witness holding it, or that execution's decoding and `s` give an explicit Keccak-256 collision;
given the guest's pending obligations (`EndPending`). -/
theorem aggregate_sound_outer (hP : EndPending) :
    MemoryAggregateSound guestProgram decode transcriptExtractor :=
  aggregate_sound_outer_dec (guest_knowledge hP)

/-- **The guest's completeness in the random-permutation model**: under the hypotheses, there is
an execution of the guest on the statement's digest whose honest proof, at an inverse rate `2^ρ`,
`1 ≤ ρ ≤ 4`, and a fuel of at most `2^64` nonces, the verifier rejects with probability at most
`completenessError fuel + rpmError (completenessPermCalls fuel)` (`Rpm.completenessRpm`). -/
theorem aggregate_complete_of {budget : NodeStatement → NodeWitness → ℕ}
    (h : GuestComplete budget) {seed : Digest} {s : NodeStatement} {w : NodeWitness}
    (hrel : NodeRelation bytecode seed s w) (hlim : DeployedLimits s w)
    (hok : ChildrenOk bytecode seed w) (hbudget : budget s w ≤ 2 ^ 28) :
    ∃ t : Execution guestProgram, ValidExecution guestProgram (publicInputOf (statementDigest seed s)) t ∧
      ∀ ρ fuel, 1 ≤ ρ ∧ ρ ≤ 4 → fuel ≤ 2 ^ 64 →
        Pr{let v ← verifierCompletenessExperimentWithHash
            (fun prog input t ρ fuel ↦
              some <$> LeanVM.Protocol.EndToEnd.Complete.honestComp prog input t ρ fuel)
            guestProgram (publicInputOf (statementDigest seed s)) t ρ fuel}[v = false] ≤
          completenessError fuel + rpmError (completenessPermCalls fuel) := by
  obtain ⟨t, hv, -, hsize⟩ := h seed s w hrel hlim hok hbudget
  exact ⟨t, hv, fun _ _ hρ hfuel ↦ Rpm.completenessRpm hv (by omega) hρ hfuel⟩

end LeanVM.Guest.End
