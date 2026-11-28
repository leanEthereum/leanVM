module

public import Statement.Theorems
public import Statement.Corollaries
public import Statement.LeanVmGuestProver
public import LeanVM.Guest.Binding
public import LeanVM.Wire.RoundTrip
public import LeanVM.Wire.OneEncoding
public import LeanVM.Wire.Honest
public import LeanVM.Prover.ExecuteSound
public import LeanVM.Prover.ExecuteComplete
public import LeanVM.Prover.ExecuteCompleteX
public import LeanVM.Protocol.Hotwire
public import LeanVM.Protocol.Verifier.Defers
public import LeanVM.Facts.Hotwire
public import LeanVM.Guest.Batch.Rpm
public import LeanVM.Guest.Batch.Node
public import LeanVM.Protocol.Compile.SpecRules.Packed
public import LeanVM.Protocol.Verifier.PackedPos
public import LeanVM.Protocol.Verifier.Cost
public import LeanVM.Protocol.Verifier.Grinds
public import LeanVM.Protocol.Extraction.AS.LiteSound
public import LeanVM.Protocol.Relation.Link.GroupLinksEnd
public import LeanVM.Protocol.KnowledgeSoundness
public import LeanVM.Cost.KnowledgeExtractor
public import LeanVM.Protocol.KnowledgeSoundnessCompiled
public import LeanVM.Prover.Complete
public import LeanVM.Cost.GuestKnowledgeHolds
public import LeanVM.Guest.Complete.Holds
public import LeanVM.Protocol.Link
public import LeanVM.Guest.Child.Accepted
public import XmssSecurity.Rpm
public import Sphincs.Security
public import LeanDa.End

public section

/-! # The end theorems of leanVM

`LeanVM.theorems_hold` proves `Statement.Theorems` (`Statement/Theorems.lean`) for the extractor
program `LeanVM.Cost.compiledKnowledgeExtractor` (`LeanVM/Cost/KnowledgeExtractor.lean`, the
agreement-set extractor compiled, within `leanVmKnowledgeExtractorSizeBound` and its budget) and the
decoder program `LeanVM.Cost.compiledGuestWitnessDecoder` (`LeanVM/Cost/DecoderSpec.lean`, the
guest's decoder compiled, within `guestWitnessDecoderSizeBound` and its budget): leanVM's knowledge
soundness (`LeanVM.knowledgeSoundness_compiled`, `LeanVM/Protocol/KnowledgeSoundnessCompiled.lean`)
and completeness (`LeanVM.completeness_holds`, `LeanVM/Prover/Complete.lean`), the guest program's
knowledge soundness (`LeanVM.Cost.guestKnowledgeSoundness_holds`,
`LeanVM/Cost/GuestKnowledgeHolds.lean`) and execution completeness
(`LeanVM.Guest.Complete.guestExecutionComplete_of_routed`, `LeanVM/Guest/Complete/Holds.lean`, at
the generated core route: `CoreMode.offSigs` is `[]`, by `rfl`), the statement digest's binding,
the batching's soundness (`LeanVM.Guest.Batch.batch_sound_holds`, `LeanVM/Guest/Batch/Rpm.lean`),
leanXMSS's and leanSPHINCS's strong unforgeability, and LeanDA's completeness, position binding and
membership soundness. `LeanVM.corollaries_of_theorems` proves `Statement.Corollaries` from the fields
of `Statement.Theorems` and `LeanVM.Node.NodeRelation.hasBytecodeShape`
(`LeanVM/Guest/Batch/Node.lean`), and `LeanVM.corollaries_hold` at the compiled programs; the
guest's aggregate soundness alone is `LeanVM.aggregateSound_holds`.

Besides the end theorems, lemmas: the state link, the shift and window reads, the mirror test and
the lookup link (`LeanVM/Protocol/Hotwire.lean`, which pins their axioms), the soundness of
`verify_link`'s sum-checks in the sample model from the link's arithmetization
(`LeanVM/Protocol/Link.lean`, which pins its axioms), and those pinned below.

The build fails if the axiom footprint of a theorem pinned here ever grows beyond Lean's three
standard axioms. -/

/-- **Every end theorem**, `Statement/Theorems.lean`, at the extractor
`LeanVM.Cost.compiledKnowledgeExtractor` and the decoder `LeanVM.Cost.compiledGuestWitnessDecoder`. -/
theorem LeanVM.theorems_hold :
    Statement.Theorems (leanVmKnowledgeExtractor := LeanVM.Cost.compiledKnowledgeExtractor)
      (guestWitnessDecoder := LeanVM.Cost.compiledGuestWitnessDecoder) where
  leanVmKnowledgeSoundness := LeanVM.knowledgeSoundness_compiled
  leanVmCompleteness := LeanVM.completeness_holds
  guestKnowledgeSoundness := LeanVM.Cost.guestKnowledgeSoundness_holds
  statementDigestBinds := LeanVM.Guest.Binding.digest_binds
  guestExecutionComplete := LeanVM.Guest.Complete.guestExecutionComplete_of_routed rfl
  leanXmssStronglyUnforgeable := XmssSecurity.leanXmss_rpm_security
  leanSphincsStronglyUnforgeable := Sphincs.leanSphincsStronglyUnforgeable
  leanDaComplete := LeanDa.leanDa_complete
  leanDaPositionBinding := LeanDa.leanDa_positionBinding_rpm
  leanDaMembershipSound := LeanDa.leanDa_membershipSound_rpm
  batchingSound := LeanVM.Guest.Batch.batch_sound_holds

/-- info: 'LeanVM.theorems_hold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.theorems_hold

/-- info: 'LeanVM.Guest.Complete.guestExecutionComplete_of_routed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.guestExecutionComplete_of_routed

example : LeanVM.Cost.compiledGuestWitnessDecoder.size ≤ LeanVM.Node.guestWitnessDecoderSizeBound :=
  LeanVM.Cost.decoderProgram_size_le

/-- info: 'LeanVM.Cost.guestKnowledgeSoundness_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Cost.guestKnowledgeSoundness_holds

/-- info: 'LeanVM.Guest.Binding.digest_binds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Binding.digest_binds

/-- info: 'LeanVM.Guest.Batch.batch_sound_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Batch.batch_sound_holds

/-- info: 'LeanVM.Node.NodeRelation.hasBytecodeShape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Node.NodeRelation.hasBytecodeShape

/-! The Fiat-Shamir framework with packed messages: the random-oracle theorem, the packed leaves of
the specification calculus and the compiled verifier's query bound. -/

/-- info: 'LeanVM.Protocol.Compile.Rom.romSound_logG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Compile.Rom.romSound_logG

/-- info: 'LeanVM.Protocol.Compile.Spec.samplePackedCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Compile.Spec.samplePackedCount

/-- info: 'LeanVM.Protocol.Compile.Spec.grindSamplePacked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Compile.Spec.grindSamplePacked

/-- info: 'LeanVM.Protocol.Compile.isTotalQueryBound_verifierComp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Compile.isTotalQueryBound_verifierComp

/-- info: 'LeanVM.Protocol.Compile.rootOk_leanVmVerifierProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Compile.rootOk_leanVmVerifierProgram

/-- info: 'LeanVM.Protocol.Verifier.isTotalQueryBound_leanVm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Verifier.isTotalQueryBound_leanVm

/-- info: 'LeanVM.Protocol.Verifier.leanVmQueryBound_add_three_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Verifier.leanVmQueryBound_add_three_le

/-- info: 'LeanVM.Protocol.Compile.grindBits_le_of_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Compile.grindBits_le_of_reachable

/-- info: 'LeanVM.Extraction.AS.transcriptExtractorL_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Extraction.AS.transcriptExtractorL_of

/-- info: 'LeanVM.Protocol.Relation.linkIface' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.linkIface

/-- info: 'LeanVM.knowledgeSoundnessRomAS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.knowledgeSoundnessRomAS

/-- info: 'LeanVM.knowledgeSoundness_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.knowledgeSoundness_of

open OracleComp OracleSpec LeanVM.Parameters LeanVM.Semantics LeanVM.Node in
/-- **The guest's prover makes the honest prover's proof of its execution**: where `guestExecution`
returns `t`, `guestProve`'s proof is rejected or not made exactly as the honest prover's proof of
`t` (`Completeness`), for any program `guest`. -/
theorem LeanVM.Guest.guestProve_complete {guest : LeanIsaProgram} {s : NodeStatement}
    {w : NodeWitness} {t : Execution guest} (he : guestExecution guest s w = .ok t)
    (hv : ValidExecution guest (PublicInput.ofDigest (statementDigest (deployedSeed guest) s)) t)
    (hsz : t.committedSize ≤ 2 ^ 30)
    (hw : t.pointerWidth ≤ LeanVM.Protocol.Verifier.maxPointerWidth)
    (hk : t.KeccakBlocksInWindows) {ρ : ℕ} (hρ : 1 ≤ ρ ∧ ρ ≤ 4) (hC : LeanVM.Completeness) :
    let input := PublicInput.ofDigest (statementDigest (deployedSeed guest) s)
    Pr{let accepted ← Common.runWithRandomPermutation (do
        match ← guestProve Common.queryPermutation guest s w ρ (2 ^ 35) with
        | none => pure false
        | some proof => leanVmVerifier Common.queryPermutation guest input proof)}[
        accepted = false] ≤ (2 : ENNReal)⁻¹ ^ 256 := by
  have hp : guestProve Common.queryPermutation guest s w ρ (2 ^ 35) =
      LeanVM.Prover.prove Common.queryPermutation guest
        (PublicInput.ofDigest (statementDigest (deployedSeed guest) s)) t ρ (2 ^ 35) := by
    simp only [guestProve, he]
  intro input
  rw [hp]
  exact hC _ _ t ρ hv hsz hw hk hρ

open OracleComp in
/-- **The guest's aggregate soundness follows from the end theorems alone**: from
`leanVmKnowledgeSoundness`, `guestKnowledgeSoundness` and `statementDigestBinds` (an accepted proof
whose extracted execution decodes, by `guestKnowledgeSoundness`, to a statement of the accepted
digest, which `statementDigestBinds` identifies with the accepted statement or turns into a
collision). The decoded statement's shape, which `statementDigestBinds` asks for, is
`NodeRelation.hasBytecodeShape`'s. -/
theorem LeanVM.aggregateSound_of_fields {extractorProgram decoderProgram : LeanVM.Cost.MachineProgram}
    (hks : LeanVM.KnowledgeSoundness (LeanVM.extractorComputedBy extractorProgram))
    (hgks : LeanVM.Node.GuestKnowledgeSoundness decoderProgram)
    (hbind : LeanVM.Node.StatementDigestBinds) :
    LeanVM.Node.AggregateSound LeanVM.Guest.guestProgram decoderProgram
      (LeanVM.extractorComputedBy extractorProgram) := by
  intro A Q hA
  refine le_trans (prEvent_mono _ _ _ ?_) (hks A Q hA)
  rintro ⟨prog, input, π, b, T⟩ ⟨s, hb, hprog, hpub, hs, hno⟩
  dsimp only at hprog
  subst hprog
  refine ⟨hb, ?_⟩
  rintro ⟨t, hx, hv⟩
  obtain ⟨d, hdec, hd, hrel⟩ := hgks input t hv
  refine hno ⟨t, d, hx, hdec, ?_⟩
  rcases hbind _ _ _ _ _ hrel.hasBytecodeShape hs.hasBytecodeShape (hd.trans hpub) with
    ⟨h1, h2⟩ | hc
  · exact Or.inl ⟨h1, h2, h1 ▸ h2 ▸ hrel⟩
  · exact Or.inr hc

open OracleComp in
/-- The same, from `Statement.Theorems`. -/
theorem LeanVM.aggregateSound_of_theorems {extractorProgram decoderProgram : LeanVM.Cost.MachineProgram}
    (h : Statement.Theorems (leanVmKnowledgeExtractor := extractorProgram)
      (guestWitnessDecoder := decoderProgram)) :
    LeanVM.Node.AggregateSound LeanVM.Guest.guestProgram decoderProgram
      (LeanVM.extractorComputedBy extractorProgram) :=
  LeanVM.aggregateSound_of_fields h.leanVmKnowledgeSoundness h.guestKnowledgeSoundness
    h.statementDigestBinds

/-- **The guest's aggregate soundness, proved**: `AggregateSound` at the compiled extractor and
decoder, from the end theorems it reads, which do not include the guest's execution completeness. -/
theorem LeanVM.aggregateSound_holds :
    LeanVM.Node.AggregateSound LeanVM.Guest.guestProgram LeanVM.Cost.compiledGuestWitnessDecoder
      (LeanVM.extractorComputedBy LeanVM.Cost.compiledKnowledgeExtractor) :=
  LeanVM.aggregateSound_of_fields LeanVM.knowledgeSoundness_compiled
    LeanVM.Cost.guestKnowledgeSoundness_holds LeanVM.Guest.Binding.digest_binds

/-- info: 'LeanVM.aggregateSound_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.aggregateSound_holds

/-- **The corollaries follow from the end theorems**, field by field:
`aggregateSound` from the end theorems alone (`LeanVM.aggregateSound_of_theorems`);
`guestProverComplete` from `guestExecutionComplete` and `leanVmCompleteness` (the guest's prover
proves the execution the executor returns with the honest prover). -/
theorem LeanVM.corollaries_of_theorems {extractorProgram decoderProgram : LeanVM.Cost.MachineProgram}
    (h : Statement.Theorems (leanVmKnowledgeExtractor := extractorProgram)
      (guestWitnessDecoder := decoderProgram)) :
    Statement.Corollaries (leanVmKnowledgeExtractor := extractorProgram)
      (guestWitnessDecoder := decoderProgram) where
  aggregateSound := LeanVM.aggregateSound_of_theorems h
  guestProverComplete s w hrel hlim :=
    (h.guestExecutionComplete s w hrel hlim).imp_left fun ⟨_, he, hv, hsz, hw, hk⟩ _ hρ ↦
      LeanVM.Guest.guestProve_complete he hv hsz hw hk hρ h.leanVmCompleteness

/-- info: 'LeanVM.corollaries_of_theorems' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.corollaries_of_theorems

/-- **Every corollary**, `Statement/Corollaries.lean`, at the compiled extractor and decoder. -/
theorem LeanVM.corollaries_hold :
    Statement.Corollaries (leanVmKnowledgeExtractor := LeanVM.Cost.compiledKnowledgeExtractor)
      (guestWitnessDecoder := LeanVM.Cost.compiledGuestWitnessDecoder) :=
  LeanVM.corollaries_of_theorems LeanVM.theorems_hold

/-- info: 'LeanVM.corollaries_hold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.corollaries_hold

/-! ## The proof on the wire

The end statements are about structured proofs; the wire encoding is a compression layer
(`LeanVM/Wire/Encoding.lean`: `Proof.toBytes`, `Proof.fromBytes`, transcriptions of leanVM's
`crates/verifier/src/wire.rs`). It is lossless on the proofs it can decode and the only encoding of
its proof:

* `LeanVM.Wire.roundTrip : RoundTripStatement`: a proof whose phases one Merkle tree each opens,
  within the decoding's bounds (`WireDecodable`), decodes from its encoding;
* `LeanVM.Wire.oneEncoding : OneEncodingStatement`: bytes that decode to a proof are its encoding;
* `LeanVM.Wire.proveWithHash_wireDecodable`: the honest prover's proofs are such proofs, with the
  hash they were proved with (`LeanVM.Wire.prove_wireDecodable` for the statement's prover, with
  Keccak-256 over its permutation): the verifier program opens at most `wireMaxPhases` phases within
  the bounds and reads fewer than `2^32` stream elements, and the honest script commits well-shaped
  words (`LeanVM/Wire/Honest.lean`).

That `Proof.toBytes` and `Proof.fromBytes` are the Rust's is test evidence (`scripts/wire-diff.py`).
The pruning idea and its formalization on leanerVM's main branch are scaraven's
(https://github.com/scaraven). -/

/-- info: 'LeanVM.Wire.roundTrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Wire.roundTrip

/-- info: 'LeanVM.Wire.oneEncoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Wire.oneEncoding

/-- info: 'LeanVM.Wire.proveWithHash_wireDecodable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Wire.proveWithHash_wireDecodable

/-- info: 'LeanVM.Wire.prove_wireDecodable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Wire.prove_wireDecodable

/-! ## The deferring verifier

An aggregate checks a child's proof with the deferring verifier (`verifyDeferred`), which takes the
program's split at the link's point from the child's fresh claim instead of computing it.
`LeanVM.verifyDeferred_of_leanVmVerifier`: a proof the deployed verifier accepts, the deployed
deferring verifier accepts under the IV the verifier hashes with a true fresh claim (the split
columns' values at the link's point), and every fresh claim it accepts it with has that point, so
no other true one. `LeanVM.leanVmVerifier_iff_verifyDeferred`: the deployed verifier accepts
exactly the proofs the deferring verifier accepts with a true fresh claim
(`LeanVM/Protocol/Verifier/Defers.lean`). A false claim at the link's point may pass the link's
terminal check, which is linear in the claim's values: that it does with small probability is a
soundness statement, not this one. -/

/-- info: 'LeanVM.verifyDeferred_of_leanVmVerifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.verifyDeferred_of_leanVmVerifier

/-- info: 'LeanVM.verifyDeferredWith_of_leanVmVerifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.verifyDeferredWith_of_leanVmVerifier

/-- info: 'LeanVM.leanVmVerifier_iff_verifyDeferred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.leanVmVerifier_iff_verifyDeferred

/-! ## The guest's children

What the guest program asks of a child (`AcceptableChild`, `LeanVM/Guest/AcceptableChild.lean`)
follows from the deferring verifier's acceptance, unless the child's openings collide
(`LeanVM/Guest/Child/`), on every bytecode:

* `LeanVM.Guest.Child.stream_le_of_verifyDeferred`: a proof the deferring verifier accepts has a
  stream of at most `leanVmStream = 4792` scalars, within `STREAM_CAP = 8192`;
* `LeanVM.Guest.Child.stackLog_ge_of_announced`: every layout a stream announces has a stack log at
  least `min_execution_stacked_log`;
* `LeanVM.Guest.Child.capsAgree_or_collide`: at every query step of the deferring verifier's run
  the step's openings agree, or the proof's openings exhibit a Keccak-256 collision;
* `LeanVM.Guest.Child.acceptableChildren_or_collide`: the children of a node `NodeRelation` admits
  are children the guest program accepts, or a child's proof exhibits a collision. -/

/-- info: 'LeanVM.Guest.Child.stream_le_of_verifyDeferred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Child.stream_le_of_verifyDeferred

/-- info: 'LeanVM.Guest.Child.stackLog_ge_of_announced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Child.stackLog_ge_of_announced

/-- info: 'LeanVM.Guest.Child.capsAgree_or_collide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Child.capsAgree_or_collide

/-- info: 'LeanVM.Guest.Child.acceptableChildren_or_collide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Child.acceptableChildren_or_collide

/-- info: 'LeanVM.Guest.Child.guestChildren_acceptable_or_collide' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Child.guestChildren_acceptable_or_collide

/-! ## The executor

`LeanVM.Prover.Exec.execute_sound`: an execution the executor `LeanVM.Prover.Exec.execute`
(`Statement/Prover/Execute.lean`) returns is a valid execution of the program on the public input,
whatever the hints and streams (`LeanVM/Prover/ExecuteSound.lean`). -/

/-- info: 'LeanVM.Prover.Exec.execute_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Prover.Exec.execute_sound

/-! `LeanVM.Prover.Exec.execute_complete`: the executor returns an execution of a program's valid
execution's step count, its memory the reference's where written, given an invariant of its states
that satisfies the invariant rule (`LeanVM/Prover/ExecuteComplete.lean`). -/

/-- info: 'LeanVM.Prover.Exec.execute_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Prover.Exec.execute_complete

/-! `LeanVM.Prover.Exec.execute_completeX`: moreover, given an invariant keeping the cells the
executor touches below `2^κ`, that execution is valid, runs the reference's instructions, and
commits no more cells than the reference (`LeanVM/Prover/ExecuteCompleteX.lean`). -/

/-- info: 'LeanVM.Prover.Exec.execute_completeX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Prover.Exec.execute_completeX

/-! `LeanVM.Cost.extractorOf_extractorProgram`: the extractor the compiled cost-machine program
`compiledKnowledgeExtractor` computes, within the statement's size bound and budget, is the lite
agreement-set extractor `transcriptExtractorL` (`LeanVM/Cost/KnowledgeExtractor.lean`). -/

example : LeanVM.Cost.compiledKnowledgeExtractor.size ≤ LeanVM.leanVmKnowledgeExtractorSizeBound :=
  LeanVM.Cost.extractorProgram_size_le

/-- info: 'LeanVM.Cost.extractorOf_extractorProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Cost.extractorOf_extractorProgram

/-- info: 'LeanVM.Cost.extractorProgram_size_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Cost.extractorProgram_size_le

/-- info: 'LeanVM.knowledgeSoundness_compiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.knowledgeSoundness_compiled

end
