import LeanVM.Protocol.LeanVM
import LeanVM.Protocol.LeanVMRpm
import LeanVM.Guest.Batch.Children
import LeanVM.Guest.Batch.Rpm
import LeanVM.Guest.EndRpm
import LeanVM.Guest.Budget.ClosedN
import LeanVM.Guest.Budget.Covered
import LeanVM.Prover.End
import LeanVM.Prover.EndChild
import LeanVM.Guest.Child.Covered
import LeanVM.Guest.HonestChildren
import XmssSecurity.Rpm
import Sphincs.Security
import LeanDa
import Statement.Theorems
import Statement.Corollaries
import LeanVM.Protocol.WithHash
import LeanVM.Guest.WithHash
import LeanVM.Cost.Efficient
import LeanVM.Guest.DecoderProgram
import LeanVM.Cost.DecoderSpec
import LeanVM.Cost.Bounds.Guest.Budget
import LeanVM.Cost.GuestDecoding
import LeanVM.Wire.OneEncoding
import LeanVM.Wire.Honest

/-! # The end theorems of leanVM

`LeanVM.theorems_hold` (at the end) proves `Statement.Theorems` (`Statement/Theorems.lean`): every
end statement of the repository, leanXMSS's, leanSPHINCS's and LeanDA's included, in one theorem.
`LeanVM.corollaries_of_theorems` proves `Statement.Corollaries` (`Statement/Corollaries.lean`) from
the fields of `Statement.Theorems` alone, and `LeanVM.corollaries_hold` for the compiled extractor
and decoder programs (`LeanVM.Cost.compiledKnowledgeExtractor`,
`LeanVM.Cost.compiledGuestWitnessDecoder`).

**The guest decoder.** `Statement.Theorems` takes the guest program's decoder as a cost-machine
program too (`GuestKnowledgeSoundness`, `Statement/LeanVmGuest.lean`):
`LeanVM.Cost.compiledGuestWitnessDecoder`, the
proofs' decoder `LeanVM.Guest.End.decode` compiled (`LeanVM/Cost/Decoder/`, its top `decTopC`),
within `guestWitnessDecoderSizeBound` (`Cost/DecoderSize.lean`) and computing `decode` on every valid
execution (`Cost/DecoderSpec.lean`: `decoderProgram_spec`) within its budget, its price within
`guestDecoderPrice` (`LeanVM.Cost.Bounds.Guest.decoderPriceWithinBudget :
DecoderPriceWithinBudget`, `Cost/Bounds/Guest/Budget.lean`). `theorems_hold` and
`corollaries_hold` take no hypothesis (the `example` after `theorems_hold` pins the statement).
Its fields are proved by `theorems_of_decoderSpec`, for any decoder program meeting
`DecoderProgramSpec` for a decoder whose decodings explain the input (`DecoderExplains`,
`LeanVM/Guest/DecoderProgram.lean`); `theorems_hold_of_decode` takes that decoder to be `decode`,
whose decodings explain the input by `guest_knowledge`.

**The extractor.** `Statement.Theorems` takes the extractor as a cost-machine program
(`Statement/CostMachine.lean`): `compiledKnowledgeExtractor`, the knowledge extractor
`transcriptExtractor` (`LeanVM/Protocol/Extraction/Extractor.lean`) compiled
(`Cost/Extractor/Top.lean`) behind an entry (`Cost/ExtractorProgram.lean`). Its size is within
`leanVmKnowledgeExtractorSizeBound` (`Cost/ExtractorSize.lean`), and the extractor it computes
within its budget is
`transcriptExtractor` (`LeanVM.Cost.extractorOf_extractorProgram`), for which
`knowledgeSoundness_holds` is proved; its price is within `leanVmKnowledgeExtractorBudget`
(`Cost/Bounds/Top.lean`).

Each theorem below proves a proposition of `Statement/` (`statement.tex`), in the
random-permutation model where an adversary is involved, except the memory-decoder forms
`MemoryGuestKnowledge` and `MemoryAggregateSound`, which are `lean_vm`'s own definitions
(`Guest/EndKnow.lean`, `Guest/EndRpm.lean`), steps to `Statement`'s `GuestKnowledgeSoundness` and
`AggregateSound`; the final `example`, after `theorems_hold`, checks the end theorem against
`Statement.Theorems` itself:

* `LeanVM.knowledgeSoundness_holds : KnowledgeSoundness transcriptExtractor` and
  `LeanVM.completeness_holds : Completeness` (`Statement/LeanVm.lean`): the verifier, knowledge
  sound for the straight-line extractor `transcriptExtractor`, and complete;
* `LeanVM.Guest.End.guest_knowledge : MemoryGuestKnowledge guestProgram decode` (`lean_vm`'s
  definition) and `LeanVM.Guest.Binding.digest_binds : StatementDigestBinds`
  (`Statement/LeanVmGuest.lean`;
  with `knowledgeSoundness_holds` they compose to `LeanVM.Guest.End.aggregate_sound_outer :
  MemoryAggregateSound guestProgram decode transcriptExtractor`): the leanISA guest program, its
  witness named by the decoder of memories `LeanVM.Guest.End.decode`
  (`LeanVM/Guest/EndFinal.lean`); `GuestKnowledgeSoundness D` of
  `Statement/LeanVmGuest.lean` follows
  for a decoder program `D` that computes it within its size bound and budget
  (`LeanVM.Guest.End.guestKnowledge_of_decode`), the compiled
  `LeanVM.Cost.compiledGuestWitnessDecoder`;
* `LeanVM.Guest.Completeness.guest_complete_on_honest_children : GuestCompleteOnHonestChildren`
  (`Statement/LeanVmGuestCompleteness.lean`): the guest program's completeness on the covered nodes whose children carry honest
  proofs, from `LeanVM.Guest.Budget.guest_complete_covered` (children the guest accepts,
  `AcceptableChild`, `LeanVM/Guest/AcceptableChild.lean`), `guest_child_complete` (an honest proof
  is such a child) and `LeanVM.Guest.Child.freshClaim_unique`;
* `LeanVM.Guest.Completeness.honest_proof_rarely_refused : HonestProofRarelyRefused`
  (`Statement/LeanVmGuestCompleteness.lean`): the honest proof of a guest execution is rejected
  with probability at most `2^-126` in the random-permutation model;
* `LeanVM.Guest.Batch.batch_sound_holds : BatchingSound` (`Statement/LeanVmGuestCompleteness.lean`): the
  recursion step, the batching of the children's deferred claims run outside the circuit, sound in
  the random-permutation model (from `batch_rpm`).

The other theorems pinned below are steps or corollaries: the bounds' numbers (the soundness and
completeness errors, and the compiled extractor's price, `LeanVM.Cost.Bounds.extractorC_cost`,
`extractorPrice_28_4`, `extractorPrice_28_4_2_128`), the guest's batching
of its children's deferred claims (`LeanVM.Guest.Batch.children_sound`, and in the
random-permutation model `batch_rpm`, `batch_rpm_bits`), `decode_binds`, `guest_sound`,
`aggregate_knowledge`, and the guest's completeness within its deployed budget
(`LeanVM.Guest.Budget.guest_complete`, `guest_complete_numeric`).
The two-oracle random-oracle model the proofs pass through (`LeanVM/Protocol/Rom/Statement.lean`:
`LeanVM.knowledgeSoundnessRom_holds`, `LeanVM.completenessRom_holds`; the batching's
`LeanVM.Guest.Batch.batch_rom`, `batch_rom_bits`) is a proof step: its theorems are not pinned here
(`tests/LeanVMTests/Protocol/` and `tests/LeanVMTests/Guest/Batch.lean` check their footprints).
The build fails if their axiom footprint ever grows beyond Lean's three standard axioms. -/

example : LeanVM.KnowledgeSoundness LeanVM.transcriptExtractor := LeanVM.knowledgeSoundness_holds
example : LeanVM.Completeness := LeanVM.completeness_holds
example : LeanVM.Node.MemoryGuestKnowledge LeanVM.Guest.guestProgram LeanVM.Guest.End.decode :=
  LeanVM.Guest.End.guest_knowledge
example : LeanVM.Node.StatementDigestBinds := LeanVM.Guest.Binding.digest_binds
example : LeanVM.Node.MemoryAggregateSound LeanVM.Guest.guestProgram LeanVM.Guest.End.decode
    LeanVM.transcriptExtractor :=
  LeanVM.Guest.End.aggregate_sound_outer
example : LeanVM.Guest.Completeness.GuestCompleteOnHonestChildren :=
  LeanVM.Guest.Completeness.guest_complete_on_honest_children
example : LeanVM.Guest.Completeness.HonestProofRarelyRefused :=
  LeanVM.Guest.Completeness.honest_proof_rarely_refused
example : LeanVM.Guest.Completeness.GuestCompleteCovered := LeanVM.Guest.Budget.guest_complete_covered
example : LeanVM.Guest.Completeness.GuestChildComplete := LeanVM.Guest.Budget.guest_child_complete
example : LeanVM.Guest.Batch.BatchingSound := LeanVM.Guest.Batch.batch_sound_holds

/-- info: 'LeanVM.knowledgeSoundness_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.knowledgeSoundness_holds

/-- info: 'LeanVM.Cost.Bounds.extractorC_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Cost.Bounds.extractorC_cost

/-- info: 'LeanVM.Cost.Bounds.extractorPrice_28_4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Cost.Bounds.extractorPrice_28_4

/-- info: 'LeanVM.Cost.Bounds.extractorPrice_28_4_2_128' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Cost.Bounds.extractorPrice_28_4_2_128

/-- info: 'LeanVM.candidates_ncard_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.candidates_ncard_le

/-- info: 'LeanVM.soundnessError_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.soundnessError_le

/-- info: 'LeanVM.soundnessRpm_le_statement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.soundnessRpm_le_statement

/-- info: 'LeanVM.completenessError_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.completenessError_le

/-- info: 'LeanVM.completeness_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.completeness_holds

/-- info: 'LeanVM.soundnessRpm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.soundnessRpm_le

/-- info: 'LeanVM.soundnessRpm_le_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.soundnessRpm_le_bits

/-- info: 'LeanVM.Rpm.completenessRpm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Rpm.completenessRpm_le

/-- info: 'LeanVM.keccak256_eq_rpm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.keccak256_eq_rpm

/-- info: 'LeanVM.Guest.Batch.children_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Batch.children_sound

/-- info: 'LeanVM.Guest.Batch.batch_rpm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Batch.batch_rpm

/-- info: 'LeanVM.Guest.Batch.batch_rpm_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Batch.batch_rpm_bits

/-- info: 'LeanVM.Guest.Batch.batch_sound_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Batch.batch_sound_holds

/-- info: 'LeanVM.Guest.End.guest_knowledge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.guest_knowledge

/-- info: 'LeanVM.Guest.End.decode_binds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.decode_binds

/-- info: 'LeanVM.Guest.Binding.digest_binds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Binding.digest_binds

/-- info: 'LeanVM.Guest.End.aggregate_sound_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.aggregate_sound_outer

/-- info: 'LeanVM.Guest.End.aggregate_knowledge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.aggregate_knowledge

/-- info: 'LeanVM.Guest.End.aggregate_complete_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.aggregate_complete_of

/-- info: 'LeanVM.Guest.End.guest_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.End.guest_sound

/-- info: 'LeanVM.Guest.Budget.guest_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.guest_complete

/-- info: 'LeanVM.Guest.Budget.guestComplete_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.guestComplete_mono

/-- info: 'LeanVM.Guest.Budget.guest_complete_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.guest_complete_numeric

/-- info: 'LeanVM.Guest.Completeness.guest_complete_on_honest_children' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Completeness.guest_complete_on_honest_children

/-- info: 'LeanVM.Guest.Completeness.honest_proof_rarely_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Completeness.honest_proof_rarely_refused

/-- info: 'LeanVM.Guest.Child.freshClaim_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Child.freshClaim_unique

/-- info: 'LeanVM.Guest.Budget.guest_complete_covered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.guest_complete_covered

/-- info: 'LeanVM.Guest.Budget.guest_child_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.guest_child_complete

/-! ## The proof on the wire

The end theorems are about structured proofs; the wire encoding is a compression layer
(`LeanVM/Wire/Encoding.lean`: `Proof.toBytes`, `Proof.fromBytes`, transcriptions of leanVM's
`crates/fiat_shamir/src/wire.rs`). It is lossless on honest proofs and the only encoding of its
proof:

* `LeanVM.Wire.roundTrip : RoundTripStatement`: a proof whose phases one Merkle tree each opens,
  within the decoding's bounds (`WireDecodable`), decodes from its encoding;
* `LeanVM.Wire.proveWithHash_wireDecodable`: the honest prover's proofs are such proofs, so the
  round trip applies to them (`LeanVM/Wire/Honest.lean`);
* `LeanVM.Wire.oneEncoding : OneEncodingStatement`: bytes that decode to a proof are its encoding.

That `Proof.toBytes` and `Proof.fromBytes` are the Rust's is test evidence (`scripts/wire-diff.py`).
The pruning idea and its formalization on leanerVM's main branch are scaraven's
(https://github.com/scaraven). -/

/-- info: 'LeanVM.Wire.roundTrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Wire.roundTrip

/-- info: 'LeanVM.Wire.proveWithHash_wireDecodable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Wire.proveWithHash_wireDecodable

/-- info: 'LeanVM.Wire.oneEncoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Wire.oneEncoding

/-- **Every end theorem**, `Statement/Theorems.lean`, at the extractor
`LeanVM.Cost.compiledKnowledgeExtractor` and any decoder program `decoderProgram` meeting its
specification
(`LeanVM/Guest/DecoderProgram.lean`). That specification has two parts. First, the program
computes a decoder of executions `decoder` on every valid execution, within its size bound and
budget (`DecoderProgramSpec`). Second, that decoder's decodings explain the public input
(`DecoderExplains`). -/
theorem LeanVM.theorems_of_decoderSpec {decoderProgram : LeanVM.Cost.MachineProgram}
    {decoder : LeanVM.Semantics.Execution LeanVM.Guest.guestProgram →
      LeanVM.Node.SeedStatementAndWitness}
    (hspec : LeanVM.Guest.End.DecoderProgramSpec decoderProgram decoder)
    (hexplains : LeanVM.Guest.End.DecoderExplains decoder) :
    Statement.Theorems (leanVmKnowledgeExtractor := LeanVM.Cost.compiledKnowledgeExtractor)
      (guestWitnessDecoder := decoderProgram) where
  leanVmKnowledgeSoundness := by
    rw [LeanVM.Cost.extractorOf_extractorProgram]
    exact LeanVM.knowledgeSoundness_holds
  leanVmCompleteness := LeanVM.completeness_holds
  guestKnowledgeSoundness := LeanVM.Guest.End.guestKnowledge_of_spec hspec hexplains
  statementDigestBinds := LeanVM.Guest.Binding.digest_binds
  guestCompleteOnHonestChildren := LeanVM.Guest.Completeness.guest_complete_on_honest_children
  honestProofRarelyRefused := LeanVM.Guest.Completeness.honest_proof_rarely_refused
  batchingSound := LeanVM.Guest.Batch.batch_sound_holds
  leanXmssStronglyUnforgeable := XmssSecurity.leanXmss_rpm_security
  leanSphincsStronglyUnforgeable := Sphincs.leanSphincsStronglyUnforgeable
  leanDaComplete := LeanDa.leanDa_perfectlyComplete_rpm
  leanDaPositionBinding := LeanDa.leanDa_positionBinding_rpm
  leanDaCodeBinding := LeanDa.leanDa_codeBinding_rpm_bound

/-- info: 'LeanVM.theorems_of_decoderSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.theorems_of_decoderSpec

/-- **Every end theorem**, for a decoder program that computes `LeanVM.Guest.End.decode` (read off
the memory) within its size bound and budget on every valid execution: that hypothesis alone
(`DecoderProgramSpec`). -/
theorem LeanVM.theorems_hold_of_decode {decoderProgram : LeanVM.Cost.MachineProgram}
    (hspec : LeanVM.Guest.End.DecoderProgramSpec decoderProgram
      fun t ↦ LeanVM.Guest.End.decode t.memory) :
    Statement.Theorems (leanVmKnowledgeExtractor := LeanVM.Cost.compiledKnowledgeExtractor)
      (guestWitnessDecoder := decoderProgram) :=
  LeanVM.theorems_of_decoderSpec hspec LeanVM.Guest.End.decoderExplains_decode

/-- info: 'LeanVM.theorems_hold_of_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.theorems_hold_of_decode

/-- **Every end theorem**, `Statement/Theorems.lean`: the guest's witness named by the compiled
decoder `LeanVM.Cost.compiledGuestWitnessDecoder`, its price within its budget
(`LeanVM.Cost.Bounds.Guest.decoderPriceWithinBudget`), the extractor
`LeanVM.Cost.compiledKnowledgeExtractor`. -/
theorem LeanVM.theorems_hold :
    Statement.Theorems (leanVmKnowledgeExtractor := LeanVM.Cost.compiledKnowledgeExtractor)
      (guestWitnessDecoder := LeanVM.Cost.compiledGuestWitnessDecoder) :=
  LeanVM.theorems_hold_of_decode
    (LeanVM.Cost.decoderProgram_spec LeanVM.Cost.Bounds.Guest.decoderPriceWithinBudget)

/-- info: 'LeanVM.theorems_hold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.theorems_hold

/-- info: 'LeanVM.Cost.Bounds.Guest.decoderPriceWithinBudget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Cost.Bounds.Guest.decoderPriceWithinBudget

/-- info: 'LeanVM.Cost.encodeValue_decoded_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Cost.encodeValue_decoded_injective

/-- The end theorems' statement, pinned: the programs named, no hypothesis. -/
example :
    Statement.Theorems (leanVmKnowledgeExtractor := LeanVM.Cost.compiledKnowledgeExtractor)
      (guestWitnessDecoder := LeanVM.Cost.compiledGuestWitnessDecoder) :=
  LeanVM.theorems_hold

open OracleComp in
/-- **The corollaries follow from the end theorems**, field by field: `aggregateSound` from
`leanVmKnowledgeSoundness`, `guestKnowledgeSoundness` and `statementDigestBinds` (an accepted proof
whose extracted execution decodes, by `guestKnowledgeSoundness`, to a statement of the accepted
digest, which `statementDigestBinds` identifies with the accepted statement or turns into a
collision). -/
theorem LeanVM.corollaries_of_theorems {extractorProgram decoderProgram : LeanVM.Cost.MachineProgram}
    (h : Statement.Theorems (leanVmKnowledgeExtractor := extractorProgram)
      (guestWitnessDecoder := decoderProgram)) :
    Statement.Corollaries (leanVmKnowledgeExtractor := extractorProgram)
      (guestWitnessDecoder := decoderProgram) where
  aggregateSound := by
    intro A Q hA hQ
    refine le_trans (prEvent_mono _ _ _ ?_) (h.leanVmKnowledgeSoundness A Q hA hQ)
    rintro ⟨prog, input, π, b, T⟩ ⟨s, hb, hprog, hpub, hs, hno⟩
    dsimp only at hprog
    subst hprog
    refine ⟨hb, ?_⟩
    rintro ⟨t, hx, hv⟩
    obtain ⟨d, hdec, hd, hrel⟩ := h.guestKnowledgeSoundness input t hv
    refine hno ⟨t, d, hx, hdec, ?_⟩
    rcases h.statementDigestBinds _ _ _ _ _ hrel.hasBytecodeShape hs.1 (hd.trans hpub) with ⟨h1, h2⟩ | hc
    · exact Or.inl ⟨h1, h2, h1 ▸ h2 ▸ hrel⟩
    · exact Or.inr hc

/-- info: 'LeanVM.corollaries_of_theorems' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.corollaries_of_theorems

/-- **Every corollary**, `Statement/Corollaries.lean`, for the compiled extractor and decoder
programs. -/
theorem LeanVM.corollaries_hold :
    Statement.Corollaries (leanVmKnowledgeExtractor := LeanVM.Cost.compiledKnowledgeExtractor)
      (guestWitnessDecoder := LeanVM.Cost.compiledGuestWitnessDecoder) :=
  LeanVM.corollaries_of_theorems LeanVM.theorems_hold

/-- info: 'LeanVM.corollaries_hold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.corollaries_hold
