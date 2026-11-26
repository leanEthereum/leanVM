module

public import Statement.LeanVmGuestCompleteness
public import Statement.LeanXmss
public import Statement.LeanSphincs
public import Statement.LeanDa

/-!
# The theorems

Every end statement of the repository, one field of `Theorems` each, defined in the file named
beside it. `lean_vm/LeanVM.lean` proves `Theorems` for its compiled programs
(`LeanVM.theorems_hold`) with Lean's three axioms. `statement.tex` states each in mathematics,
with what it does not give.
-/

@[expose] public section

namespace Statement

/-- **The end theorems**, for the extractor program and the guest decoder program, two cost-machine
programs (`CostMachine.lean`) of the same type, so every use names them. -/
structure Theorems
    (leanVmKnowledgeExtractor guestWitnessDecoder : LeanVM.Cost.MachineProgram) : Prop where
  /-- leanVM is knowledge sound for the extractor the program computes (`LeanVm.lean`). -/
  leanVmKnowledgeSoundness : LeanVM.KnowledgeSoundness
      (LeanVM.extractorComputedBy leanVmKnowledgeExtractor)
  /-- leanVM is complete for its honest prover, `LeanVM.Prover.prove` (`LeanVm.lean`). -/
  leanVmCompleteness : LeanVM.Completeness

  /-- Every valid execution of the guest program decodes, by the decoder program, to a seed, a
  statement whose digest is the public input, and a witness holding it (`LeanVmGuest.lean`). -/
  guestKnowledgeSoundness : LeanVM.Node.GuestKnowledgeSoundness guestWitnessDecoder
  /-- A statement's digest binds the seed and the statement, up to a Keccak-256 collision
  (`LeanVmGuest.lean`). -/
  statementDigestBinds : LeanVM.Node.StatementDigestBinds
  /-- The executor runs the guest program to a valid execution on every node within the deployed
  limits, or a child's proof exhibits a Keccak-256 collision (`LeanVmGuestCompleteness.lean`). -/
  guestExecutionComplete : LeanVM.Guest.Completeness.GuestExecutionComplete
  /-- The batching of the children's claims, run outside the circuit, is sound
  (`LeanVmGuestCompleteness.lean`). -/
  batchingSound : LeanVM.Guest.Batch.BatchingSound

  /-- leanXMSS is strongly unforgeable, for one key (`LeanXmss.lean`). -/
  leanXmssStronglyUnforgeable : LeanXmss.RandomPermutationModel.LeanXmssStronglyUnforgeable
  /-- leanSPHINCS is strongly unforgeable, for one key (`LeanSphincs.lean`). -/
  leanSphincsStronglyUnforgeable : Sphincs.LeanSphincsStronglyUnforgeable

  /-- LeanDA is complete, for every `π` (`LeanDa.lean`). -/
  leanDaComplete : LeanDa.LeanDaComplete
  /-- LeanDA is position binding (`LeanDa.lean`). -/
  leanDaPositionBinding : LeanDa.LeanDaPositionBinding
  /-- LeanDA's membership test is sound (`LeanDa.lean`). -/
  leanDaMembershipSound : LeanDa.LeanDaMembershipSound

end Statement

end
