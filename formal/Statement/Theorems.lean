module

public import Statement.LeanVmGuestCompleteness
public import Statement.LeanXmss
public import Statement.LeanSphincs
public import Statement.LeanDa

/-!
# The theorems

Everything this repository proves, in one place: each field of `Theorems` is one end statement,
defined in the file of `Statement/` named next to it. `lean_vm/LeanVM.lean` proves `Theorems` for
its compiled programs (`LeanVM.theorems_hold`), and the build fails if its axioms are ever more than
Lean's three (`propext`, `Classical.choice`, `Quot.sound`). `Corollaries.lean` composes some of the
fields; a reviewer may skip it.

`Theorems` takes two programs of the cost machine (`CostMachine.lean`), of the same type, so every
use names them: `leanVmKnowledgeExtractor`, the extractor leanVM's knowledge soundness is stated for
(`LeanVM.extractorComputedBy`), and `guestWitnessDecoder`, the decoder that names the guest
program's witness (`GuestKnowledgeSoundness`, `LeanVmGuest.lean`). The statement constrains them
only by their size bounds and budgets, whose docstrings say what those exclude and what they do
not. Every statement with an adversary is in the random-permutation model (`statement.tex`).

What no field states: security with many keys (each signature game has one key); anything about a
claim an aggregate holds through a child (the guest statements cover one node, `LeanVmGuest.lean`);
that an accepted aggregate's signatures were made by their keys' holders, or that its DA roots
commit to codewords (the guest's relation evaluates the deployed Keccak-f[1600], the signature and
LeanDA games the model's permutation, and no statement composes them). Both signature bounds charge
only the adversary's own calls of `π` and `π⁻¹`: the signer's grinding, key generation and the
forgery's verification are the game's. Signed messages are 32 bytes: a longer payload needs an
outer hash, whose collisions are outside the signature bounds.
-/

@[expose] public section

namespace Statement

/-- **The end theorems**, for the extractor program and the guest decoder program (two parameters
of the same type: every use names them). -/
structure Theorems
    (leanVmKnowledgeExtractor guestWitnessDecoder : LeanVM.Cost.MachineProgram) : Prop where
  /-- leanVM is knowledge sound for the straight-line extractor the program computes,
  `extractorComputedBy leanVmKnowledgeExtractor`: at most `(Q + 2^14) · 2^-128 +
  5 (Q + 2^14)² · 2^-256` for `Q ≤ 2^128` queries (`LeanVm.lean`). The program extracts nothing if
  its size or its run's price exceeds its bound or budget (`leanVmKnowledgeExtractorBudget N`, for
  `N` permutation queries: about `2^81` up to `2^50` queries, `O(N·log³N)`), and extracting nothing
  from an accepted proof is a break; so, but with that probability, the program extracts a valid
  execution within its budget. That a price unit is a constant number of instructions of a 64-bit
  CPU is trusted (`CostMachine.lean`). -/
  leanVmKnowledgeSoundness : LeanVM.KnowledgeSoundness
      (LeanVM.extractorComputedBy leanVmKnowledgeExtractor)
  /-- leanVM is complete: the honest prover's (`LeanVM.leanVmHonestProver`, the executable
  `LeanVM.Prover.prove` of `Prover/Prove.lean`) proof of a valid execution of committed size at
  most `2^28`, at an inverse rate `2^ρ` with `1 ≤ ρ ≤ 4` and `2^33` nonces per proof of work, is
  rejected with probability at most `2^-256` (`LeanVm.lean`). -/
  leanVmCompleteness : LeanVM.Completeness

  /-- Every valid execution of the leanISA guest program proves the node statement its public input
  commits to: the decoder program outputs, within its size bound and budget, the encoding of a
  seed, a statement whose digest under that seed is the input's, and a witness for it
  (`NodeRelation`, `LeanVmGuest.lean`): each raw signature verifying and each signature claim held
  by a raw signature or a child whose proof the deferring verifier accepts, the DA digest that of
  the blob matrix it checks, zeros or a child's, and its deferred claim the batching of its
  children's. A child's proof is accepted with the bytecode's value at the child's point taken from
  the witness, which no end statement requires true, so a child's claims carry knowledge only
  through the root's deferred claim and a batching sound in the circuit (`LeanVmGuest.lean`). The
  blob matrix opens the membership challenge the witness chooses: only the outer verifier's
  derivation of the root's challenge, not modelled, makes its rows codewords. -/
  guestKnowledgeSoundness : LeanVM.Node.GuestKnowledgeSoundness guestWitnessDecoder
  /-- A statement's digest binds the seed and the statement, up to a Keccak-256 collision among the
  candidates (`LeanVmGuest.lean`). With `leanVmKnowledgeSoundness` and `guestKnowledgeSoundness` it
  gives what an accepted proof establishes, `Statement.Corollaries`' `aggregateSound`. -/
  statementDigestBinds : LeanVM.Node.StatementDigestBinds
  /-- The leanISA guest program is complete on the seven families of `CoveredNode`, under the
  deployed seed and within the deployed limits, wherever every child carries the honest prover's
  proof (`HonestChild`) (`LeanVmGuestCompleteness.lean`). -/
  guestCompleteOnHonestChildren : LeanVM.Guest.Completeness.GuestCompleteOnHonestChildren
  /-- The same honest prover's proof of an execution of the guest program is rarely refused: it
  makes none, or the verifier refusing a zero challenge rejects it, with probability at most
  `2^-126` in the random-permutation model (`LeanVmGuestCompleteness.lean`). Read for the deployed
  Keccak, it is what makes a child carrying the honest proof a `HonestChild`. -/
  honestProofRarelyRefused : LeanVM.Guest.Completeness.HonestProofRarelyRefused
  /-- The batching run outside the circuit is sound: at most `(QA + QV + 1) · M · 2^-191 +
  5 (QA + QV)² · 2^-256` for fewer than `M` children, `QA ≤ 2^128`, `QV ≤ 2^96`; it does not
  compose with the in-circuit statements (`LeanVmGuestCompleteness.lean`). -/
  batchingSound : LeanVM.Guest.Batch.BatchingSound
  
  /-- leanXMSS is strongly unforgeable, for one key: at most `(q + 2^10) · 2^-127` for an
  adversary making `q` calls of `π` and `π⁻¹` itself and at most `2^32` signing requests
  (`LeanXmss.lean`); the honest parties' hashing is not charged to `q`. The adversary chooses each
  request's leaf index, and a run that requests one twice is a loss. -/
  leanXmssStronglyUnforgeable : LeanXmss.RandomPermutationModel.LeanXmssStronglyUnforgeable
  /-- leanSPHINCS is strongly unforgeable, for one key: at most `(q + 2^19) · 2^-127` for an
  adversary making `q` calls of `π` and `π⁻¹` itself and at most `1,182,000,000` signing requests
  (`LeanSphincs.lean`); the honest parties' hashing is not charged to `q`. -/
  leanSphincsStronglyUnforgeable : Sphincs.LeanSphincsStronglyUnforgeable

  /-- LeanDA is perfectly complete, for every `π` (`LeanDa.lean`). -/
  leanDaComplete : LeanDa.LeanDaPerfectlyComplete
  /-- LeanDA is position binding: at most `(Q + 1)² · 2^-256` for every `Q` (`LeanDa.lean`). -/
  leanDaPositionBinding : LeanDa.LeanDaPositionBinding
  /-- LeanDA is code binding if its argument, querying the model's oracles, is knowledge sound in
  the random-permutation model with a straight-line extractor (`LeanDa.lean`), for a relation
  evaluated over the model's permutation: leanVM's argument, whose relation uses the deployed
  Keccak-f[1600], cannot meet that hypothesis, so nothing here makes an accepted aggregate's DA root
  code binding. -/
  leanDaCodeBinding : LeanDa.LeanDaCodeBinding

end Statement

end
