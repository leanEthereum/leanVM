/-
  LeanVM.Protocol.Spine.Compose

  The oracle protocol on ArkLib's typed framework: the commitment, the bundle of the five phases
  at their slots, the composed protocol, its extractor and the stack it extracts, and the two
  master theorems.
-/

module

public import LeanVM.Protocol.Spine.Slots

/-!
# The oracle protocol and its master theorems

The oracle protocol is the stack sent as an oracle message, then `bus ⟫ table ⟫ pub ⟫ flock ⟫
opening`, then one question to the stack (`stackQuestion`): the commit-reduce-open protocol of
`LeanVM.Protocol.ToArkLib.Typed.Commit` at the stack, over the five phases in sequence. The five
phases are the fields of a `Phases I`, each a typed front component at its slot
(`LeanVM.Protocol.Spine.Slots`), so that none can query the stack; their proofs are the fields of
`Phases.Complete` and `Phases.Security`, the latter at the slots' errors. The opening ends in
`Seam.opened`: the final weighted claim holds of the stack, which is what the question checks.
The protocol starts from `M3Holds` of the statement and the stack and ends with nothing left to
check (`Seam.done`).

`piop_completeness`: given every phase's completeness, on every statement and stack satisfying
`M3Honest` (`M3Holds`, the padding rows honest) every outcome of the honest execution is accepted; `piop_perfectCompleteness` is its
reading as probability one. `piop_knowledgeSoundness`: given every phase's security, the protocol
has a knowledge certificate (round-by-round knowledge soundness, worst case over prefixes) from
`M3Holds` at `piopErrors I`, the slots' errors side by side, for the named extractor
`piopExtractor` (the commitment's step, which reads the stack off the message, then the phases'
own, composed by ArkLib's composition of backward witness maps), whose terminal state is
`Seam.done` at the verifier's output (`piopTerminal`) and whose challenges the verifier draws. The
stack the extractor returns on a path is the committed message (`piopExtractedStack_eq`), and a
path the verifier accepts on whose committed stack `M3Holds` fails has a bad challenge
(`piop_badChallenge`, ArkLib's `extraction_failure_implies_bad_challenge`).

Both theorems are stated in the ideal oracle model, over an abstract instance, and are conditional
only on the phases' proofs; `LeanVM.Protocol.Piop` fills them at every instance.
-/

namespace LeanVM.Protocol

open Interaction Interaction.TwoParty Interaction.Oracle Interaction.Oracle.Security
open OracleComp OracleSpec Typed
open scoped NNReal ENNReal

@[expose] public section

variable (I : M3Instance)

/-! ## Slots and errors -/

/-- The slot of the five phases: the bus, the table sumcheck, the public input, Flock and the
opening, side by side. -/
abbrev phasesSlot : Slot :=
  ((((busSlot I).append (tableSlot I)).append pubSlot).append (flockPhaseSlot I)).append
    openingSlot

/-- The protocol's slot: the stack as an oracle message, then the five phases. -/
abbrev piopSlot : Slot := commitSlot (Column I.μ) (phasesSlot I)

/-- The protocol's errors: the five slots' side by side; the commitment has no challenge. -/
noncomputable abbrev piopErrors : Errors (piopSlot I).tree (piopSlot I).roles :=
  Errors.append _ _ (Errors.append _ _ (Errors.append _ _ (Errors.append (busSlot I).tree
    (busSlot I).roles (busErrors I) (tableErrors I)) pubErrors) (flockErrors I)) (openingErrors I)

/-- **The protocol's error is small at admissible sizes.** With the bus's leaf stacks of
log-height at most 30, tables of log-height at most 32, at most `2^16` constraints, at most `2^32`
batched compressions and at most `2^16` pooled claims, the errors along every path sum to at most
`(2^32 + 2^31 + 2^20) / |E|`, less than `2^{-159}`, the fingerprint's `2^32` and the ring
switching's `2^31` dominating. -/
theorem piopErrors_bounded (hμ : I.μBus ≤ 30) (hτ : I.τmax ≤ 32) (hB : I.B ≤ 2 ^ 16)
    (hk : ∀ r ∈ I.flock, r.kBatch ≤ 32) (hJ : I.poolSize ≤ 2 ^ 16) :
    Errors.Bounded (piopSlot I).tree (piopSlot I).roles (piopErrors I)
      (overE (2 ^ 32 + 2 ^ 31 + 2 ^ 20)) := by
  have h := ((((busErrors_bounded I).append (tableErrors_bounded I)).append
    pubErrors_bounded).append (flockErrors_bounded I hk)).append (openingErrors_bounded I)
  refine fun path ↦ (h path.2).trans (le_of_eq_of_le (b := overE (4 * 2 ^ I.μBus +
    ((I.μBus + 1) * 2 + 2 * I.μBus * I.μBus + 3 * I.μBus + 3) + (I.B + 2 + I.τmax * 3) + 1 +
    (4 * 32 + 302 + 2 ^ 31 + 2 ^ 15) + (I.poolSize - 1))) ?_ (overE_mono ?_))
  · simp only [nat_mul_overE, overE_add]
  · have h2μ : 2 ^ I.μBus ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) hμ
    have hμμ : I.μBus * I.μBus ≤ 30 * 30 := Nat.mul_le_mul hμ hμ
    have hμμ' : 2 * I.μBus * I.μBus = 2 * (I.μBus * I.μBus) := by ring
    rw [hμμ']
    omega

/-! ## The bundle of phases -/

/-- The five phases after the commitment, each a typed front component at its slot. -/
structure Phases where
  /-- The bus phase: from `M3Holds` of the oracle to the point, the forms and the boundary
  claims (§5.2 to §5.4). -/
  bus : Typed.Def (TheOracle I) I.Stmt Unit (I.Stmt × BusOut I) Unit (busSlot I)
  /-- The table sumcheck: from the forms to column claims (§5.5). -/
  table : Typed.Def (TheOracle I) (I.Stmt × BusOut I) Unit (I.Stmt × TableOut I) Unit
    (tableSlot I)
  /-- The public-input phase: the public lines become column claims (§8.2). -/
  pub : Typed.Def (TheOracle I) (I.Stmt × TableOut I) Unit (I.Stmt × PubOut I) Unit pubSlot
  /-- The Flock phase: the Flock predicate becomes a weighted claim (Annex C). -/
  flock : Typed.Def (TheOracle I) (I.Stmt × PubOut I) Unit (I.Stmt × FlockOut I) Unit
    (flockPhaseSlot I)
  /-- The opening phase: the pool is batched into one weighted claim, which the protocol's
  question then asks the stack (§8.5). -/
  opening : Typed.Def (TheOracle I) (I.Stmt × FlockOut I) Unit (WeightedClaim I) Unit openingSlot

variable {I}

/-- The five phases in sequence. -/
def Phases.toDef (P : Phases I) :
    Typed.Def (TheOracle I) I.Stmt Unit (WeightedClaim I) Unit (phasesSlot I) :=
  (((P.bus.append P.table).append P.pub).append P.flock).append P.opening

/-- The completeness halves of the five phases, against the seams. -/
structure Phases.Complete (P : Phases I) : Prop where
  /-- The bus phase's. -/
  bus : Typed.Complete P.bus (Seam.commitHonest I) (Seam.bus I)
  /-- The table sumcheck's. -/
  table : Typed.Complete P.table (Seam.bus I) (Seam.table I)
  /-- The public-input phase's. -/
  pub : Typed.Complete P.pub (Seam.table I) (Seam.pub I)
  /-- The Flock phase's. -/
  flock : Typed.Complete P.flock (Seam.pub I) (Seam.flock I)
  /-- The opening phase's. -/
  opening : Typed.Complete P.opening (Seam.flock I) (Seam.opened I)

/-- The five phases' completeness in sequence. -/
theorem Phases.Complete.toDef {P : Phases I} (C : P.Complete) :
    Typed.Complete P.toDef (Seam.commitHonest I) (Seam.opened I) :=
  (((C.bus.append C.table).append C.pub).append C.flock).append C.opening

/-- The security halves of the five phases, against the seams, at the slots' errors. -/
structure Phases.Security (P : Phases I) where
  /-- The bus phase's. -/
  bus : Typed.Security P.bus (Seam.commit I) (Seam.bus I) (busErrors I)
  /-- The table sumcheck's. -/
  table : Typed.Security P.table (Seam.bus I) (Seam.table I) (tableErrors I)
  /-- The public-input phase's. -/
  pub : Typed.Security P.pub (Seam.table I) (Seam.pub I) pubErrors
  /-- The Flock phase's. -/
  flock : Typed.Security P.flock (Seam.pub I) (Seam.flock I) (flockErrors I)
  /-- The opening phase's. -/
  opening : Typed.Security P.opening (Seam.flock I) (Seam.opened I) (openingErrors I)

/-- The five phases' security in sequence, at the slots' errors side by side. It computes: the
compositions are inlined before compilation and the errors stay in types. -/
def Phases.Security.toDef {P : Phases I} (S : P.Security) :
    Typed.Security P.toDef (Seam.commit I) (Seam.opened I) (piopErrors I) :=
  (((S.bus.append S.table).append S.pub).append S.flock).append S.opening

/-! ## The oracle protocol -/

/-- The oracle protocol as an ArkLib oracle reduction: the statement public, the stack the
witness, sent as the first message; `initial` is whatever the verifier may query before it. -/
def leanVmPiop (P : Phases I) (initial : PFunctor) :=
  commitReduction P.toDef (stackQuestion I) initial

/-- Its verifier at a statement. -/
def leanVmVerifier (P : Phases I) (initial : PFunctor) (s : I.Stmt) :=
  commitVerifier P.toDef (stackQuestion I) initial s

/-- The verifier's verdict on an execution path: the five phases' verdicts in sequence, then the
stack's answer to the final claim checked. -/
def piopVerdict (P : Phases I) (s : I.Stmt) (path : (piopSlot I).tree.ExecutionPath) :
    Option Unit :=
  commitVerdict P.toDef (stackQuestion I) s path

/-- **The verifier outputs the verdict**: on every outcome of an execution, with any prover, the
verifier's output is the verdict on the execution path. -/
theorem piop_output (P : Phases I) (initial : PFunctor)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (s : I.Stmt) {A : Type}
    (p : Prover.Strategy unifSpec (piopSlot I).tree (piopSlot I).roles fun _ ↦ A) :
    ∀ x ∈ support (executeStrategies unifSpec (piopSlot I).tree (piopSlot I).roles
      (piopSlot I).oracles initial impl p (leanVmVerifier P initial s)),
      x.2.2 = piopVerdict P s x.1 :=
  fun x hx ↦ (commit_output P.toDef (stackQuestion I) initial impl s p x hx).2

/-! ## The master theorems -/

/-- **Completeness.** On every statement and stack with `M3Honest` (`M3Holds`, the padding rows
honest), every outcome of the honest execution, for any input oracles, sends the stack and is
accepted. -/
theorem piop_completeness (P : Phases I) (C : P.Complete) (initial : PFunctor)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (input : I.Stmt) (q : Column I.μ)
    (h : ((input, fun i ↦ i.elim0), q) ∈ M3HonestRel I) :
    ∀ x ∈ support ((leanVmPiop P initial).execute impl input q),
      x.1.1 = q ∧ x.2.2 = some () ∧ (((), sent q), ()) ∈ Seam.done I :=
  commit_complete (relIn := M3Honest I) C.toDef initial impl input q h

/-- **Perfect completeness.** On every statement and stack with `M3Honest`, the honest prover
convinces the verifier with probability one. -/
theorem piop_perfectCompleteness (P : Phases I) (C : P.Complete) (initial : PFunctor)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (input : I.Stmt) (q : Column I.μ)
    (h : ((input, fun i ↦ i.elim0), q) ∈ M3HonestRel I) :
    Pr{let x ← (leanVmPiop P initial).execute impl input q}[x.2.2 = some ()] = 1 :=
  (OracleComp.prEvent_eq_one_iff _ _).mpr fun x hx ↦
    (piop_completeness P C initial impl input q h x hx).2.1

/-- The extractor: the commitment's step, which reads the stack off the message, then the five
phases' backward witness maps with the message as the oracle. It computes. -/
def piopExtractor (P : Phases I) (S : P.Security) (s : I.Stmt) :
    RoundExtractor (piopSlot I).tree ⟨Column I.μ, M3Holds I s⟩ :=
  commitExtractor S.toDef.extractor s

/-- **The extractor reads the stack.** On every execution path, whatever the terminal witness, the
extracted stack is the committed message. -/
theorem piopExtractedStack_eq (P : Phases I) (S : P.Security) (s : I.Stmt)
    (path : (piopSlot I).tree.ExecutionPath)
    (w : ((piopExtractor P S s).terminalState path).Witness) :
    (piopExtractor P S s).extractWitness path w = path.1 :=
  rfl

/-- The protocol's knowledge certificate at a statement: the extractor `piopExtractor`, the
challenges at `piopErrors I`. -/
noncomputable def piopCertificate (P : Phases I) (S : P.Security) (s : I.Stmt) :
    KnowledgeCertificate (piopSlot I).tree (piopSlot I).roles ⟨Column I.μ, M3Holds I s⟩ :=
  S.toDef.commitCertificate s

/-- The certificate's terminal relation: after the last move, its state is `Seam.done` at the
verifier's verdict, with the committed stack as the oracle. -/
noncomputable def piopTerminal (P : Phases I) (S : P.Security) (s : I.Stmt) :
    TerminalRelation (piopExtractor P S s) (commitProblem (Seam.done I)) (fun path ↦ sent path.1)
      (piopVerdict P s) :=
  S.toDef.commitTerminal s

/-- **Round-by-round knowledge soundness** at `piopErrors I`, worst case over prefixes, for the
extractor `piopExtractor P S`: a knowledge certificate from `M3Holds` whose extractor is that
one, whose challenges are the slots' samplers at the slots' errors and are what the verifier
draws, and whose terminal state is the verdict's acceptance (`piopTerminal`). Each challenge can
turn the state from false to true with probability at most its error. -/
theorem piop_knowledgeSoundness (P : Phases I) (S : P.Security) (initial : PFunctor)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (s : I.Stmt) :
    ∃ cert : KnowledgeCertificate (piopSlot I).tree (piopSlot I).roles ⟨Column I.μ, M3Holds I s⟩,
      cert.extractor = piopExtractor P S s ∧
      cert.challenges = schedule (piopSlot I).tree (piopSlot I).roles (piopSlot I).samplers
        (piopErrors I) ∧
      SamplesChallenges unifSpec (QueryImpl.id' unifSpec) (piopSlot I).tree (piopSlot I).roles
        (piopSlot I).oracles initial impl _ (leanVmVerifier P initial s) cert.challenges :=
  ⟨piopCertificate P S s, rfl, rfl, S.toDef.commit_samplesChallenges initial impl s⟩

/-- **A bad challenge explains every false acceptance.** On a path the verifier accepts whose
committed stack fails `M3Holds`, some challenge on the path turned the extractor's state from
false to true: ArkLib's `extraction_failure_implies_bad_challenge` on the certificate. -/
theorem piop_badChallenge (P : Phases I) (S : P.Security) (s : I.Stmt)
    (path : (piopSlot I).tree.ExecutionPath) (hacc : piopVerdict P s path = some ())
    (hbad : ¬ M3Holds I s path.1) :
    RoundExtractor.BadChallengeOnPath (piopExtractor P S s) (piopSlot I).roles path
      (((piopTerminal P S s).witnessEquiv path).symm ()) :=
  RoundExtractor.extraction_failure_implies_bad_challenge _ _
    (piopCertificate P S s).prover_preserving path _
    (terminal_holds_of_rel (piopTerminal P S s) path () ⟨(), hacc, trivial⟩) hbad

end
end LeanVM.Protocol
