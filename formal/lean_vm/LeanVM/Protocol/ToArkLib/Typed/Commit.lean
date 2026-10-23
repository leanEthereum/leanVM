/-
  LeanVM.Protocol.ToArkLib.Typed.Commit

  An interactive oracle proof that commits to its witness: the prover sends the witness as an
  oracle message, a front component runs over it, and the verifier asks it one question at the
  end. Completeness, and round-by-round knowledge soundness with the extractor that reads the
  witness off the message. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Typed.Component
public import LeanVM.Protocol.ToArkLib.Oracles

/-!
# Commit, reduce, open

`commitSlot M σ` is the slot `σ` behind one oracle message of type `M`. The protocol on it
(`commitReduction D Q`) has the statement public and the witness `m : M`: the prover sends `m` as
the oracle message, then runs the front component `D` with `m` as its one oracle; the verifier
runs `D`'s front verifier and, on `D`'s output `t`, asks the message the question `Q.query t`
(`priorQuery`, routed past the slot) and accepts `Q.out t` when `Q.check` holds of the answer.
The verifier's output on an execution path is `commitVerdict D Q s path`
(`commit_output`), whatever the prover.

* `commit_complete`: if `D` is complete from the witness relation at the message into `Q.rel
  relOut` (the check passes and the output is in `relOut`), every outcome of the honest execution
  is accepted into `relOut`.
* `Security.commitCertificate`: if `D` is secure into `Q.rel relOut` at errors `err`, the
  protocol has a knowledge certificate at the same errors from the witness relation, whose
  extractor reads the witness off the message (`extractWitness_commit`), whose terminal state is
  `relOut` at the verifier's output (`Security.commitTerminal`), and whose challenges the verifier
  draws (`Security.commit_samplesChallenges`). The question needs no challenge of its own: it is
  checked at the leaf, and `Q.rel` makes the component's terminal state the protocol's.
-/

namespace LeanVM.Protocol.Typed

open Interaction Interaction.TwoParty Interaction.Oracle Interaction.Oracle.Security
open OracleComp OracleSpec
open scoped NNReal ENNReal

@[expose] public section

attribute [local implicit_reducible] Interaction.Oracle.TypeTree.runtimeLens

variable (M : Type) [OracleInterface M]

/-- The slot `σ` behind one oracle message of type `M`. -/
abbrev commitSlot (σ : Slot) : Slot :=
  ⟨.oracle M fun _ ↦ σ.tree, ⟨PUnit.unit, fun _ ↦ σ.roles⟩, ⟨inferInstance, fun _ ↦ σ.oracles⟩,
    σ.samplers⟩

/-- The message as the one oracle. -/
abbrev sent {M : Type} (m : M) : ∀ i, OneOracle M i := fun _ ↦ m

/-- The question asked of the message at the end: what to ask on a statement, the check on the
answer, and the statement output when it passes. -/
structure Question (T U : Type) where
  /-- The question. -/
  query : T → OracleInterface.Query M
  /-- The check on the answer. -/
  check : (t : T) → OracleInterface.Response (query t) → Bool
  /-- The statement output. -/
  out : T → U

variable {M} {S T U W : Type}

/-- The verdict once the message is known: a verdict `v`, then the check of the message's answer
to its question. -/
def Question.verdict (Q : Question M T U) (m : M) (v : Option T) : Option U :=
  v.bind fun t ↦ if Q.check t (OracleInterface.answer m (Q.query t)) then some (Q.out t) else none

/-- What the component before the question reaches: the check passes and the output is in
`relOut`. -/
def Question.rel (Q : Question M T U) (relOut : Set ((U × ∀ i, OneOracle M i) × W)) :
    Set ((T × ∀ i, OneOracle M i) × W) :=
  {p | Q.check p.1.1 (OracleInterface.answer (p.1.2 0) (Q.query p.1.1)) = true ∧
    ((Q.out p.1.1, p.1.2), p.2) ∈ relOut}

/-- A verdict reaches `Q.rel relOut` exactly when the verdict after the question reaches
`relOut`. -/
theorem Question.verdict_rel (Q : Question M T U) (relOut : Set ((U × ∀ i, OneOracle M i) × W))
    (m : M) (v : Option T) (w : W) :
    (∃ t, v = some t ∧ ((t, sent m), w) ∈ Q.rel relOut) ↔
      ∃ u, Q.verdict m v = some u ∧ ((u, sent m), w) ∈ relOut := by
  cases v with
  | none => simp [Question.verdict]
  | some t =>
    by_cases hc : Q.check t (OracleInterface.answer m (Q.query t)) = true
    · simp [Question.verdict, Question.rel, hc]
    · simp [Question.verdict, Question.rel, hc]

/-- The witness relation at the message, as the relation the component starts from. -/
def atSent (relIn : S → M → Prop) : Set ((S × ∀ i, OneOracle M i) × Unit) :=
  {p | relIn p.1.1 (p.1.2 0)}

variable {σ : Slot} (D : Def (OneOracle M) S Unit T Unit σ) (Q : Question M T U)

/-- The part of an execution path after the message. -/
abbrev restPath (path : (commitSlot M σ).tree.ExecutionPath) : σ.tree.ExecutionPath := path.2

/-! ## The protocol -/

/-- The verifier's leaf after the component's path: the component's verdict, then the question to
the message, the latest oracle before the slot. -/
def commitLeaf (initial : PFunctor) (s : S) (path : σ.tree.BranchPath) :
    OracleComp (unifSpec + OracleSpec.ofPFunctor (TypeTree.accessAfter σ.tree σ.oracles
      (Access.extend initial (inferInstance : OracleInterface M)) path)) (Option U) :=
  match D.verdict s path with
  | none => pure none
  | some t => (fun (a : (Access.extend initial (inferInstance : OracleInterface M)).B
        (.inr (Q.query t))) ↦ if Q.check t a then some (Q.out t) else none) <$>
      priorQuery σ.tree σ.oracles (Access.extend initial (inferInstance : OracleInterface M)) path
        (.inr (Q.query t))

/-- The verifier: the component's front verifier behind the message, then the question. -/
def commitVerifier (initial : PFunctor) (s : S) :
    Verifier.Strategy unifSpec (commitSlot M σ).tree (commitSlot M σ).roles
      (commitSlot M σ).oracles initial fun _ ↦ Option U :=
  frontFragment (commitSlot M σ).tree (commitSlot M σ).roles (commitSlot M σ).oracles initial
    σ.samplers fun path ↦ commitLeaf D Q initial s path.2

/-- The honest prover: sends the witness, then runs the component with it as the oracle. -/
def commitProver (s : S) (m : M) :
    Prover.Strategy unifSpec (commitSlot M σ).tree (commitSlot M σ).roles
      fun _ ↦ (T × ∀ i, OneOracle M i) × Unit :=
  pure ⟨m, D.prover (s, sent m) ()⟩

/-- The protocol as an ArkLib oracle reduction: the statement public, the witness the message. -/
def commitReduction (initial : PFunctor) :
    Oracle.Reduction unifSpec ⟨(commitSlot M σ).tree, (commitSlot M σ).roles,
      (commitSlot M σ).oracles⟩ initial S M (fun _ ↦ (T × ∀ i, OneOracle M i) × Unit)
      (fun _ ↦ Option U) where
  prover s m := pure (commitProver D s m)
  verifier s := commitVerifier D Q initial s

/-- The verdict on an execution path: the component's on its part of the path, then the question
to the message the path sends. -/
def commitVerdict (s : S) (path : (commitSlot M σ).tree.ExecutionPath) : Option U :=
  Q.verdict path.1 (D.verdict s (restPath path).toBranchPath)

/-- The leaf, run against the handler after an execution path, returns the verdict. -/
theorem simulateQ_commitLeaf (initial : PFunctor)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (s : S)
    (path : (commitSlot M σ).tree.ExecutionPath) :
    simulateQ (Verifier.liftAccessImpl unifSpec _
        (implAfter (commitSlot M σ).tree (commitSlot M σ).oracles initial impl path))
      (commitLeaf D Q initial s (restPath path).toBranchPath) = pure (commitVerdict D Q s path) := by
  change simulateQ (Verifier.liftAccessImpl unifSpec _ (implAfter σ.tree σ.oracles
    (Access.extend initial _) (Access.extendImpl initial _ impl path.1) (restPath path))) _ = _
  unfold commitLeaf commitVerdict
  cases D.verdict s (restPath path).toBranchPath with
  | none => simp [Question.verdict]
  | some t =>
    dsimp only
    rw [simulateQ_map, simulateQ_priorQuery, map_pure]
    rfl

/-- **The verifier outputs the verdict**: on every outcome of an execution, with any prover, the
verifier's output is the verdict on the execution path. -/
theorem commit_output (initial : PFunctor) (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id)
    (s : S) {A : Type}
    (p : Prover.Strategy unifSpec (commitSlot M σ).tree (commitSlot M σ).roles fun _ ↦ A) :
    ∀ x ∈ support (executeStrategies unifSpec (commitSlot M σ).tree (commitSlot M σ).roles
      (commitSlot M σ).oracles initial impl p (commitVerifier D Q initial s)),
      Runs (commitSlot M σ).tree (commitSlot M σ).roles σ.samplers p x.1 x.2.1 ∧
        x.2.2 = commitVerdict D Q s x.1 := by
  intro x hx
  obtain ⟨hruns, hleaf⟩ := runs_of_mem_support_leaf (commitSlot M σ).tree (commitSlot M σ).roles
    (commitSlot M σ).oracles initial impl (commitSlot M σ).samplers p
    (fun path ↦ commitLeaf D Q initial s path.2) x hx
  have hv : x.2.2 ∈ support (pure (commitVerdict D Q s x.1) : OracleComp unifSpec _) := by
    rw [← simulateQ_commitLeaf D Q initial impl s x.1]
    exact hleaf
  rw [support_pure, Set.mem_singleton_iff] at hv
  exact ⟨hruns, hv⟩

/-! ## Completeness -/

variable {D Q} {relIn : S → M → Prop} {relOut : Set ((U × ∀ i, OneOracle M i) × Unit)}

/-- **Completeness**: if the component is complete from the witness relation at the message into
the question's relation, every outcome of the honest execution, for any input oracles, sends the
witness, is accepted with the question's output on the prover's statement, and lands in `relOut`
with the message as the oracle. -/
theorem commit_complete (C : Complete D (atSent relIn) (Q.rel relOut)) (initial : PFunctor)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (s : S) (m : M) (h : relIn s m) :
    ∀ x ∈ support ((commitReduction D Q initial).execute impl s m),
      x.1.1 = m ∧ x.2.2 = some (Q.out x.2.1.1.1) ∧ ((Q.out x.2.1.1.1, sent m), ()) ∈ relOut := by
  intro x hx
  simp only [Oracle.Reduction.execute, commitReduction, pure_bind] at hx
  obtain ⟨⟨rest, hrest, hruns⟩, hout⟩ := commit_output D Q initial impl s _ x hx
  rw [commitProver, support_pure, Set.mem_singleton_iff] at hrest
  obtain ⟨hm, hrest⟩ := Sigma.mk.inj_iff.mp hrest
  obtain rfl := eq_of_heq hrest
  obtain ⟨hv, ho, hcheck, hrel⟩ := C s (sent m) () h x.1.2 x.2.1 hruns
  rw [ho] at hcheck hrel
  refine ⟨hm, ?_, hrel⟩
  rw [hout, commitVerdict, hv, Question.verdict, Option.bind_some, hm]
  simp [hcheck]

/-! ## Knowledge soundness -/

/-- The family of the protocol's output claims, over the message as the oracle. -/
abbrev commitFamily (M U : Type) : ClaimFamily.{0, 0} (∀ i, OneOracle M i) :=
  ⟨fun _ ↦ Option U⟩

/-- The protocol's output problem: the verifier's output accepts a statement which, with the
message and the witness, is in `relOut`. -/
def commitProblem (relOut : Set ((U × ∀ i, OneOracle M i) × W)) :
    Problem.{0, 0, 0} (commitFamily M U) where
  Witness _ _ := W
  admissible _ _ := True
  rel o v w := ∃ u, v = some u ∧ ((u, o), w) ∈ relOut
  rel_admissible _ _ _ _ := trivial

/-- The extractor: read the witness off the message, then the component's maps with the message as
the oracle. -/
def commitExtractor
    (X : (s : S) → (o : ∀ i, OneOracle M i) → RoundExtractor σ.tree (inState _ (atSent relIn) s o))
    (s : S) : RoundExtractor (commitSlot M σ).tree ⟨M, relIn s⟩ :=
  fun m ↦ ⟨inState _ (atSent relIn) s (sent m), fun _ ↦ m, X s (sent m)⟩

/-- **The extractor reads the message**: on every execution path, whatever the terminal witness,
the extracted witness is the message the path sends. -/
theorem extractWitness_commit
    (X : (s : S) → (o : ∀ i, OneOracle M i) → RoundExtractor σ.tree (inState _ (atSent relIn) s o))
    (s : S) (path : (commitSlot M σ).tree.ExecutionPath)
    (w : ((commitExtractor X s).terminalState path).Witness) :
    (commitExtractor X s).extractWitness path w = path.1 :=
  rfl

variable {err : Errors σ.tree σ.roles}

/-- **The knowledge certificate**: the component's security into the question's relation gives the
protocol a certificate at the same errors from the witness relation, with the extractor that reads
the witness off the message. -/
noncomputable def Security.commitCertificate (Sec : Security D (atSent relIn) (Q.rel relOut) err)
    (s : S) : KnowledgeCertificate (commitSlot M σ).tree (commitSlot M σ).roles ⟨M, relIn s⟩ where
  extractor := commitExtractor Sec.extractor s
  challenges := schedule (commitSlot M σ).tree (commitSlot M σ).roles σ.samplers err
  prover_preserving := ⟨fun _ _ h ↦ h, fun m ↦ Sec.prover_preserving s (sent m)⟩
  local_bound := fun m ↦ Sec.local_bound s (sent m)

/-- **The terminal relation**: after the last move, the certificate's state is `relOut` at the
verifier's output, with the message as the oracle. -/
def Security.commitTerminal (Sec : Security D (atSent relIn) (Q.rel relOut) err) (s : S) :
    TerminalRelation (commitExtractor Sec.extractor s) (commitProblem relOut)
      (fun path ↦ sent path.1) (commitVerdict D Q s) where
  witnessEquiv path := (Sec.terminal s (sent path.1)).witnessEquiv path.2
  knowledge_iff path w := ((Sec.terminal s (sent path.1)).knowledge_iff path.2 w).trans
    (by exact Q.verdict_rel relOut path.1 _ _)

/-- The protocol's verifier draws the certificate's challenges, for any input oracles. -/
theorem Security.commit_samplesChallenges (Sec : Security D (atSent relIn) (Q.rel relOut) err)
    (initial : PFunctor) (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (s : S) :
    SamplesChallenges unifSpec (QueryImpl.id' unifSpec) (commitSlot M σ).tree
      (commitSlot M σ).roles (commitSlot M σ).oracles initial impl _ (commitVerifier D Q initial s)
      (Sec.commitCertificate s).challenges :=
  samplesChallenges_frontFragment (commitSlot M σ).tree (commitSlot M σ).roles
    (commitSlot M σ).oracles initial impl (commitSlot M σ).samplers err _

end
end LeanVM.Protocol.Typed
