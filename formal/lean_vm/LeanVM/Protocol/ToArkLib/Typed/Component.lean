/-
  LeanVM.Protocol.ToArkLib.Typed.Component

  A front component of an interactive oracle proof on ArkLib's typed interaction trees: its
  definition, its completeness, and its round-by-round knowledge soundness at a given error with
  a named extractor. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Typed.Front

/-!
# Front components

A `Typed.Def O StmtIn WitIn StmtOut WitOut σ` is a reduction at the slot `σ` (a typed interaction
tree with its roles, oracle interfaces and challenge samplers) whose
verifier is front (`frontVerifier`): it samples its challenges with the component's samplers,
reads the prover's moves, and returns a verdict of the branch path, an `Option` (`none`
rejects). The oracles `O` are the input oracles: the honest prover receives their contents with
the witness, the verifier would reach them only through queries, which a front verifier does not
make, and they are handed on unchanged. `Def.reduction` is the component as an ArkLib
`Interaction.Oracle.Reduction`.

* `Complete D relIn relOut`: from the input relation, every honest run (`Runs`: the paths the
  honest prover reaches against fresh challenges, with its output) is accepted with the prover's
  statement, keeps the oracles, and is in the output relation. `Complete.execute` reads it on
  ArkLib's execution: every outcome of the honest execution, for any input oracle interface and
  handler, is so. The executions are probabilistic computations with no failure, so this is
  perfect completeness.
* `Security D relIn relOut err`: round-by-round knowledge soundness in the worst case over
  prefixes at the errors `err`, for a named extractor. For each input statement and oracles it
  gives backward witness maps (`RoundExtractor`) from the input relation, that prover moves cannot
  make knowledge appear (`IsProverPreserving`), that at every verifier prefix a fresh challenge
  makes it appear with probability at most the error there (`IsLocallyBounded`, at the
  component's samplers), and that after the last move the state is the output relation at the
  verdict (`TerminalRelation`). `Security.certificate` is the ArkLib `KnowledgeCertificate`; by
  `samplesChallenges_frontFragment` the component's verifier draws exactly its challenges.

A security holds no real number: the errors are in its type and its propositions, so a security,
its extractor included, computes.
-/

namespace LeanVM.Protocol.Typed

open Interaction Interaction.TwoParty Interaction.Oracle Interaction.Oracle.Security
open OracleComp OracleSpec
open scoped NNReal ENNReal

@[expose] public section

/-- The values satisfying `p`, counted as a subtype, are those of the filtered universe: errors
count bad challenges with `Nat.card`, which needs no `Fintype` instance, and proofs count them
with `Finset`. -/
theorem _root_.LeanVM.Protocol.natCard_subtype_eq_card_filter {α : Type} [Fintype α]
    (p : α → Prop) [DecidablePred p] : Nat.card {a // p a} = (Finset.univ.filter p).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

variable {ι : Type} (O : ι → Type)

/-! ## The relations as knowledge states -/

/-- The verdicts of a component, one claim per context. -/
abbrev verdictFamily (StmtOut : Type) : ClaimFamily.{0, 0} Unit :=
  ⟨fun _ ↦ Option StmtOut⟩

/-- The output problem at oracles `o`: a verdict and a witness are related when the verdict
accepts a statement which, with `o` and the witness, is in the output relation. -/
def outProblem {StmtOut W : Type} (relOut : Set ((StmtOut × ∀ i, O i) × W)) (o : ∀ i, O i) :
    Problem.{0, 0, 0} (verdictFamily StmtOut) where
  Witness _ _ := W
  admissible _ _ := True
  rel _ v w := ∃ t, v = some t ∧ ((t, o), w) ∈ relOut
  rel_admissible _ _ _ _ := trivial

/-- The input relation at a statement and oracles, as a knowledge state. -/
def inState {StmtIn W : Type} (relIn : Set ((StmtIn × ∀ i, O i) × W)) (s : StmtIn)
    (o : ∀ i, O i) : KnowledgeState.{0} :=
  ⟨W, fun w ↦ ((s, o), w) ∈ relIn⟩

/-- A terminal relation reflects the output relation into the terminal knowledge state. -/
theorem terminal_holds_of_rel {tree : Oracle.TypeTree.{0}} {state : KnowledgeState.{0}}
    {X : RoundExtractor tree state} {Context : Type} {family : ClaimFamily.{0, 0} Context}
    {P : Problem.{0, 0, 0} family} {context : tree.ExecutionPath → Context}
    {claim : (path : tree.ExecutionPath) → family.Claim (context path)}
    (T : TerminalRelation X P context claim) (path : tree.ExecutionPath)
    (w : P.Witness (context path) (claim path)) (h : P.rel (context path) (claim path) w) :
    (X.terminalState path).holds ((T.witnessEquiv path).symm w) :=
  (T.knowledge_iff path _).mpr (by rwa [Equiv.apply_symm_apply])

/-! ## Components -/

/-- A front component at a slot: the verdict of a branch path, and the honest prover, which
receives the statement, the oracles' contents and the witness and outputs the next statement, the
oracles and the next witness. The slot is part of the type, so a component fills a slot only when
its schedule is the one written down. -/
structure Def (StmtIn WitIn StmtOut WitOut : Type) (σ : Slot) where
  /-- The verdict on a branch path; `none` rejects. -/
  verdict : StmtIn → σ.tree.BranchPath → Option StmtOut
  /-- The honest prover, a strategy with no setup. -/
  prover : StmtIn × (∀ i, O i) → WitIn →
    Prover.Strategy unifSpec σ.tree σ.roles fun _ ↦ (StmtOut × ∀ i, O i) × WitOut

variable {O} {StmtIn WitIn StmtOut WitOut : Type} {σ : Slot}

/-- The component's tree. -/
abbrev Def.tree (_ : Def O StmtIn WitIn StmtOut WitOut σ) : Oracle.TypeTree.{0} := σ.tree

/-- The component's roles. -/
abbrev Def.roles (_ : Def O StmtIn WitIn StmtOut WitOut σ) : σ.tree.RoleDecoration := σ.roles

/-- The component's oracle interfaces. -/
abbrev Def.oracles (_ : Def O StmtIn WitIn StmtOut WitOut σ) : σ.tree.OracleDecoration :=
  σ.oracles

/-- The component's samplers. -/
abbrev Def.samplers (_ : Def O StmtIn WitIn StmtOut WitOut σ) : Samplers σ.tree σ.roles :=
  σ.samplers

/-- The component's protocol. -/
abbrev Def.protocol (D : Def O StmtIn WitIn StmtOut WitOut σ) : Oracle.Protocol.{0} :=
  ⟨D.tree, D.roles, D.oracles⟩

/-- The component's verifier at a statement, for an input oracle interface. -/
def Def.verifier (D : Def O StmtIn WitIn StmtOut WitOut σ) (initial : PFunctor) (s : StmtIn) :
    Verifier.Strategy unifSpec D.tree D.roles D.oracles initial fun _ ↦ Option StmtOut :=
  frontVerifier D.tree D.roles D.oracles initial D.samplers (D.verdict s)

/-- The component as an ArkLib oracle reduction: the statement is public, the oracles' contents
are the prover's with the witness, and the verifier reaches the oracles through `initial`. -/
def Def.reduction (D : Def O StmtIn WitIn StmtOut WitOut σ) (initial : PFunctor) :
    Oracle.Reduction unifSpec D.protocol initial StmtIn ((∀ i, O i) × WitIn)
      (fun _ ↦ (StmtOut × ∀ i, O i) × WitOut) (fun _ ↦ Option StmtOut) where
  prover s w := pure (D.prover (s, w.1) w.2)
  verifier s := D.verifier initial s

/-- **Completeness**: from the input relation, every honest run of the prover against fresh
challenges from the samplers is accepted with the prover's statement, keeps the oracles, and is
in the output relation. -/
def Complete (D : Def O StmtIn WitIn StmtOut WitOut σ) (relIn : Set ((StmtIn × ∀ i, O i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, O i) × WitOut)) : Prop :=
  ∀ s o w, ((s, o), w) ∈ relIn → ∀ path a,
    Runs D.tree D.roles D.samplers (D.prover (s, o) w) path a →
      D.verdict s path.toBranchPath = some a.1.1 ∧ a.1.2 = o ∧ a ∈ relOut

/-- **Perfect completeness of the execution**: from the input relation, every outcome of the
honest execution, for any input oracle interface and handler, is accepted with the prover's
statement, keeps the oracles, and is in the output relation. -/
theorem Complete.execute {D : Def O StmtIn WitIn StmtOut WitOut σ}
    {relIn : Set ((StmtIn × ∀ i, O i) × WitIn)} {relOut : Set ((StmtOut × ∀ i, O i) × WitOut)}
    (C : Complete D relIn relOut) (initial : PFunctor)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (s : StmtIn) (o : ∀ i, O i)
    (w : WitIn) (hin : ((s, o), w) ∈ relIn) :
    ∀ x ∈ support ((D.reduction initial).execute impl s (o, w)),
      x.2.2 = some x.2.1.1.1 ∧ x.2.1.1.2 = o ∧ x.2.1 ∈ relOut := by
  intro x hx
  simp only [Oracle.Reduction.execute, Def.reduction, pure_bind] at hx
  obtain ⟨hruns, hverdict⟩ := runs_of_mem_support D.tree D.roles D.oracles initial impl
    D.samplers _ (D.verdict s) x hx
  rw [hverdict]
  exact C s o w hin x.1 x.2.1 hruns

/-- **Round-by-round knowledge soundness** at the errors `err`, worst case over prefixes, for a
named extractor: for each input statement and oracles, backward witness maps from the input
relation that prover moves keep, that a fresh challenge at any verifier prefix breaks with
probability at most the error there, and whose state after the last move is the output relation
at the verdict. -/
structure Security (D : Def O StmtIn WitIn StmtOut WitOut σ)
    (relIn : Set ((StmtIn × ∀ i, O i) × WitIn)) (relOut : Set ((StmtOut × ∀ i, O i) × WitOut))
    (err : Errors D.tree D.roles) where
  /-- The backward witness maps. -/
  extractor : (s : StmtIn) → (o : ∀ i, O i) → RoundExtractor D.tree (inState O relIn s o)
  /-- A prover move cannot make knowledge appear. -/
  prover_preserving : ∀ s o, (extractor s o).IsProverPreserving D.roles
  /-- A fresh challenge makes it appear with probability at most the error. -/
  local_bound : ∀ s o,
    (extractor s o).IsLocallyBounded D.roles (schedule D.tree D.roles D.samplers err)
  /-- After the last move, the state is the output relation at the verdict. -/
  terminal : ∀ s o, TerminalRelation (extractor s o) (outProblem O relOut o) (fun _ ↦ ())
    fun path ↦ D.verdict s path.toBranchPath

/-- The security's knowledge certificate at a statement and oracles. -/
noncomputable def Security.certificate {D : Def O StmtIn WitIn StmtOut WitOut σ}
    {relIn : Set ((StmtIn × ∀ i, O i) × WitIn)} {relOut : Set ((StmtOut × ∀ i, O i) × WitOut)}
    {err : Errors D.tree D.roles} (S : Security D relIn relOut err) (s : StmtIn) (o : ∀ i, O i) :
    KnowledgeCertificate D.tree D.roles (inState O relIn s o) where
  extractor := S.extractor s o
  challenges := schedule D.tree D.roles D.samplers err
  prover_preserving := S.prover_preserving s o
  local_bound := S.local_bound s o

/-- The component's verifier draws its security's challenges, for any input oracles. -/
theorem Security.samplesChallenges {D : Def O StmtIn WitIn StmtOut WitOut σ}
    {relIn : Set ((StmtIn × ∀ i, O i) × WitIn)} {relOut : Set ((StmtOut × ∀ i, O i) × WitOut)}
    {err : Errors D.tree D.roles} (S : Security D relIn relOut err) (initial : PFunctor)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (s : StmtIn) (o : ∀ i, O i) :
    SamplesChallenges unifSpec (QueryImpl.id' unifSpec) D.tree D.roles D.oracles initial impl _
      (D.verifier initial s) (S.certificate s o).challenges :=
  samplesChallenges_frontFragment D.tree D.roles D.oracles initial impl D.samplers err _

/-! ## Raising the errors -/

/-- A locally bounded extractor stays bounded at larger errors. -/
theorem isLocallyBounded_mono : (tree : Oracle.TypeTree.{0}) → (roles : tree.RoleDecoration) →
    (s : Samplers tree roles) → (e e' : Errors tree roles) → Errors.Le tree roles e e' →
    {state : KnowledgeState.{0}} → (X : RoundExtractor tree state) →
    X.IsLocallyBounded roles (schedule tree roles s e) →
    X.IsLocallyBounded roles (schedule tree roles s e')
  | .done, _, _, _, _, _, _, _, _ => trivial
  | .public _ next, ⟨.sender, roles⟩, s, e, e', h, _, X, hX => fun move ↦
      isLocallyBounded_mono (next move) (roles move) (s move) (e move) (e' move) (h move)
        (X move).2.2 (hX move)
  | .public _ next, ⟨.receiver, roles⟩, s, e, e', h, _, X, ⟨hb, hX⟩ => by
      refine ⟨?_, fun move ↦ isLocallyBounded_mono (next move) (roles move) (s.2 move)
        (e.2 move) (e'.2 move) (h.2 move) (X move).2.2 (hX move)⟩
      rw [_root_.RoundByRound.GameFamily.isBounded_iff] at hb ⊢
      exact fun r c ↦ (hb r c).trans (ENNReal.coe_le_coe.mpr h.1)
  | .oracle _ next, roles, s, e, e', h, _, X, hX => fun message ↦
      isLocallyBounded_mono (next PUnit.unit) (roles.2 PUnit.unit) s e e' h
        (X message).2.2 (hX message)

/-- Security at errors is security at any larger errors. Inlined before compilation, so the
errors, real numbers, never reach compiled code and a security built with it computes. -/
@[macro_inline]
def Security.mono {D : Def O StmtIn WitIn StmtOut WitOut σ}
    {relIn : Set ((StmtIn × ∀ i, O i) × WitIn)} {relOut : Set ((StmtOut × ∀ i, O i) × WitOut)}
    {err err' : Errors D.tree D.roles} (h : Errors.Le D.tree D.roles err err')
    (S : Security D relIn relOut err) : Security D relIn relOut err' where
  extractor := S.extractor
  prover_preserving := S.prover_preserving
  local_bound s o := isLocallyBounded_mono D.tree D.roles D.samplers err err' h _
    (S.local_bound s o)
  terminal := S.terminal


/-! ## No security below error one -/

/-- A path with no challenge on it: every node is the prover's. -/
def NoChallenge : (tree : Oracle.TypeTree.{0}) → tree.RoleDecoration → tree.ExecutionPath → Prop
  | .done, _, _ => True
  | .public _ next, ⟨.sender, roles⟩, path => NoChallenge (next path.1) (roles path.1) path.2
  | .public _ _, ⟨.receiver, _⟩, _ => False
  | .oracle _ next, roles, path => NoChallenge (next PUnit.unit) (roles.2 PUnit.unit) path.2

/-- Along a path with no challenge, prover-preserving maps carry the terminal state's knowledge
back to the input state at the extracted witness. -/
theorem holds_of_noChallenge : (tree : Oracle.TypeTree.{0}) → (roles : tree.RoleDecoration) →
    {state : KnowledgeState.{0}} → (X : RoundExtractor tree state) →
    X.IsProverPreserving roles → (path : tree.ExecutionPath) → NoChallenge tree roles path →
    (w : (X.terminalState path).Witness) → (X.terminalState path).holds w →
    state.holds (X.extractWitness path w)
  | .done, _, _, _, _, _, _, _, h => h
  | .public _ next, ⟨.sender, roles⟩, _, X, hX, path, hn, w, h =>
      hX.1 path.1 rfl _ (holds_of_noChallenge (next path.1) (roles path.1) (X path.1).2.2
        (hX.2 path.1) path.2 hn w h)
  | .public _ _, ⟨.receiver, _⟩, _, _, _, _, hn, _, _ => hn.elim
  | .oracle _ next, roles, _, X, hX, path, hn, w, h =>
      hX.1 path.1 _ (holds_of_noChallenge (next PUnit.unit) (roles.2 PUnit.unit) (X path.1).2.2
        (hX.2 path.1) path.2 hn w h)

/-- **No security below error one at a first challenge from which every value escapes.** For a
component whose first move is a challenge: if a statement with no witness has, at every
challenge, a rest of the path with no further challenge on which the verdict accepts into the
output relation, the error at the challenge is at least one, whatever the extractor. -/
theorem Security.one_le_of_escape {Ch : Type} {rest : Oracle.TypeTree.{0}}
    {r : rest.RoleDecoration} {ors : (Oracle.TypeTree.public Ch fun _ ↦ rest).OracleDecoration}
    {smp : ProbComp Ch} {sr : Ch → Samplers rest r}
    {D : Def O StmtIn WitIn StmtOut WitOut
      ⟨.public Ch fun _ ↦ rest, ⟨.receiver, fun _ ↦ r⟩, ors, (smp, sr)⟩}
    {relIn : Set ((StmtIn × ∀ i, O i) × WitIn)} {relOut : Set ((StmtOut × ∀ i, O i) × WitOut)}
    {err : Errors (.public Ch fun _ ↦ rest) ⟨.receiver, fun _ ↦ r⟩}
    (Sec : Security D relIn relOut err) (s : StmtIn) (o : ∀ i, O i)
    (hin : ∀ w, ((s, o), w) ∉ relIn)
    (hesc : ∀ c, ∃ p : rest.ExecutionPath, NoChallenge rest r p ∧ ∃ t w,
      D.verdict s (Oracle.TypeTree.ExecutionPath.toBranchPath
        (tree := .public Ch fun _ ↦ rest) ⟨c, p⟩) = some t ∧ ((t, o), w) ∈ relOut) :
    1 ≤ err.1 := by
  have hb := (Sec.local_bound s o).1
  rw [_root_.RoundByRound.GameFamily.isBounded_iff] at hb
  have h1 : Pr{let c ← smp}[RoundExtractor.badChallenge (Sec.extractor s o) c] = 1 := by
    refine (OracleComp.prEvent_eq_one_iff _ _).mpr fun c _ ↦ ?_
    obtain ⟨p, hn, t, w, hv, hout⟩ := hesc c
    let path : (Oracle.TypeTree.public Ch fun _ ↦ rest).ExecutionPath := ⟨c, p⟩
    have hterm := terminal_holds_of_rel (Sec.terminal s o) path w ⟨t, hv, hout⟩
    exact ⟨_, hin _, holds_of_noChallenge rest r _ ((Sec.prover_preserving s o).2 c) p hn _ hterm⟩
  have h := hb () ()
  change Pr{let c ← smp}[RoundExtractor.badChallenge (Sec.extractor s o) c] ≤ (err.1 : ℝ≥0∞)
    at h
  rw [h1] at h
  exact_mod_cast h

end
end LeanVM.Protocol.Typed
