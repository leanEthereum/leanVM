/-
  LeanVM.Protocol.ToArkLib.Typed.Append

  Two typed front components in sequence: their trees, samplers, errors and provers appended,
  their verdicts chained. Completeness composes, and round-by-round knowledge soundness composes
  at the errors side by side through ArkLib's composition of backward witness maps. Candidate for
  ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Typed.Component

/-!
# Front components in sequence

`D₁.append D₂` runs `D₁`, then `D₂` from `D₁`'s output: its tree is ArkLib's dependent append
`PFunctor.FreeM.append` with a constant suffix, its roles and oracle interfaces the decorations'
append, its samplers and errors the two side by side (`Samplers.append`, `Errors.append`), its
honest prover `D₁`'s followed by `D₂`'s on `D₁`'s output (`proverAppend`), and its verdict `D₁`'s
verdict followed by `D₂`'s on it, a rejection of either rejecting.

* `Complete.append`: completeness composes, through the honest runs of a front component
  (`Runs`): every outcome of the honest execution is an honest run with the verdict at its path
  (`runs_of_mem_support`).
* `Security.append`: security composes at the errors side by side. The backward witness maps are
  ArkLib's `RoundExtractor.append`, the second component's maps entered at the first's terminal
  state through its terminal relation (`RoundExtractor.changeInputState`) where the first accepts,
  and the maps of a false state where it rejects (`falseExtractor`); the bounds are ArkLib's
  `isProverPreserving_append`, `isLocallyBounded_append` and `TerminalRelation.append`. This is
  ArkLib's own composition of knowledge, proved at the pin.
-/

namespace LeanVM.Protocol.Typed

open Interaction Interaction.TwoParty Interaction.Oracle Interaction.Oracle.Security
open Interaction.Oracle.TypeTree OracleComp OracleSpec
open PFunctor.FreeM.Displayed (Decoration)
open scoped NNReal ENNReal

@[expose] public section

attribute [local implicit_reducible] Interaction.Oracle.TypeTree.runtimeLens

/-! ## Samplers, errors and provers in sequence -/

/-- The samplers of two trees in sequence. -/
def Samplers.append : (t₁ : Oracle.TypeTree.{0}) → (r₁ : t₁.RoleDecoration) →
    Samplers t₁ r₁ → {t₂ : Oracle.TypeTree.{0}} → {r₂ : t₂.RoleDecoration} → Samplers t₂ r₂ →
    Samplers (PFunctor.FreeM.append t₁ fun _ ↦ t₂) (Decoration.append r₁ fun _ ↦ r₂)
  | .done, _, _, _, _, s₂ => s₂
  | .public _ next, ⟨.sender, roles⟩, s₁, _, _, s₂ => fun move ↦
      Samplers.append (next move) (roles move) (s₁ move) s₂
  | .public _ next, ⟨.receiver, roles⟩, s₁, _, _, s₂ =>
      (s₁.1, fun move ↦ Samplers.append (next move) (roles move) (s₁.2 move) s₂)
  | .oracle _ next, roles, s₁, _, _, s₂ => Samplers.append (next PUnit.unit) (roles.2 PUnit.unit) s₁ s₂

/-- The errors of two trees in sequence: each challenge keeps its error. -/
def Errors.append : (t₁ : Oracle.TypeTree.{0}) → (r₁ : t₁.RoleDecoration) →
    Errors t₁ r₁ → {t₂ : Oracle.TypeTree.{0}} → {r₂ : t₂.RoleDecoration} → Errors t₂ r₂ →
    Errors (PFunctor.FreeM.append t₁ fun _ ↦ t₂) (Decoration.append r₁ fun _ ↦ r₂)
  | .done, _, _, _, _, e₂ => e₂
  | .public _ next, ⟨.sender, roles⟩, e₁, _, _, e₂ => fun move ↦
      Errors.append (next move) (roles move) (e₁ move) e₂
  | .public _ next, ⟨.receiver, roles⟩, e₁, _, _, e₂ =>
      (e₁.1, fun move ↦ Errors.append (next move) (roles move) (e₁.2 move) e₂)
  | .oracle _ next, roles, e₁, _, _, e₂ => Errors.append (next PUnit.unit) (roles.2 PUnit.unit) e₁ e₂

/-- The schedule of two trees in sequence is ArkLib's appended schedule. -/
theorem schedule_append : (t₁ : Oracle.TypeTree.{0}) → (r₁ : t₁.RoleDecoration) →
    (s₁ : Samplers t₁ r₁) → (e₁ : Errors t₁ r₁) → {t₂ : Oracle.TypeTree.{0}} →
    {r₂ : t₂.RoleDecoration} → (s₂ : Samplers t₂ r₂) → (e₂ : Errors t₂ r₂) →
    schedule _ _ (Samplers.append t₁ r₁ s₁ s₂) (Errors.append t₁ r₁ e₁ e₂) =
      RoundExtractor.appendSchedule (fun _ ↦ t₂) r₁ (fun _ ↦ r₂) (schedule t₁ r₁ s₁ e₁)
        fun _ ↦ schedule t₂ r₂ s₂ e₂
  | .done, _, _, _, _, _, _, _ => rfl
  | .public _ next, ⟨.sender, roles⟩, s₁, e₁, _, _, s₂, e₂ =>
      Prod.ext rfl (funext fun move ↦
        schedule_append (next move) (roles move) (s₁ move) (e₁ move) s₂ e₂)
  | .public _ next, ⟨.receiver, roles⟩, s₁, e₁, _, _, s₂, e₂ =>
      Prod.ext rfl (funext fun move ↦
        schedule_append (next move) (roles move) (s₁.2 move) (e₁.2 move) s₂ e₂)
  | .oracle _ next, roles, s₁, e₁, _, _, s₂, e₂ =>
      funext fun _ ↦ schedule_append (next PUnit.unit) (roles.2 PUnit.unit) s₁ e₁ s₂ e₂

/-- Errors at most others stay so side by side. -/
theorem Errors.Le.append : (t₁ : Oracle.TypeTree.{0}) → (r₁ : t₁.RoleDecoration) →
    {e₁ e₁' : Errors t₁ r₁} → Errors.Le t₁ r₁ e₁ e₁' → {t₂ : Oracle.TypeTree.{0}} →
    {r₂ : t₂.RoleDecoration} → {e₂ e₂' : Errors t₂ r₂} → Errors.Le t₂ r₂ e₂ e₂' →
    Errors.Le _ _ (Errors.append t₁ r₁ e₁ e₂) (Errors.append t₁ r₁ e₁' e₂')
  | .done, _, _, _, _, _, _, _, _, h₂ => h₂
  | .public _ next, ⟨.sender, roles⟩, _, _, h₁, _, _, _, _, h₂ => fun move ↦
      Errors.Le.append (next move) (roles move) (h₁ move) h₂
  | .public _ next, ⟨.receiver, roles⟩, _, _, h₁, _, _, _, _, h₂ =>
      ⟨h₁.1, fun move ↦ Errors.Le.append (next move) (roles move) (h₁.2 move) h₂⟩
  | .oracle _ next, roles, _, _, h₁, _, _, _, _, h₂ =>
      Errors.Le.append (next PUnit.unit) (roles.2 PUnit.unit) h₁ h₂

/-- The errors side by side, summed along a path: the first's along its first piece, plus the
second's along the rest. -/
theorem Errors.along_append : (t₁ : Oracle.TypeTree.{0}) → (r₁ : t₁.RoleDecoration) →
    (e₁ : Errors t₁ r₁) → {t₂ : Oracle.TypeTree.{0}} → {r₂ : t₂.RoleDecoration} →
    (e₂ : Errors t₂ r₂) →
    (path : Oracle.TypeTree.BranchPath (PFunctor.FreeM.append t₁ fun _ ↦ t₂)) →
    Errors.along _ _ (Errors.append t₁ r₁ e₁ e₂) path =
      Errors.along t₁ r₁ e₁ (PFunctor.FreeM.Path.split t₁ _ path).1 +
        Errors.along t₂ r₂ e₂ (PFunctor.FreeM.Path.split t₁ _ path).2
  | .done, _, _, _, _, _, _ => (zero_add _).symm
  | .public _ next, ⟨.sender, roles⟩, e₁, _, _, e₂, path =>
      Errors.along_append (next path.1) (roles path.1) (e₁ path.1) e₂ path.2
  | .public _ next, ⟨.receiver, roles⟩, e₁, _, _, e₂, path =>
      (congrArg (e₁.1 + ·) (Errors.along_append (next path.1) (roles path.1) (e₁.2 path.1) e₂
        path.2)).trans (add_assoc _ _ _).symm
  | .oracle _ next, roles, e₁, _, _, e₂, path =>
      Errors.along_append (next PUnit.unit) (roles.2 PUnit.unit) e₁ e₂ path.2

/-- Bounds add side by side. -/
theorem Errors.Bounded.append {t₁ : Oracle.TypeTree.{0}} {r₁ : t₁.RoleDecoration}
    {e₁ : Errors t₁ r₁} {c₁ : ℝ≥0} (h₁ : Errors.Bounded t₁ r₁ e₁ c₁) {t₂ : Oracle.TypeTree.{0}}
    {r₂ : t₂.RoleDecoration} {e₂ : Errors t₂ r₂} {c₂ : ℝ≥0} (h₂ : Errors.Bounded t₂ r₂ e₂ c₂) :
    Errors.Bounded _ _ (Errors.append t₁ r₁ e₁ e₂) (c₁ + c₂) :=
  fun path ↦ (Errors.along_append t₁ r₁ e₁ e₂ path).trans_le (add_le_add (h₁ _) (h₂ _))

/-- A prover on a tree, then, from its output, a prover on a second tree. -/
def proverAppend : (t₁ : Oracle.TypeTree.{0}) → (r₁ : t₁.RoleDecoration) → {A : Type} →
    Prover.Strategy unifSpec t₁ r₁ (fun _ ↦ A) → {t₂ : Oracle.TypeTree.{0}} →
    {r₂ : t₂.RoleDecoration} → {B : Type} → (A → Prover.Strategy unifSpec t₂ r₂ fun _ ↦ B) →
    Prover.Strategy unifSpec (PFunctor.FreeM.append t₁ fun _ ↦ t₂)
      (Decoration.append r₁ fun _ ↦ r₂) fun _ ↦ B
  | .done, _, _, p₁, _, _, _, p₂ => p₂ p₁
  | .public _ next, ⟨.sender, roles⟩, _, p₁, _, _, _, p₂ => do
      let x ← p₁
      return ⟨x.1, proverAppend (next x.1) (roles x.1) x.2 p₂⟩
  | .public _ next, ⟨.receiver, roles⟩, _, p₁, _, _, _, p₂ => fun move ↦ do
      let rest ← p₁ move
      return proverAppend (next move) (roles move) rest p₂
  | .oracle _ next, roles, _, p₁, _, _, _, p₂ => do
      let x ← p₁
      return ⟨x.1, proverAppend (next PUnit.unit) (roles.2 PUnit.unit) x.2 p₂⟩

/-! ## Honest runs in sequence -/

/-- **An honest run of the provers in sequence** is an honest run of the first to some output,
then an honest run of the second from it, on the two pieces of the path. -/
theorem runs_append : (t₁ : Oracle.TypeTree.{0}) → (r₁ : t₁.RoleDecoration) →
    (s₁ : Samplers t₁ r₁) → {A : Type} → (p₁ : Prover.Strategy unifSpec t₁ r₁ fun _ ↦ A) →
    {t₂ : Oracle.TypeTree.{0}} → {r₂ : t₂.RoleDecoration} → (s₂ : Samplers t₂ r₂) →
    {B : Type} → (p₂ : A → Prover.Strategy unifSpec t₂ r₂ fun _ ↦ B) →
    (path : ExecutionPath (PFunctor.FreeM.append t₁ fun _ ↦ t₂)) → (b : B) →
    Runs _ _ (Samplers.append t₁ r₁ s₁ s₂) (proverAppend t₁ r₁ p₁ p₂) path b →
    ∃ a, Runs t₁ r₁ s₁ p₁ (PFunctor.FreeM.PathAlong.split runtimeLens t₁ (fun _ ↦ t₂) path).1 a ∧
      Runs t₂ r₂ s₂ (p₂ a) (PFunctor.FreeM.PathAlong.split runtimeLens t₁ (fun _ ↦ t₂) path).2 b
  | .done, _, _, _, p₁, _, _, _, _, _, _, _, h => ⟨p₁, rfl, h⟩
  | .public _ next, ⟨.sender, roles⟩, s₁, _, p₁, _, _, s₂, _, p₂, path, b, ⟨rest, hrest, h⟩ => by
      obtain ⟨x, hx, hrest⟩ := (mem_support_bind_iff _ _ _).mp hrest
      have hrest := (mem_support_pure_iff _ _).mp hrest
      obtain ⟨m, rest₁⟩ := x
      obtain ⟨rfl, hrest⟩ := Sigma.mk.inj_iff.mp hrest
      obtain rfl := eq_of_heq hrest
      obtain ⟨a, h₁, h₂⟩ := runs_append (next path.1) (roles path.1) (s₁ path.1) rest₁ s₂ p₂
        path.2 b h
      exact ⟨a, ⟨rest₁, hx, h₁⟩, h₂⟩
  | .public _ next, ⟨.receiver, roles⟩, s₁, _, p₁, _, _, s₂, _, p₂, path, b,
      ⟨hc, rest, hrest, h⟩ => by
      obtain ⟨rest₁, hx, hrest⟩ := (mem_support_bind_iff _ _ _).mp hrest
      obtain rfl := (mem_support_pure_iff _ _).mp hrest
      obtain ⟨a, h₁, h₂⟩ := runs_append (next path.1) (roles path.1) (s₁.2 path.1) rest₁ s₂ p₂
        path.2 b h
      exact ⟨a, ⟨hc, rest₁, hx, h₁⟩, h₂⟩
  | .oracle _ next, roles, s₁, _, p₁, _, _, s₂, _, p₂, path, b, ⟨rest, hrest, h⟩ => by
      obtain ⟨x, hx, hrest⟩ := (mem_support_bind_iff _ _ _).mp hrest
      have hrest := (mem_support_pure_iff _ _).mp hrest
      obtain ⟨m, rest₁⟩ := x
      obtain ⟨rfl, hrest⟩ := Sigma.mk.inj_iff.mp hrest
      obtain rfl := eq_of_heq hrest
      obtain ⟨a, h₁, h₂⟩ := runs_append (next PUnit.unit) (roles.2 PUnit.unit) s₁ rest₁ s₂ p₂
        path.2 b h
      exact ⟨a, ⟨rest₁, hx, h₁⟩, h₂⟩

/-! ## Components in sequence -/

/-- Two slots in sequence. -/
abbrev Slot.append (σ₁ σ₂ : Slot) : Slot :=
  ⟨PFunctor.FreeM.append σ₁.tree fun _ ↦ σ₂.tree, Decoration.append σ₁.roles fun _ ↦ σ₂.roles,
    Decoration.append σ₁.oracles fun _ ↦ σ₂.oracles,
    Samplers.append σ₁.tree σ₁.roles σ₁.samplers σ₂.samplers⟩

variable {ι : Type} {O : ι → Type}

/-- **Two components in sequence**: the trees, decorations, samplers and provers appended, the
second verdict on the first, a rejection of either rejecting. -/
def Def.append {S₁ S₂ S₃ W₁ W₂ W₃ : Type} {σ₁ σ₂ : Slot} (D₁ : Def O S₁ W₁ S₂ W₂ σ₁)
    (D₂ : Def O S₂ W₂ S₃ W₃ σ₂) : Def O S₁ W₁ S₃ W₃ (σ₁.append σ₂) where
  verdict s p := (D₁.verdict s (PFunctor.FreeM.Path.split D₁.tree _ p).1).bind fun t ↦
    D₂.verdict t (PFunctor.FreeM.Path.split D₁.tree _ p).2
  prover so w := proverAppend D₁.tree D₁.roles (D₁.prover so w) fun x ↦ D₂.prover x.1 x.2

/-- The verdict in sequence on an execution path: the first verdict on its first piece, then the
second on its second piece. -/
theorem Def.append_verdict {S₁ S₂ S₃ W₁ W₂ W₃ : Type} {σ₁ σ₂ : Slot} (D₁ : Def O S₁ W₁ S₂ W₂ σ₁)
    (D₂ : Def O S₂ W₂ S₃ W₃ σ₂) (s : S₁) (path : (D₁.append D₂).tree.ExecutionPath) :
    (D₁.append D₂).verdict s path.toBranchPath =
      (D₁.verdict s (ExecutionPath.toBranchPath
        (PFunctor.FreeM.PathAlong.split runtimeLens D₁.tree _ path).1)).bind fun t ↦
        D₂.verdict t (ExecutionPath.toBranchPath
          (PFunctor.FreeM.PathAlong.split runtimeLens D₁.tree _ path).2) := by
  change (D₁.verdict s (PFunctor.FreeM.Path.split D₁.tree _ path.toBranchPath).1).bind
    (fun t ↦ D₂.verdict t (PFunctor.FreeM.Path.split D₁.tree _ path.toBranchPath).2) = _
  rw [show PFunctor.FreeM.Path.split D₁.tree (fun _ ↦ D₂.tree) path.toBranchPath = _ from
    ExecutionPath.toBranchPath_split D₁.tree (fun _ ↦ D₂.tree) path]

/-- **Completeness composes.** -/
theorem Complete.append {S₁ S₂ S₃ W₁ W₂ W₃ : Type} {σ₁ σ₂ : Slot} {D₁ : Def O S₁ W₁ S₂ W₂ σ₁}
    {D₂ : Def O S₂ W₂ S₃ W₃ σ₂} {rel₁ : Set ((S₁ × ∀ i, O i) × W₁)}
    {rel₂ : Set ((S₂ × ∀ i, O i) × W₂)} {rel₃ : Set ((S₃ × ∀ i, O i) × W₃)}
    (C₁ : Complete D₁ rel₁ rel₂) (C₂ : Complete D₂ rel₂ rel₃) :
    Complete (D₁.append D₂) rel₁ rel₃ := by
  intro s o w hin path c hruns
  obtain ⟨a, h₁, h₂⟩ := runs_append D₁.tree D₁.roles D₁.samplers (D₁.prover (s, o) w)
    D₂.samplers (fun x ↦ D₂.prover x.1 x.2) path c hruns
  obtain ⟨hv₁, ho₁, hmid⟩ := C₁ s o w hin _ a h₁
  obtain ⟨a₁, a₂⟩ := a
  obtain ⟨t, o'⟩ := a₁
  dsimp only at hv₁ ho₁ hmid h₂
  subst ho₁
  obtain ⟨hv₂, ho₂, hout⟩ := C₂ t o' a₂ hmid _ c h₂
  refine ⟨?_, ho₂, hout⟩
  rw [Def.append_verdict, hv₁, Option.bind_some, hv₂]

/-! ## Knowledge soundness in sequence -/

section Security

variable {S : Type} {W : Type}

/-- The knowledge state of a verdict: the witnesses that, with the oracles, put the accepted
statement in the relation. -/
abbrev verdictState (rel : Set ((S × ∀ i, O i) × W)) (o : ∀ i, O i) (v : Option S) :
    KnowledgeState.{0} :=
  KnowledgeState.ofProblem (outProblem O rel o) () v

/-- The backward maps of a false state: every state after it is false, and the witness is kept. -/
def falseExtractor : (tree : Oracle.TypeTree.{0}) → (P : W → Prop) → RoundExtractor tree ⟨W, P⟩
  | .done, _ => PUnit.unit
  | .public _ next, _ => fun move ↦ ⟨⟨W, fun _ ↦ False⟩, id, falseExtractor (next move) _⟩
  | .oracle _ next, _ => fun _ ↦ ⟨⟨W, fun _ ↦ False⟩, id, falseExtractor (next PUnit.unit) _⟩

/-- A false state's maps preserve knowledge: there is none after a move. -/
theorem falseExtractor_preserving : (tree : Oracle.TypeTree.{0}) → (P : W → Prop) →
    (roles : tree.RoleDecoration) → (falseExtractor tree P).IsProverPreserving roles
  | .done, _, _ => trivial
  | .public _ next, _, roles => ⟨fun _ _ _ h ↦ h.elim, fun move ↦
      falseExtractor_preserving (next move) _ (roles.2 move)⟩
  | .oracle _ next, _, roles => ⟨fun _ _ h ↦ h.elim, fun _ ↦
      falseExtractor_preserving (next PUnit.unit) _ (roles.2 PUnit.unit)⟩

/-- A false state's maps are bounded at any errors: no challenge makes knowledge appear. -/
theorem falseExtractor_bounded : (tree : Oracle.TypeTree.{0}) → (P : W → Prop) →
    (roles : tree.RoleDecoration) → (s : Samplers tree roles) → (e : Errors tree roles) →
    (falseExtractor tree P).IsLocallyBounded roles (schedule tree roles s e)
  | .done, _, _, _, _ => trivial
  | .public _ next, _, ⟨.sender, roles⟩, s, e => fun move ↦
      falseExtractor_bounded (next move) _ (roles move) (s move) (e move)
  | .public _ next, _, ⟨.receiver, roles⟩, s, e => by
      refine ⟨?_, fun move ↦ falseExtractor_bounded (next move) _ (roles move) (s.2 move)
        (e.2 move)⟩
      rw [_root_.RoundByRound.GameFamily.isBounded_iff]
      intro _ _
      refine le_trans (le_of_eq ((OracleComp.prEvent_eq_zero_iff _ _).mpr ?_)) zero_le
      rintro c - ⟨_, -, h⟩
      exact h
  | .oracle _ next, _, roles, s, e => fun _ ↦
      falseExtractor_bounded (next PUnit.unit) _ (roles.2 PUnit.unit) s e

/-- A false state's terminal witnesses are the witnesses. -/
theorem falseExtractor_terminal_witness : (tree : Oracle.TypeTree.{0}) → (P : W → Prop) →
    (path : tree.ExecutionPath) → ((falseExtractor tree P).terminalState path).Witness = W
  | .done, _, _ => rfl
  | .public _ next, _, path => falseExtractor_terminal_witness (next path.1) _ path.2
  | .oracle _ next, _, path => falseExtractor_terminal_witness (next PUnit.unit) _ path.2

/-- From a false state, no terminal state holds. -/
theorem falseExtractor_terminal_not : (tree : Oracle.TypeTree.{0}) → (P : W → Prop) →
    (∀ w, ¬ P w) → (path : tree.ExecutionPath) →
    (w : ((falseExtractor tree P).terminalState path).Witness) →
    ¬ ((falseExtractor tree P).terminalState path).holds w
  | .done, _, hP, _, w => hP w
  | .public _ next, _, _, path, w => falseExtractor_terminal_not (next path.1) _
      (fun _ h ↦ h) path.2 w
  | .oracle _ next, _, _, path, w => falseExtractor_terminal_not (next PUnit.unit) _
      (fun _ h ↦ h) path.2 w

/-- A terminal relation holds of any claim function equal to its own. -/
def terminalCongr {tree : Oracle.TypeTree.{0}} {state : KnowledgeState.{0}}
    {X : RoundExtractor tree state} {Context : Type} {family : ClaimFamily.{0, 0} Context}
    {P : Problem.{0, 0, 0} family} {context : tree.ExecutionPath → Context}
    {claim claim' : (path : tree.ExecutionPath) → family.Claim (context path)}
    (h : ∀ path, claim path = claim' path) (T : TerminalRelation X P context claim) :
    TerminalRelation X P context claim' :=
  (funext h : claim = claim') ▸ T

end Security

section SecurityAppend

variable {S₁ S₂ S₃ W : Type} {σ₁ σ₂ : Slot} {D₁ : Def O S₁ W S₂ W σ₁} {D₂ : Def O S₂ W S₃ W σ₂}
  {rel₁ : Set ((S₁ × ∀ i, O i) × W)} {rel₂ : Set ((S₂ × ∀ i, O i) × W)}
  {rel₃ : Set ((S₃ × ∀ i, O i) × W)} {e₁ : Errors D₁.tree D₁.roles} {e₂ : Errors D₂.tree D₂.roles}

/-- The second component's backward maps at a verdict of the first: its own at an accepted
statement, entered at the verdict's state; a false state's at a rejection. -/
def secondFor (X₂ : (t : S₂) → (o : ∀ i, O i) → RoundExtractor D₂.tree (inState O rel₂ t o))
    (o : ∀ i, O i) : (v : Option S₂) → RoundExtractor D₂.tree (verdictState rel₂ o v)
  | some t => (X₂ t o).changeInputState _ (Equiv.refl W)
  | none => falseExtractor D₂.tree _

/-- The verdict's state at an accepted statement is the input relation there. -/
theorem secondFor_compat (t : S₂) (o : ∀ i, O i) (w : W) :
    (verdictState rel₂ o (some t)).holds w ↔ (inState O rel₂ t o).holds (Equiv.refl W w) :=
  ⟨fun ⟨_, ht, h⟩ ↦ by cases ht; exact h, fun h ↦ ⟨t, rfl, h⟩⟩

/-- The second component's maps at a verdict preserve knowledge. -/
theorem secondFor_preserving (S₂' : Security D₂ rel₂ rel₃ e₂) (o : ∀ i, O i) :
    (v : Option S₂) → (secondFor S₂'.extractor o v).IsProverPreserving D₂.roles
  | some t => (S₂'.extractor t o).isProverPreserving_changeInputState
      (verdictState rel₂ o (some t)) (Equiv.refl W) (secondFor_compat t o) D₂.roles
      (S₂'.prover_preserving t o)
  | none => falseExtractor_preserving D₂.tree _ D₂.roles

/-- The second component's maps at a verdict are bounded at its errors. -/
theorem secondFor_bounded (S₂' : Security D₂ rel₂ rel₃ e₂) (o : ∀ i, O i) :
    (v : Option S₂) →
      (secondFor S₂'.extractor o v).IsLocallyBounded D₂.roles
        (schedule D₂.tree D₂.roles D₂.samplers e₂)
  | some t => (S₂'.extractor t o).isLocallyBounded_changeInputState
      (verdictState rel₂ o (some t)) (Equiv.refl W) (secondFor_compat t o) D₂.roles _
      (S₂'.local_bound t o)
  | none => falseExtractor_bounded D₂.tree _ D₂.roles D₂.samplers e₂

/-- The second component's terminal relation at a verdict of the first: the output relation at
its own verdict on the accepted statement, a rejection at a rejection. -/
def secondForTerminal
    (X₂ : (t : S₂) → (o : ∀ i, O i) → RoundExtractor D₂.tree (inState O rel₂ t o))
    (T₂ : ∀ t o, TerminalRelation (X₂ t o) (outProblem O rel₃ o) (fun _ ↦ ())
      fun path ↦ D₂.verdict t path.toBranchPath) (o : ∀ i, O i) :
    (v : Option S₂) → TerminalRelation (secondFor X₂ o v) (outProblem O rel₃ o)
      (fun _ ↦ ())
      fun rest ↦ v.bind fun t ↦ D₂.verdict t rest.toBranchPath
  | some t => (T₂ t o).changeInputState (verdictState rel₂ o (some t)) (Equiv.refl W)
      (secondFor_compat t o)
  | none =>
    { witnessEquiv := fun path ↦ Equiv.cast (falseExtractor_terminal_witness D₂.tree _ path)
      knowledge_iff := fun path w ↦ by
        refine iff_of_false (falseExtractor_terminal_not D₂.tree _
          (fun _ ⟨_, h, _⟩ ↦ nomatch h) path w) ?_
        rintro ⟨_, h, _⟩
        exact nomatch h }

/-- The backward maps in sequence: the first component's, then, at each of its paths, the second
component's at its verdict, entered at its terminal state. -/
def appendExtractor
    (X₁ : (s : S₁) → (o : ∀ i, O i) → RoundExtractor D₁.tree (inState O rel₁ s o))
    (T₁ : ∀ s o, TerminalRelation (X₁ s o) (outProblem O rel₂ o) (fun _ ↦ ())
      fun path ↦ D₁.verdict s path.toBranchPath)
    (X₂ : (t : S₂) → (o : ∀ i, O i) → RoundExtractor D₂.tree (inState O rel₂ t o)) (s : S₁)
    (o : ∀ i, O i) : RoundExtractor (D₁.append D₂).tree (inState O rel₁ s o) :=
  (X₁ s o).append (fun _ ↦ D₂.tree) fun path ↦
    (secondFor X₂ o (D₁.verdict s path.toBranchPath)).changeInputState _
      ((T₁ s o).witnessEquiv path)

/-- **Knowledge soundness composes**, at the errors side by side, with ArkLib's composition of
backward witness maps. Inlined before compilation, like `Security.mono`, so a composed security
computes. -/
@[macro_inline]
def Security.append (S₁' : Security D₁ rel₁ rel₂ e₁) (S₂' : Security D₂ rel₂ rel₃ e₂) :
    Security (D₁.append D₂) rel₁ rel₃ (Errors.append D₁.tree D₁.roles e₁ e₂) where
  extractor := appendExtractor S₁'.extractor S₁'.terminal S₂'.extractor
  prover_preserving s o := RoundExtractor.isProverPreserving_append _ _ _ D₁.roles
    (fun _ ↦ D₂.roles) (S₁'.prover_preserving s o) fun path ↦
      RoundExtractor.isProverPreserving_changeInputState _ _ _
        ((S₁'.terminal s o).knowledge_iff path) D₂.roles
        (secondFor_preserving S₂' o (D₁.verdict s path.toBranchPath))
  local_bound s o := by
    change RoundExtractor.IsLocallyBounded _ _
      (schedule _ _ (Samplers.append D₁.tree D₁.roles D₁.samplers D₂.samplers)
        (Errors.append D₁.tree D₁.roles e₁ e₂))
    rw [schedule_append]
    exact RoundExtractor.isLocallyBounded_append _ _ _ D₁.roles (fun _ ↦ D₂.roles) _ _
      (S₁'.local_bound s o) fun path ↦
        RoundExtractor.isLocallyBounded_changeInputState _ _ _
          ((S₁'.terminal s o).knowledge_iff path) D₂.roles _
          (secondFor_bounded S₂' o (D₁.verdict s path.toBranchPath))
  terminal s o := terminalCongr (fun full ↦ (Def.append_verdict D₁ D₂ s full).symm)
    (TerminalRelation.append (S₁'.extractor s o) (fun _ ↦ D₂.tree) _ (outProblem O rel₃ o)
      (fun _ _ ↦ ()) (fun path rest ↦ (D₁.verdict s path.toBranchPath).bind fun t ↦
        D₂.verdict t rest.toBranchPath) fun path ↦
          (secondForTerminal S₂'.extractor S₂'.terminal o
            (D₁.verdict s path.toBranchPath)).changeInputState _
            ((S₁'.terminal s o).witnessEquiv path) ((S₁'.terminal s o).knowledge_iff path))

end SecurityAppend

end
end LeanVM.Protocol.Typed
