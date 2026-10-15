import ArkLib.Interaction.CompositionSoundness
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.EvalDist.Measure
import VCVio.OracleComp.Constructions.SampleableType.Measure
import VCVio.EvalDist.ProbabilityBounds

/-!
# Phases of a public-coin protocol

A `Phase A B` is a piece of a public-coin interactive protocol on ArkLib's native two-party
interaction trees (`Interaction.TwoParty.run`): a type tree with its roles, the verifier's
counterpart strategy, which turns the verifier's state `A` into a state `B`, and the honest
prover's strategy, which predicts that state. Phases compose along `TypeTree.append`.

Soundness (`Phase.Sound`) is a truth transition: from a bad input state, every native prover
strategy, with arbitrary private memory and effects, makes the verifier's output good with
probability at most `ε`. Composition adds the errors, through ArkLib's
`Interaction.TwoParty.run_appendFlat_soundness`. Completeness (`Phase.Complete`) says that every
possible honest execution from a good input ends with prover and verifier in the same good state.
-/

open Interaction Interaction.TwoParty OracleComp OracleSpec
open scoped ENNReal

namespace KeccakGkr

/-- A prover strategy on a type tree. -/
abbrev Focal (tree : TypeTree) (roles : RoleDecoration tree)
    (Out : PFunctor.FreeM.Path tree → Type) :=
  StrategyOver (SyntaxOver.TwoParty.pairedTypeTree ProbComp) Participant.focal tree roles Out

/-- A verifier strategy on a type tree. -/
abbrev Counterpart (tree : TypeTree) (roles : RoleDecoration tree)
    (Out : PFunctor.FreeM.Path tree → Type) :=
  StrategyOver (SyntaxOver.TwoParty.pairedTypeTree ProbComp) Participant.counterpart tree roles Out

/-- A piece of a protocol: the verifier moves its state from `A` to `B`, and the honest prover
predicts it. -/
structure Phase (A B : Type) where
  tree : TypeTree
  roles : RoleDecoration tree
  verifier : A → Counterpart tree roles (fun _ => B)
  prover : A → Focal tree roles (fun _ => B)

namespace Phase

variable {A B C : Type}

/-- From a bad input, every prover makes the output good with probability at most `ε`. -/
def Sound (P : Phase A B) (Bad : A → Prop) (Good : B → Prop) (ε : ℝ≥0∞) : Prop :=
  ∀ a, Bad a → ∀ (OutP : PFunctor.FreeM.Path P.tree → Type) (prover : Focal P.tree P.roles OutP),
    Pr{let r ← run P.tree P.roles prover (P.verifier a)}[Good r.2.2] ≤ ε

/-- From a good input, every possible honest execution ends with the prover and the verifier in
the same good state. -/
def Complete (P : Phase A B) (Rel : A → Prop) (Rel' : B → Prop) : Prop :=
  ∀ a, Rel a → ∀ z ∈ support (run P.tree P.roles (P.prover a) (P.verifier a)),
    z.2.1 = z.2.2 ∧ Rel' z.2.2

theorem Sound.mono {P : Phase A B} {Bad Bad' : A → Prop} {Good Good' : B → Prop} {ε ε' : ℝ≥0∞}
    (h : P.Sound Bad Good ε) (hBad : ∀ a, Bad' a → Bad a) (hGood : ∀ b, Good' b → Good b)
    (hε : ε ≤ ε') : P.Sound Bad' Good' ε' := fun a ha OutP prover =>
  ((prEvent_mono _ _ _ fun _ hr => hGood _ hr).trans (h a (hBad a ha) OutP prover)).trans hε

theorem Complete.mono {P : Phase A B} {Rel Rel' : A → Prop} {Out Out' : B → Prop}
    (h : P.Complete Rel Out) (hRel : ∀ a, Rel' a → Rel a) (hOut : ∀ b, Out b → Out' b) :
    P.Complete Rel' Out' := fun a ha z hz =>
  let ⟨heq, hz'⟩ := h a (hRel a ha) z hz
  ⟨heq, hOut _ hz'⟩

/-! ## Sequential composition -/

/-- Compose prover strategies along `append` with a fixed second tree, with a pure continuation. -/
def focalComp {T : TypeTree} {rT : RoleDecoration T} {C : Type} :
    {s₁ : TypeTree} → {r₁ : RoleDecoration s₁} → {Mid : PFunctor.FreeM.Path s₁ → Type} →
    Focal s₁ r₁ Mid → ((t : PFunctor.FreeM.Path s₁) → Mid t → Focal T rT (fun _ => C)) →
      Focal (s₁.append fun _ => T) (r₁.append fun _ => rT) (fun _ => C)
  | .done, _, _, strat, f => f ⟨⟩ strat
  | .node _ _, ⟨.sender, _⟩, _, strat, f =>
      (fun xc => ⟨xc.1, focalComp xc.2 (fun t mid => f ⟨xc.1, t⟩ mid)⟩) <$> strat
  | .node _ _, ⟨.receiver, _⟩, _, strat, f =>
      fun x => (fun next => focalComp next (fun t mid => f ⟨x, t⟩ mid)) <$> strat x

theorem compFlat_pure {T : TypeTree} {rT : RoleDecoration T} {C : Type} :
    (s₁ : TypeTree) → (r₁ : RoleDecoration s₁) → {Mid : PFunctor.FreeM.Path s₁ → Type} →
    (strat : Focal s₁ r₁ Mid) → (f : (t : PFunctor.FreeM.Path s₁) → Mid t → Focal T rT (fun _ => C)) →
    StrategyOver.TwoParty.Focal.compFlat (s₂ := fun _ => T) (r₂ := fun _ => rT)
        (Output := fun _ => C) strat (fun t mid => pure (f t mid)) =
      (pure (focalComp strat f) : ProbComp _)
  | .done, _, _, _, _ => rfl
  | .node X rest, ⟨.sender, rRest⟩, _, strat, f => by
      simp only [StrategyOver.TwoParty.Focal.compFlat, focalComp]
      congr 1
      rw [map_eq_bind_pure_comp]
      refine bind_congr fun xc => ?_
      rw [compFlat_pure (rest xc.1) (rRest xc.1) xc.2 (fun t mid => f ⟨xc.1, t⟩ mid)]
      simp
  | .node X rest, ⟨.receiver, rRest⟩, _, strat, f => by
      simp only [StrategyOver.TwoParty.Focal.compFlat, focalComp]
      congr 1
      funext x
      rw [map_eq_bind_pure_comp]
      refine bind_congr fun next => ?_
      rw [compFlat_pure (rest x) (rRest x) next (fun t mid => f ⟨x, t⟩ mid)]
      rfl

/-- Run the first phase, then the second from the verifier's state. -/
def comp (P₁ : Phase A B) (P₂ : Phase B C) : Phase A C where
  tree := P₁.tree.append (fun _ => P₂.tree)
  roles := P₁.roles.append (fun _ => P₂.roles)
  verifier a :=
    StrategyOver.TwoParty.Counterpart.appendFlat (Output₂ := fun _ => C) (P₁.verifier a)
      (fun _ b => P₂.verifier b)
  prover a := focalComp (P₁.prover a) (fun _ b => P₂.prover b)

theorem Sound.comp {P₁ : Phase A B} {P₂ : Phase B C} {Bad : A → Prop} {Mid : B → Prop}
    {Good : C → Prop} {ε₁ ε₂ : ℝ≥0∞} (h₁ : P₁.Sound Bad Mid ε₁)
    (h₂ : P₂.Sound (fun b => ¬ Mid b) Good ε₂) : (P₁.comp P₂).Sound Bad Good (ε₁ + ε₂) := by
  intro a ha OutP prover
  exact run_appendFlat_soundness (OutputC := fun _ => C) prover (P₁.verifier a)
    (fun _ b => P₂.verifier b) (fun _ b => Mid b) (fun _ c => Good c) ε₁ ε₂
    (fun strategy => h₁ a ha _ strategy)
    (fun _ b hb strategy => h₂ b hb _ strategy)

theorem run_comp (P₁ : Phase A B) (P₂ : Phase B C) (a : A) :
    run (P₁.comp P₂).tree (P₁.comp P₂).roles ((P₁.comp P₂).prover a) ((P₁.comp P₂).verifier a) =
      (do
        let ⟨t₁, mid, out₁⟩ ← run P₁.tree P₁.roles (P₁.prover a) (P₁.verifier a)
        let ⟨t₂, outP, outC⟩ ← run P₂.tree P₂.roles (P₂.prover mid) (P₂.verifier out₁)
        pure ⟨PFunctor.FreeM.Path.append P₁.tree (fun _ => P₂.tree) t₁ t₂, outP, outC⟩) := by
  have h := run_compFlat_appendFlat_pure (OutputP := fun _ => C) (OutputC := fun _ => C)
    (P₁.prover a) (fun _ b => P₂.prover b) (P₁.verifier a) (fun _ b => P₂.verifier b)
  rw [compFlat_pure, pure_bind] at h
  exact h

theorem Complete.comp {P₁ : Phase A B} {P₂ : Phase B C} {Rel : A → Prop} {Mid : B → Prop}
    {Rel' : C → Prop} (h₁ : P₁.Complete Rel Mid) (h₂ : P₂.Complete Mid Rel') :
    (P₁.comp P₂).Complete Rel Rel' := by
  intro a ha z hz
  rw [run_comp, mem_support_bind_iff] at hz
  obtain ⟨⟨t₁, mid, out₁⟩, hz₁, hz⟩ := hz
  rw [mem_support_bind_iff] at hz
  obtain ⟨⟨t₂, outP, outC⟩, hz₂, hz⟩ := hz
  obtain ⟨heq, hmid⟩ := h₁ a ha _ hz₁
  simp only at heq hmid
  subst heq
  obtain ⟨heq', hrel⟩ := h₂ mid hmid _ hz₂
  rw [mem_support_pure_iff] at hz
  subst hz
  exact ⟨heq', hrel⟩

/-! ## Post-processing the state -/

/-- Apply a function to the output state. -/
def map (P : Phase A B) (g : B → C) : Phase A C where
  tree := P.tree
  roles := P.roles
  verifier a := StrategyOver.TwoParty.Counterpart.mapOutput (fun _ => g) (P.verifier a)
  prover a := StrategyOver.TwoParty.Focal.mapOutput (fun _ => g) (P.prover a)

theorem run_map_verifier (P : Phase A B) (g : B → C) (a : A) {OutP : PFunctor.FreeM.Path P.tree → Type}
    (prover : Focal P.tree P.roles OutP) :
    run P.tree P.roles prover ((P.map g).verifier a) =
      (fun z => ⟨z.1, z.2.1, g z.2.2⟩) <$> run P.tree P.roles prover (P.verifier a) := by
  have h := run_mapOutput_mapOutput (fun _ x => x) (fun _ => g) prover (P.verifier a)
  rw [StrategyOver.TwoParty.Focal.mapOutput_id] at h
  exact h

theorem Sound.map {P : Phase A B} {g : B → C} {Bad : A → Prop} {Good : C → Prop} {ε : ℝ≥0∞}
    (h : P.Sound Bad (fun b => Good (g b)) ε) : (P.map g).Sound Bad Good ε := by
  intro a ha OutP prover
  have e := run_map_verifier P g a prover
  calc _ = Pr{let r ← run P.tree P.roles prover ((P.map g).verifier a)}[Good r.2.2] := rfl
    _ = _ := by rw [e, prEvent_map]
    _ ≤ ε := h a ha OutP prover

theorem Complete.map {P : Phase A B} {g : B → C} {Rel : A → Prop} {Rel' : C → Prop}
    (h : P.Complete Rel (fun b => Rel' (g b))) : (P.map g).Complete Rel Rel' := by
  intro a ha z hz
  change z ∈ support (run P.tree P.roles
    (StrategyOver.TwoParty.Focal.mapOutput (fun _ => g) (P.prover a))
    (StrategyOver.TwoParty.Counterpart.mapOutput (fun _ => g) (P.verifier a))) at hz
  rw [run_mapOutput_mapOutput, support_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  obtain ⟨heq, hrel⟩ := h a ha y hy
  exact ⟨congrArg g heq, hrel⟩

/-! ## The three kinds of node -/

/-- No interaction: the verifier computes its next state. -/
def compute (g : A → B) : Phase A B where
  tree := .done
  roles := PUnit.unit
  verifier a := g a
  prover a := g a

theorem compute_sound {g : A → B} {Bad : A → Prop} {Good : B → Prop}
    (h : ∀ a, Bad a → ¬ Good (g a)) : (compute g).Sound Bad Good 0 := by
  intro a ha OutP prover
  refine le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz => ?_)
  change z ∈ support (Pure.pure ⟨⟨⟩, prover, g a⟩ : ProbComp _) at hz
  rw [support_pure] at hz
  subst hz
  exact h a ha

theorem compute_complete {g : A → B} {Rel : A → Prop} {Rel' : B → Prop}
    (h : ∀ a, Rel a → Rel' (g a)) : (compute g).Complete Rel Rel' := by
  intro a ha z hz
  change z ∈ support (Pure.pure ⟨⟨⟩, g a, g a⟩ : ProbComp _) at hz
  rw [support_pure] at hz
  subst hz
  exact ⟨rfl, h a ha⟩

/-- The prover sends a message, which the verifier folds into its state. The honest prover sends
`honest a`. -/
def receive (Msg : Type) (f : A → Msg → B) (honest : A → Msg) : Phase A B where
  tree := .node Msg fun _ => .done
  roles := ⟨.sender, fun _ => PUnit.unit⟩
  verifier a := fun msg => pure (f a msg)
  prover a := pure ⟨honest a, f a (honest a)⟩

/-- The verifier samples a uniform challenge and folds it into its state. -/
def sample (Ch : Type) [SampleableType Ch] (f : A → Ch → B) : Phase A B where
  tree := .node Ch fun _ => .done
  roles := ⟨.receiver, fun _ => PUnit.unit⟩
  verifier a := do
    let x ← $ᵗ Ch
    pure ⟨x, f a x⟩
  prover a := fun x => pure (f a x)

theorem receive_sound {Msg : Type} {f : A → Msg → B} {honest : A → Msg} {Bad : A → Prop}
    {Good : B → Prop} (h : ∀ a, Bad a → ∀ msg, ¬ Good (f a msg)) :
    (receive Msg f honest).Sound Bad Good 0 := by
  intro a ha OutP prover
  simp only [receive]
  dsimp only [run, InteractionOver.runTypeTree, InteractionOver.TwoParty.pairedTypeTree,
    InteractionOver.TwoParty.paired, participantProfile, collectParticipantOutputs]
  simp only [pure_bind]
  refine prEvent_bind_le_of_forall_le _ _ _ fun xc => ?_
  simp [h a ha]

theorem sample_sound {Ch : Type} [SampleableType Ch] {f : A → Ch → B} {Bad : A → Prop}
    {Good : B → Prop} {ε : ℝ≥0∞}
    (h : ∀ a, Bad a → Pr{let x ← $ᵗ Ch}[Good (f a x)] ≤ ε) :
    (sample Ch f).Sound Bad Good ε := by
  intro a ha OutP prover
  simp only [sample]
  dsimp only [run, InteractionOver.runTypeTree, InteractionOver.TwoParty.pairedTypeTree,
    InteractionOver.TwoParty.paired, participantProfile, collectParticipantOutputs]
  simp only [bind_assoc, pure_bind]
  refine (prEvent_bind_le_prEvent_of_forall_eq_zero _ _ (fun x => Good (f a x)) _
    fun x hx => le_antisymm ?_ zero_le).trans (h a ha)
  refine prEvent_bind_le_of_forall_le _ _ _ fun _ => ?_
  simp [hx]

theorem receive_complete {Msg : Type} {f : A → Msg → B} {honest : A → Msg} {Rel : A → Prop}
    {Rel' : B → Prop} (h : ∀ a, Rel a → Rel' (f a (honest a))) :
    (receive Msg f honest).Complete Rel Rel' := by
  intro a ha z hz
  simp only [receive] at hz
  dsimp only [run, InteractionOver.runTypeTree, InteractionOver.TwoParty.pairedTypeTree,
    InteractionOver.TwoParty.paired, participantProfile, collectParticipantOutputs] at hz
  simp only [pure_bind, support_pure] at hz
  subst hz
  exact ⟨rfl, h a ha⟩

theorem sample_complete {Ch : Type} [SampleableType Ch] {f : A → Ch → B} {Rel : A → Prop}
    {Rel' : B → Prop} (h : ∀ a, Rel a → ∀ x, Rel' (f a x)) :
    (sample Ch f).Complete Rel Rel' := by
  intro a ha z hz
  have e : run (sample Ch f).tree (sample Ch f).roles ((sample Ch f).prover a)
      ((sample Ch f).verifier a) =
        (do let x ← $ᵗ Ch; pure ⟨⟨x, PUnit.unit⟩, (f a x, f a x)⟩) := by
    simp only [sample]
    dsimp only [run, InteractionOver.runTypeTree, InteractionOver.TwoParty.pairedTypeTree,
      InteractionOver.TwoParty.paired, participantProfile, collectParticipantOutputs]
    simp only [bind_assoc, pure_bind]
  rw [e, mem_support_bind_iff] at hz
  obtain ⟨x, -, hz⟩ := hz
  rw [support_pure] at hz
  subst hz
  exact ⟨rfl, h a ha x⟩

end Phase

end KeccakGkr
