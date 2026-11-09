/-
  LeanVM.Protocol.ToArkLib.Typed.Front

  Front verifiers on ArkLib's typed interaction trees: the verifier that samples a fresh
  challenge at each of its nodes, reads the prover's moves, never queries an oracle, and returns
  a verdict of the path. Its challenge marginals. Candidate for ArkLib.
-/

module

public import ArkLib.Interaction.Oracle.Security.KnowledgeComposition

/-!
# Front verifiers

A verifier is *front* when it decides from the statement and the moves alone: it samples a
challenge at each of its own nodes, reads the prover's moves, makes no oracle query, and at the
leaf returns a verdict of the branch path. Every verifier of leanVM's oracle protocol before the
opening has this shape.

* `Samplers tree roles`: a sampler at each verifier node, constant across oracle messages (the
  verifier cannot see them);
* `Errors tree roles`: an error at each verifier node, with `Errors.along` their sum along a path
  and `Errors.Bounded` a bound on it over every path;
* `schedule`: the two as the `RoundExtractor.ChallengeSchedule` a knowledge certificate carries;
* `frontFragment samplers leaf`: the verifier fragment that samples with `samplers` and returns
  `leaf` of the branch path, with `samplesChallenges_frontFragment`: it draws exactly the
  schedule's challenges, whatever the errors, the input oracles and their handler.

The ambient oracle is `unifSpec`, so the verifier's effects are probabilistic computations.
-/

namespace LeanVM.Protocol.Typed

open Interaction Interaction.TwoParty Interaction.Oracle Interaction.Oracle.Security
open OracleComp OracleSpec
open scoped NNReal ENNReal

@[expose] public section

/-! ## Samplers and errors -/

/-- A sampler at each verifier node of a tree. An oracle message cannot select the next sampler:
the verifier never sees its payload. -/
def Samplers : (tree : Oracle.TypeTree.{0}) → tree.RoleDecoration → Type
  | .done, _ => PUnit
  | .public Moves next, ⟨.sender, roles⟩ => (move : Moves) → Samplers (next move) (roles move)
  | .public Moves next, ⟨.receiver, roles⟩ =>
      ProbComp Moves × ((move : Moves) → Samplers (next move) (roles move))
  | .oracle _ next, roles => Samplers (next PUnit.unit) (roles.2 PUnit.unit)

/-- An error at each verifier node of a tree. -/
def Errors : (tree : Oracle.TypeTree.{0}) → tree.RoleDecoration → Type
  | .done, _ => PUnit
  | .public Moves next, ⟨.sender, roles⟩ => (move : Moves) → Errors (next move) (roles move)
  | .public Moves next, ⟨.receiver, roles⟩ =>
      ℝ≥0 × ((move : Moves) → Errors (next move) (roles move))
  | .oracle _ next, roles => Errors (next PUnit.unit) (roles.2 PUnit.unit)

/-- Errors pointwise at most others. -/
def Errors.Le : (tree : Oracle.TypeTree.{0}) → (roles : tree.RoleDecoration) →
    Errors tree roles → Errors tree roles → Prop
  | .done, _, _, _ => True
  | .public _ next, ⟨.sender, roles⟩, e, e' =>
      ∀ move, Errors.Le (next move) (roles move) (e move) (e' move)
  | .public _ next, ⟨.receiver, roles⟩, e, e' =>
      e.1 ≤ e'.1 ∧ ∀ move, Errors.Le (next move) (roles move) (e.2 move) (e'.2 move)
  | .oracle _ next, roles, e, e' => Errors.Le (next PUnit.unit) (roles.2 PUnit.unit) e e'

/-- Errors are at most themselves. -/
theorem Errors.Le.refl : (tree : Oracle.TypeTree.{0}) → (roles : tree.RoleDecoration) →
    (e : Errors tree roles) → Errors.Le tree roles e e
  | .done, _, _ => trivial
  | .public _ next, ⟨.sender, roles⟩, e => fun move ↦ Errors.Le.refl (next move) (roles move) (e move)
  | .public _ next, ⟨.receiver, roles⟩, e =>
      ⟨le_rfl, fun move ↦ Errors.Le.refl (next move) (roles move) (e.2 move)⟩
  | .oracle _ next, roles, e => Errors.Le.refl (next PUnit.unit) (roles.2 PUnit.unit) e

/-- Equal errors are at most one another. -/
theorem Errors.Le.of_eq {tree : Oracle.TypeTree.{0}} {roles : tree.RoleDecoration}
    {e e' : Errors tree roles} (h : e = e') : Errors.Le tree roles e e' :=
  h ▸ Errors.Le.refl tree roles e

/-- The errors along a branch path, summed: the total error charged to the challenges a run along
the path draws. -/
def Errors.along : (tree : Oracle.TypeTree.{0}) → (roles : tree.RoleDecoration) →
    Errors tree roles → tree.BranchPath → ℝ≥0
  | .done, _, _, _ => 0
  | .public _ next, ⟨.sender, roles⟩, e, path =>
      Errors.along (next path.1) (roles path.1) (e path.1) path.2
  | .public _ next, ⟨.receiver, roles⟩, e, path =>
      e.1 + Errors.along (next path.1) (roles path.1) (e.2 path.1) path.2
  | .oracle _ next, roles, e, path => Errors.along (next PUnit.unit) (roles.2 PUnit.unit) e path.2

/-- Errors whose sum along every branch path is at most `c`. -/
def Errors.Bounded (tree : Oracle.TypeTree.{0}) (roles : tree.RoleDecoration)
    (e : Errors tree roles) (c : ℝ≥0) : Prop :=
  ∀ path, Errors.along tree roles e path ≤ c

/-- A bound is a bound at anything larger. -/
theorem Errors.Bounded.mono {tree : Oracle.TypeTree.{0}} {roles : tree.RoleDecoration}
    {e : Errors tree roles} {c c' : ℝ≥0} (h : Errors.Bounded tree roles e c) (hc : c ≤ c') :
    Errors.Bounded tree roles e c' :=
  fun path ↦ (h path).trans hc

/-- The samplers and the errors as a knowledge certificate's challenge schedule. -/
def schedule : (tree : Oracle.TypeTree.{0}) → (roles : tree.RoleDecoration) →
    Samplers tree roles → Errors tree roles → RoundExtractor.ChallengeSchedule tree roles
  | .done, _, _, _ => PUnit.unit
  | .public _ next, ⟨.sender, roles⟩, s, e =>
      ⟨PUnit.unit, fun move => schedule (next move) (roles move) (s move) (e move)⟩
  | .public _ next, ⟨.receiver, roles⟩, s, e =>
      ⟨(s.1, (e.1 : ℝ≥0∞)), fun move => schedule (next move) (roles move) (s.2 move) (e.2 move)⟩
  | .oracle _ next, roles, s, e =>
      fun _ => schedule (next PUnit.unit) (roles.2 PUnit.unit) s e

/-- A slot: a tree of public moves and oracle messages, who moves at each public node, the oracle
interface of each oracle message, and the challenge samplers. The schedule a component runs at. -/
structure Slot where
  /-- The interaction tree. -/
  tree : Oracle.TypeTree.{0}
  /-- Who moves at each public node. -/
  roles : tree.RoleDecoration
  /-- The oracle interface of each oracle message. -/
  oracles : tree.OracleDecoration
  /-- The challenge samplers. -/
  samplers : Samplers tree roles

/-! ## The front verifier -/

/-- The front verifier fragment: samples with `samplers` at its nodes, reads the prover's moves
and returns `leaf` of the branch path, querying nothing. -/
def frontFragment : (tree : Oracle.TypeTree.{0}) → (roles : tree.RoleDecoration) →
    (oracles : tree.OracleDecoration) → (initial : PFunctor) → Samplers tree roles →
    {Leaf : tree.BranchPath → Type} → ((path : tree.BranchPath) → Leaf path) →
    Verifier.Fragment unifSpec tree roles oracles initial Leaf
  | .done, _, _, _, _, _, leaf => leaf PUnit.unit
  | .public _ next, ⟨.sender, roles⟩, oracles, initial, s, _, leaf => fun move =>
      pure (frontFragment (next move) (roles move) (oracles.2 move) initial (s move)
        (fun path => leaf ⟨move, path⟩))
  | .public _ next, ⟨.receiver, roles⟩, oracles, initial, s, _, leaf => do
      let move ← OracleComp.liftComp s.1 (unifSpec + OracleSpec.ofPFunctor initial)
      return ⟨move, frontFragment (next move) (roles move) (oracles.2 move) initial (s.2 move)
        (fun path => leaf ⟨move, path⟩)⟩
  | .oracle _ next, roles, oracles, initial, s, _, leaf =>
      pure (frontFragment (next PUnit.unit) (roles.2 PUnit.unit) (oracles.2 PUnit.unit)
        (Access.extend initial oracles.1) s (fun path => leaf ⟨PUnit.unit, path⟩))

/-- The front verifier: the front fragment whose leaf returns its verdict without a query. -/
def frontVerifier (tree : Oracle.TypeTree.{0}) (roles : tree.RoleDecoration)
    (oracles : tree.OracleDecoration) (initial : PFunctor) (s : Samplers tree roles)
    {Out : tree.BranchPath → Type} (verdict : (path : tree.BranchPath) → Out path) :
    Verifier.Strategy unifSpec tree roles oracles initial Out :=
  frontFragment tree roles oracles initial s (fun path ↦ pure (verdict path))

/-- Running a lifted sampler against any handler of the input oracles is the sampler. -/
theorem simulateQ_liftComp_sampler {initial : PFunctor}
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) {α : Type} (sampler : ProbComp α) :
    simulateQ (QueryImpl.id' unifSpec)
      (simulateQ (Verifier.liftAccessImpl unifSpec initial impl)
        (OracleComp.liftComp sampler (unifSpec + OracleSpec.ofPFunctor initial))) = sampler := by
  rw [QueryImpl.simulateQ_liftComp_left_eq_of_apply _ (QueryImpl.id' unifSpec) (fun _ ↦ rfl),
    simulateQ_id', simulateQ_id']

/-- Running a lifted sampler against any handler of the input oracles, before the ambient
handler, is the sampler. -/
theorem simulateQ_liftComp_sampler' {initial : PFunctor}
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) {α : Type} (sampler : ProbComp α) :
    simulateQ (Verifier.liftAccessImpl unifSpec initial impl)
      (OracleComp.liftComp sampler (unifSpec + OracleSpec.ofPFunctor initial)) = sampler := by
  rw [QueryImpl.simulateQ_liftComp_left_eq_of_apply _ (QueryImpl.id' unifSpec) (fun _ ↦ rfl),
    simulateQ_id']

/-- **The front verifier draws the schedule's challenges**: at each of its nodes, the challenge
it draws has exactly the sampler's law, whatever the errors, the input oracles and their
handler. -/
theorem samplesChallenges_frontFragment : (tree : Oracle.TypeTree.{0}) →
    (roles : tree.RoleDecoration) → (oracles : tree.OracleDecoration) → (initial : PFunctor) →
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) → (s : Samplers tree roles) →
    (e : Errors tree roles) → {Leaf : tree.BranchPath → Type} →
    (leaf : (path : tree.BranchPath) → Leaf path) →
    SamplesChallenges unifSpec (QueryImpl.id' unifSpec) tree roles oracles initial impl Leaf
      (frontFragment tree roles oracles initial s leaf) (schedule tree roles s e)
  | .done, _, _, _, _, _, _, _, _ => trivial
  | .public _ next, ⟨.sender, roles⟩, oracles, initial, impl, s, e, _, leaf => by
      intro move after hafter
      simp only [frontFragment, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hafter
      subst hafter
      exact samplesChallenges_frontFragment (next move) (roles move) (oracles.2 move) initial
        impl (s move) (e move) (fun path ↦ leaf ⟨move, path⟩)
  | .public _ next, ⟨.receiver, roles⟩, oracles, initial, impl, s, e, _, leaf => by
      refine ⟨fun event ↦ ?_, fun chosen hchosen ↦ ?_⟩
      · simp only [frontFragment, bind_pure_comp, simulateQ_map, simulateQ_liftComp_sampler,
          prEvent_map]
        rfl
      · simp only [frontFragment, bind_pure_comp, simulateQ_map, simulateQ_liftComp_sampler,
          support_map, Set.mem_image] at hchosen
        obtain ⟨move, -, rfl⟩ := hchosen
        exact samplesChallenges_frontFragment (next move) (roles move) (oracles.2 move) initial
          impl (s.2 move) (e.2 move) (fun path ↦ leaf ⟨move, path⟩)
  | .oracle _ next, roles, oracles, initial, impl, s, e, _, leaf => by
      intro message after hafter
      simp only [frontFragment, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hafter
      subst hafter
      exact samplesChallenges_frontFragment (next PUnit.unit) (roles.2 PUnit.unit)
        (oracles.2 PUnit.unit) (Access.extend initial oracles.1)
        (Access.extendImpl initial oracles.1 impl message) s e
        (fun path ↦ leaf ⟨PUnit.unit, path⟩)

/-! ## Honest runs -/

attribute [local implicit_reducible] Interaction.Oracle.TypeTree.runtimeLens

/-- The honest runs of a prover against fresh challenges from the samplers: the execution paths it
reaches, with its output at each. -/
def Runs : (tree : Oracle.TypeTree.{0}) → (roles : tree.RoleDecoration) → Samplers tree roles →
    {A : Type} → Prover.Strategy unifSpec tree roles (fun _ ↦ A) → tree.ExecutionPath → A → Prop
  | .done, _, _, _, p, _, a => a = p
  | .public _ next, ⟨.sender, roles⟩, s, _, p, path, a =>
      ∃ rest, Sigma.mk path.1 rest ∈ support p ∧
        Runs (next path.1) (roles path.1) (s path.1) rest path.2 a
  | .public _ next, ⟨.receiver, roles⟩, s, _, p, path, a =>
      path.1 ∈ support s.1 ∧ ∃ rest ∈ support (p path.1),
        Runs (next path.1) (roles path.1) (s.2 path.1) rest path.2 a
  | .oracle _ next, roles, s, _, p, path, a =>
      ∃ rest, Sigma.mk path.1 rest ∈ support p ∧
        Runs (next PUnit.unit) (roles.2 PUnit.unit) s rest path.2 a

/-! ## Querying the earlier oracles at the leaf -/

/-- The handler of the oracles available after an execution path: the prior handler, extended at
each oracle message on the path by that message's answers. -/
def implAfter : (tree : Oracle.TypeTree.{0}) → (oracles : tree.OracleDecoration) →
    (initial : PFunctor) → QueryImpl (OracleSpec.ofPFunctor initial) Id →
    (path : tree.ExecutionPath) →
    QueryImpl (OracleSpec.ofPFunctor (TypeTree.accessAfter tree oracles initial path.toBranchPath)) Id
  | .done, _, _, impl, _ => impl
  | .public _ next, oracles, initial, impl, path =>
      implAfter (next path.1) (oracles.2 path.1) initial impl path.2
  | .oracle _ next, oracles, initial, impl, path =>
      implAfter (next PUnit.unit) (oracles.2 PUnit.unit) (Access.extend initial oracles.1)
        (Access.extendImpl initial oracles.1 impl path.1) path.2

/-- A query to the oracles available before a tree, asked at the leaf of a path through it:
routed past each oracle message on the path. -/
def priorQuery : (tree : Oracle.TypeTree.{0}) → (oracles : tree.OracleDecoration) →
    (access : PFunctor) → (path : tree.BranchPath) → (q : access.A) →
    OracleComp (unifSpec + OracleSpec.ofPFunctor (TypeTree.accessAfter tree oracles access path))
      (access.B q)
  | .done, _, access, _, q =>
      (liftM ((unifSpec + OracleSpec.ofPFunctor access).query (.inr q)) :
        OracleComp (unifSpec + OracleSpec.ofPFunctor access) _)
  | .public _ next, oracles, access, path, q =>
      priorQuery (next path.1) (oracles.2 path.1) access path.2 q
  | .oracle _ next, oracles, access, path, q =>
      priorQuery (next PUnit.unit) (oracles.2 PUnit.unit) (Access.extend access oracles.1) path.2
        (.inl q)

/-- **A prior query is answered by the prior handler**, whatever oracle messages the path sends. -/
theorem simulateQ_priorQuery : (tree : Oracle.TypeTree.{0}) → (oracles : tree.OracleDecoration) →
    (access : PFunctor) → (impl : QueryImpl (OracleSpec.ofPFunctor access) Id) →
    (path : tree.ExecutionPath) → (q : access.A) →
    simulateQ (Verifier.liftAccessImpl unifSpec _ (implAfter tree oracles access impl path))
      (priorQuery tree oracles access path.toBranchPath q) = pure (impl q)
  | .done, _, _, _, _, _ => simulateQ_spec_query _ _
  | .public _ next, oracles, access, impl, path, q =>
      simulateQ_priorQuery (next path.1) (oracles.2 path.1) access impl path.2 q
  | .oracle _ next, oracles, access, impl, path, q =>
      simulateQ_priorQuery (next PUnit.unit) (oracles.2 PUnit.unit)
        (Access.extend access oracles.1) (Access.extendImpl access oracles.1 impl path.1) path.2
        (.inl q)

/-- **Every outcome of an execution against a front fragment is an honest run**, with an output
of the fragment's leaf at its path, run against the handler after the path. -/
theorem runs_of_mem_support_leaf : (tree : Oracle.TypeTree.{0}) → (roles : tree.RoleDecoration) →
    (oracles : tree.OracleDecoration) → (initial : PFunctor) →
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) → (s : Samplers tree roles) →
    {A : Type} → (p : Prover.Strategy unifSpec tree roles fun _ ↦ A) →
    {Out : tree.BranchPath → Type} →
    (leaf : (path : tree.BranchPath) → OracleComp (unifSpec +
      OracleSpec.ofPFunctor (TypeTree.accessAfter tree oracles initial path)) (Out path)) →
    ∀ x ∈ support (executeStrategies unifSpec tree roles oracles initial impl p
      (frontFragment tree roles oracles initial s leaf)),
      Runs tree roles s p x.1 x.2.1 ∧ x.2.2 ∈ support (simulateQ
        (Verifier.liftAccessImpl unifSpec _ (implAfter tree oracles initial impl x.1))
        (leaf x.1.toBranchPath))
  | .done, ⟨⟩, ⟨⟩, initial, impl, _, _, p, _, leaf, x, hx => by
      rw [executeStrategies_done] at hx
      obtain ⟨out, hout, hx⟩ := (mem_support_bind_iff _ _ _).mp hx
      rw [support_pure, Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨rfl, hout⟩
  | .public _ next, ⟨.sender, roles⟩, oracles, initial, impl, s, _, p, _, leaf, x, hx => by
      rw [executeStrategies_public_sender] at hx
      obtain ⟨chosen, hchosen, hx⟩ := (mem_support_bind_iff _ _ _).mp hx
      obtain ⟨after, hafter, hx⟩ := (mem_support_bind_iff _ _ _).mp hx
      simp only [frontFragment, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hafter
      subst hafter
      obtain ⟨result, hresult, hx⟩ := (mem_support_bind_iff _ _ _).mp hx
      rw [support_pure, Set.mem_singleton_iff] at hx
      subst hx
      obtain ⟨hruns, hleaf⟩ := runs_of_mem_support_leaf (next chosen.1) (roles chosen.1)
        (oracles.2 chosen.1) initial impl (s chosen.1) chosen.2
        (fun path ↦ leaf ⟨chosen.1, path⟩) result hresult
      exact ⟨⟨chosen.2, hchosen, hruns⟩, hleaf⟩
  | .public _ next, ⟨.receiver, roles⟩, oracles, initial, impl, s, _, p, _, leaf, x, hx => by
      rw [executeStrategies_public_receiver] at hx
      obtain ⟨chosen, hchosen, hx⟩ := (mem_support_bind_iff _ _ _).mp hx
      simp only [frontFragment, simulateQ_bind, simulateQ_pure,
        simulateQ_liftComp_sampler', mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hchosen
      obtain ⟨c, hc, rfl⟩ := hchosen
      obtain ⟨rest, hrest, hx⟩ := (mem_support_bind_iff _ _ _).mp hx
      obtain ⟨result, hresult, hx⟩ := (mem_support_bind_iff _ _ _).mp hx
      rw [support_pure, Set.mem_singleton_iff] at hx
      subst hx
      obtain ⟨hruns, hleaf⟩ := runs_of_mem_support_leaf (next c) (roles c) (oracles.2 c) initial
        impl (s.2 c) rest (fun path ↦ leaf ⟨c, path⟩) result hresult
      exact ⟨⟨hc, rest, hrest, hruns⟩, hleaf⟩
  | .oracle _ next, roles, oracles, initial, impl, s, _, p, _, leaf, x, hx => by
      rw [executeStrategies_oracle] at hx
      obtain ⟨chosen, hchosen, hx⟩ := (mem_support_bind_iff _ _ _).mp hx
      obtain ⟨after, hafter, hx⟩ := (mem_support_bind_iff _ _ _).mp hx
      simp only [frontFragment, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hafter
      subst hafter
      obtain ⟨result, hresult, hx⟩ := (mem_support_bind_iff _ _ _).mp hx
      rw [support_pure, Set.mem_singleton_iff] at hx
      subst hx
      obtain ⟨hruns, hleaf⟩ := runs_of_mem_support_leaf (next PUnit.unit) (roles.2 PUnit.unit)
        (oracles.2 PUnit.unit) (Access.extend initial oracles.1)
        (Access.extendImpl initial oracles.1 impl chosen.1) s chosen.2
        (fun path ↦ leaf ⟨PUnit.unit, path⟩) result hresult
      exact ⟨⟨chosen.2, hchosen, hruns⟩, hleaf⟩

/-- **Every outcome of an execution against a front verifier is an honest run**, with the
verdict at its path. -/
theorem runs_of_mem_support (tree : Oracle.TypeTree.{0}) (roles : tree.RoleDecoration)
    (oracles : tree.OracleDecoration) (initial : PFunctor)
    (impl : QueryImpl (OracleSpec.ofPFunctor initial) Id) (s : Samplers tree roles)
    {A : Type} (p : Prover.Strategy unifSpec tree roles fun _ ↦ A)
    {Out : tree.BranchPath → Type} (verdict : (path : tree.BranchPath) → Out path) :
    ∀ x ∈ support (executeStrategies unifSpec tree roles oracles initial impl p
      (frontVerifier tree roles oracles initial s verdict)),
      Runs tree roles s p x.1 x.2.1 ∧ x.2.2 = verdict x.1.toBranchPath := by
  intro x hx
  obtain ⟨hruns, hleaf⟩ := runs_of_mem_support_leaf tree roles oracles initial impl s p
    (fun path ↦ pure (verdict path)) x hx
  rw [simulateQ_pure, support_pure, Set.mem_singleton_iff] at hleaf
  exact ⟨hruns, hleaf⟩

end
end LeanVM.Protocol.Typed
