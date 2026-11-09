module

public import Common.Duplex.Lazy

@[expose] public section

/-!
# The simulator against a fixed table of challenges

With the challenges sampled in advance as a table `g` (`eagerImpl`, `run'_romImpl_evalDistEq_eager`),
the simulator and the random oracle `H` fold into one stateful implementation over `ProbComp`
(`tabImpl`), whose steps are described here (`tabImpl_F_support`, …).
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec
open Common
open Common.Duplex (GSpec hP gaP VSpec toV)

namespace Common

section FoldWith

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {ι' : Type} {spec' : OracleSpec.{0, 0} ι'}
  {σ τ α : Type}

/-- Fold an outer stateful implementation over `ProbComp` into the state of an implementation. -/
noncomputable def foldWith (outer : QueryImpl spec' (StateT τ ProbComp))
    (impl : QueryImpl spec (StateT σ (OracleComp spec'))) :
    QueryImpl spec (StateT (σ × τ) ProbComp) :=
  (outer.mapStateTBase impl).flattenStateT

theorem foldWith_run (outer : QueryImpl spec' (StateT τ ProbComp))
    (impl : QueryImpl spec (StateT σ (OracleComp spec'))) (t : spec.Domain) (s : σ) (c : τ) :
    ((foldWith outer impl) t).run (s, c) =
      (fun y ↦ (y.1.1, (y.1.2, y.2))) <$> (simulateQ outer ((impl t).run s)).run c :=
  rfl

theorem run_simulateQ_foldWith (outer : QueryImpl spec' (StateT τ ProbComp))
    (impl : QueryImpl spec (StateT σ (OracleComp spec'))) (oa : OracleComp spec α) (s : σ)
    (c : τ) :
    (simulateQ outer ((simulateQ impl oa).run s)).run c =
      (fun z ↦ ((z.1, z.2.1), z.2.2)) <$> (simulateQ (foldWith outer impl) oa).run (s, c) := by
  rw [foldWith, OracleComp.simulateQ_flattenStateT_run, ← QueryImpl.simulateQ_mapStateTBase_run]
  simp

theorem run'_simulateQ_foldWith (outer : QueryImpl spec' (StateT τ ProbComp))
    (impl : QueryImpl spec (StateT σ (OracleComp spec'))) (oa : OracleComp spec α) (s : σ)
    (c : τ) :
    (simulateQ outer ((simulateQ impl oa).run' s)).run' c =
      (simulateQ (foldWith outer impl) oa).run' (s, c) := by
  have h := congrArg (fun x ↦ (fun z ↦ z.1.1) <$> x) (run_simulateQ_foldWith outer impl oa s c)
  simp only [Functor.map_map] at h
  simpa [StateT.run'_eq, simulateQ_map] using h

end FoldWith

end Common

namespace Common.SeedDuplex

variable {Msg Dg St Root Z W Cp : Type} {n : ℕ}
  [DecidableEq Msg] [DecidableEq St] [DecidableEq Root] [DecidableEq Cp]
  [SampleableType Dg] [SampleableType St] [SampleableType Z] [SampleableType W]
  [Fintype St] [Fintype Z] [Fintype W] [Fintype Root] [Nonempty Z]
  (D : DuplexSpec Msg Dg St Root Z W Cp n)

/-- A table of challenges. -/
abbrev Tab (Root Z : Type) (n : ℕ) := Subtype (fun _ : Root × Fin n ↦ True) → Z

/-- The challenge `(r, j)` of a table. -/
def Tab.at (g : Tab Root Z n) (r : Root) (j : Fin n) : Z := g ⟨(r, j), trivial⟩

/-- The challenges a table, `H` a random oracle. -/
noncomputable abbrev tabOuter (g : Tab Root Z n) :=
  eagerImpl (hs := roSpec Msg Dg) (fun _ : Root × Fin n ↦ True) g

/-- **The simulator against the table `g`**, with `H` folded in. -/
noncomputable def tabImpl (g : Tab Root Z n) :
    QueryImpl (Rom2 Msg Dg St)
      (StateT (SimSt Dg St Root n × (GSpec Msg Dg Root Z n).QueryCache) ProbComp) :=
  foldWith (tabOuter g) (simImpl D hP gaP)

/-- The challenge a fresh state is programmed with, if any. -/
def progLbl (s : SimSt Dg St Root n) (x : St) : Option (Root × Fin n) :=
  match efflab D s x with
  | some L => if L ∈ s.used then none else some L
  | none => none

/-- A cache without challenges. -/
def GFree (c : (GSpec Msg Dg Root Z n).QueryCache) : Prop := ∀ d, c (.inr d) = none

theorem tab_coin (g : Tab Root Z n) (k : ℕ) (s : SimSt Dg St Root n)
    (c : (GSpec Msg Dg Root Z n).QueryCache) {z}
    (hz : z ∈ support ((tabImpl D g (.inl k)).run (s, c))) : z.2 = (s, c) := by
  rw [tabImpl, foldWith_run] at hz
  simp only [simImpl, StateT.run_monadLift, monadLift_self, simulateQ_bind, StateT.run_bind,
    simulateQ_pure, StateT.run_pure, simulateQ_eagerImpl_liftM] at hz
  simp at hz
  obtain ⟨a, rfl⟩ := hz
  rfl

theorem tabOuter_hP (g : Tab Root Z n) (m : Msg) (c : (GSpec Msg Dg Root Z n).QueryCache) :
    (simulateQ (tabOuter g) (hP (Root := Root) (Z := Z) (n := n) m)).run c =
      roStep (hs := GSpec Msg Dg Root Z n) (.inl m) c := by
  rw [hP, show (simulateQ (tabOuter g) (liftM ((unifSpec + GSpec Msg Dg Root Z n).query
    (.inr (.inl m))))) = tabOuter g (.inr (.inl m)) from simulateQ_spec_query _ _]
  change ((GSpec Msg Dg Root Z n).randomOracle (.inl m)).run c = _
  rw [randomOracle.run_eq]
  rfl

theorem tabOuter_gaP (g : Tab Root Z n) (r : Root) (j : Fin n)
    (c : (GSpec Msg Dg Root Z n).QueryCache) :
    (simulateQ (tabOuter g) (gaP (Msg := Msg) (Dg := Dg) r j)).run c =
      pure ((c (.inr (r, j))).getD (g.at r j), c) := by
  rw [gaP, show (simulateQ (tabOuter g) (liftM ((unifSpec + GSpec Msg Dg Root Z n).query
    (.inr (.inr (r, j)))))) = tabOuter g (.inr (.inr (r, j))) from simulateQ_spec_query _ _]
  simp [eagerImpl, Tab.at]

theorem tabOuter_G_run (g : Tab Root Z n) (r : Root) (j : Fin n)
    (c : (GSpec Msg Dg Root Z n).QueryCache) :
    (tabOuter (Msg := Msg) (Dg := Dg) g (.inr (.inr (r, j)))).run c =
      pure ((c (.inr (r, j))).getD (g.at r j), c) := by
  simp [eagerImpl, Tab.at]

theorem tab_H (g : Tab Root Z n) (m : Msg) (s : SimSt Dg St Root n)
    (c : (GSpec Msg Dg Root Z n).QueryCache) {z}
    (hz : z ∈ support ((tabImpl D g (.inr (.inl m))).run (s, c))) :
    (z.1, z.2.2) ∈ support (roStep (hs := GSpec Msg Dg Root Z n) (.inl m) c) ∧
      z.2.1 = if m = D.label then { s with x0 := some (D.init z.1), iv := some z.1 } else s := by
  rw [tabImpl, foldWith_run] at hz
  simp only [simImpl, StateT.run_mk, simulateQ_bind, StateT.run_bind, simulateQ_pure,
    StateT.run_pure, tabOuter_hP, support_map, Set.mem_image, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨_, ⟨v, hv, rfl⟩, rfl⟩ := hz
  exact ⟨hv, rfl⟩

theorem tab_F (g : Tab Root Z n) (x : St) (s : SimSt Dg St Root n)
    (c : (GSpec Msg Dg Root Z n).QueryCache) (hc : GFree c) {z}
    (hz : z ∈ support ((tabImpl D g (.inr (.inr x))).run (s, c))) :
    (s.answer x = some z.1 ∧ z.2 = (s, c)) ∨
      (s.answer x = none ∧ z.2 = (s.record D x z.1 (progLbl D s x), c) ∧
        ∀ r j, progLbl D s x = some (r, j) → ∃ w, z.1 = D.build (g.at r j, w)) := by
  rw [tabImpl, foldWith_run] at hz
  simp only [simImpl, StateT.run_mk] at hz
  rcases ha : s.answer x with _ | y
  · simp only [ha, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
      support_map, Set.mem_image, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨_, ⟨v, hv, rfl⟩, rfl⟩ := hz
    right
    unfold freshAns at hv
    unfold progLbl
    split at hv
    · next r j hrj =>
      simp only [hrj]
      split_ifs at hv ⊢ with hu
      · simp [simulateQ_map, simulateQ_eagerImpl_liftM] at hv
        obtain ⟨y, rfl⟩ := hv
        simp
      · simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
          tabOuter_gaP, simulateQ_eagerImpl_liftM, pure_bind, support_bind, support_map,
          Set.mem_iUnion, Set.mem_image, support_pure, Set.mem_singleton_iff] at hv
        obtain ⟨_, ⟨w, -, rfl⟩, rfl⟩ := hv
        refine ⟨trivial, rfl, ?_⟩
        intro r' j' h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨w, by simp [hc (r, j)]⟩
    · next hrj =>
      simp only [hrj]
      simp [simulateQ_map, simulateQ_eagerImpl_liftM] at hv
      obtain ⟨y, rfl⟩ := hv
      simp
  · simp only [ha, simulateQ_pure, StateT.run_pure, support_map, Set.mem_image, support_pure,
      Set.mem_singleton_iff] at hz
    obtain ⟨_, rfl, rfl⟩ := hz
    exact Or.inl ⟨rfl, rfl⟩

end Common.SeedDuplex
