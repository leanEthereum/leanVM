module

public import Common.RomComm

@[expose] public section

/-!
# Folding a random oracle into the state

A stateful implementation over `StateT σ (OracleComp (unifSpec + hs))`, run in the random oracle
model for `hs`, is a stateful implementation over `StateT (σ × hs.QueryCache) ProbComp`: the
random oracle's cache joins the state (`foldRO`, `run_simulateQ_foldRO`). Lemmas about runs over
`ProbComp` then apply to random-oracle-model games.
-/

open OracleComp OracleSpec

namespace Common

variable {ι : Type} {spec : OracleSpec.{0, 0} ι} {ι' : Type} [DecidableEq ι']
  {hs : OracleSpec.{0, 0} ι'} [∀ t : hs.Domain, SampleableType (hs.Range t)] {σ α : Type}

/-- Fold the random oracle `hs` into the state of an implementation. -/
noncomputable def foldRO (impl : QueryImpl spec (StateT σ (OracleComp (unifSpec + hs)))) :
    QueryImpl spec (StateT (σ × hs.QueryCache) ProbComp) :=
  (hs.romImpl.mapStateTBase impl).flattenStateT

/-- One step of the folded implementation is one step run in the random oracle model. -/
theorem foldRO_run (impl : QueryImpl spec (StateT σ (OracleComp (unifSpec + hs))))
    (t : spec.Domain) (s : σ) (c : hs.QueryCache) :
    ((foldRO impl) t).run (s, c) =
      (fun y ↦ (y.1.1, (y.1.2, y.2))) <$> (simulateQ hs.romImpl ((impl t).run s)).run c :=
  rfl

/-- **Folding.** A run in the random oracle model is a run of the folded implementation. -/
theorem run_simulateQ_foldRO (impl : QueryImpl spec (StateT σ (OracleComp (unifSpec + hs))))
    (oa : OracleComp spec α) (s : σ) (c : hs.QueryCache) :
    (simulateQ hs.romImpl ((simulateQ impl oa).run s)).run c =
      (fun z ↦ ((z.1, z.2.1), z.2.2)) <$> (simulateQ (foldRO impl) oa).run (s, c) := by
  rw [foldRO, OracleComp.simulateQ_flattenStateT_run, ← QueryImpl.simulateQ_mapStateTBase_run]
  simp

/-- Output form of `run_simulateQ_foldRO`. -/
theorem run'_simulateQ_foldRO (impl : QueryImpl spec (StateT σ (OracleComp (unifSpec + hs))))
    (oa : OracleComp spec α) (s : σ) (c : hs.QueryCache) :
    (simulateQ hs.romImpl ((simulateQ impl oa).run' s)).run' c =
      (simulateQ (foldRO impl) oa).run' (s, c) := by
  have h := congrArg (fun x ↦ (fun z ↦ z.1.1) <$> x) (run_simulateQ_foldRO impl oa s c)
  simp only [Functor.map_map] at h
  simpa [StateT.run'_eq, simulateQ_map] using h

end Common
