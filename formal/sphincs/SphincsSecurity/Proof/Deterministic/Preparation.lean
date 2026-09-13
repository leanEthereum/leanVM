import SphincsSecurity.Proof.Deterministic.MemoErasure
import SphincsSecurity.Proof.Seeded.Presampling

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

open DeterministicSigning

set_option backward.isDefEq.respectTransparency false

/-- Preparing finitely many deterministic computations fixes every result in the final cache. -/
theorem resolves_sequenceFin {α : Type} {n : Nat} (computations : Fin n → OracleComp HashSpec α)
    (before : QueryCache HashSpec) (result : (Fin n → α) × QueryCache HashSpec)
    (h : result ∈ support ((simulateQ randomOracle (Concrete.sequenceFin computations)).run before)) :
    ∀ i, Resolves result.2 (computations i) (result.1 i) := by
  induction n generalizing before with
  | zero => intro i; exact i.elim0
  | succ n ih =>
      simp only [Concrete.sequenceFin, simulateQ_bind, StateT.run_bind,
        simulateQ_pure, StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at h
      obtain ⟨head, hhead, tail, htail, rfl⟩ := h
      intro i
      cases i using Fin.cases with
      | zero =>
          exact (resolves_of_run (computations 0) before head hhead).mono
            (cache_le_of_run (Concrete.sequenceFin fun i => computations i.succ) head.2 tail htail)
      | succ i => exact ih (fun i => computations i.succ) head.2 tail htail i

variable {Request Answer : Type} [Fintype Request] [DecidableEq Request]

noncomputable def prepareSigning (sign : Request → OracleComp HashSpec Answer) :
    OracleComp HashSpec (Request → Answer) :=
  (fun values request => values (Fintype.equivFin Request request)) <$>
    Concrete.sequenceFin (fun i => sign ((Fintype.equivFin Request).symm i))

omit [DecidableEq Request] in
theorem resolves_prepareSigning (sign : Request → OracleComp HashSpec Answer)
    (before : QueryCache HashSpec) (result : (Request → Answer) × QueryCache HashSpec)
    (h : result ∈ support ((simulateQ randomOracle (prepareSigning sign)).run before)) :
    ∀ request, Resolves result.2 (sign request) (result.1 request) := by
  simp only [prepareSigning, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at h
  obtain ⟨raw, hraw, rfl⟩ := h
  intro request
  have h := resolves_sequenceFin (fun i => sign ((Fintype.equivFin Request).symm i)) before raw hraw
    (Fintype.equivFin Request request)
  simpa only [Equiv.symm_apply_apply] using h

/-- Memoization preserves the output distribution of any complete continuation. -/
theorem evalDist_runSigning_memoize {α : Type} (sign : Request → OracleComp HashSpec Answer)
    (computation : OracleComp (OracleWorld + (Request →ₒ Answer)) α) (cache : QueryCache HashSpec) :
    𝒟[(simulateQ romImpl (runSigning sign computation)).run' cache] =
      𝒟[(simulateQ romImpl (runSigning sign (memoize computation ∅))).run' cache] := by
  let preparation : OracleComp OracleWorld (Request → Answer) := liftM (prepareSigning sign)
  rw [evalDist_presample_computation _ preparation cache,
    evalDist_presample_computation (runSigning sign (memoize computation ∅)) preparation cache]
  apply evalDist_bind_congr
  intro prepared hprepared
  have hrun : simulateQ romImpl preparation = simulateQ randomOracle (prepareSigning sign) :=
    QueryImpl.simulateQ_add_liftM_right _ _ _
  rw [hrun] at hprepared
  have hknown := resolves_prepareSigning sign cache prepared hprepared
  have herases := erases_memoize prepared.2 sign prepared.1 hknown computation ∅
    (fun request answer h => by simp at h)
  rw [StateT.run'_eq, StateT.run'_eq, evalDist_map, evalDist_map,
    herases.evalDist_run prepared.2 le_rfl]

theorem hashQueryBound_runSigning_memoize {α : Type} (sign : Request → OracleComp HashSpec Answer)
    (computation : OracleComp (OracleWorld + (Request →ₒ Answer)) α) (cache : QueryCache HashSpec)
    (q : Nat) (hbound : HashQueryBound (runSigning sign computation) cache q) :
    HashQueryBound (runSigning sign (memoize computation ∅)) cache q := by
  let preparation : OracleComp OracleWorld (Request → Answer) := liftM (prepareSigning sign)
  intro result hresult
  rw [mem_support_iff_of_evalDist_eq (evalDist_presample_computation
    (countHashQueries (runSigning sign (memoize computation ∅))) preparation cache),
    mem_support_bind_iff] at hresult
  obtain ⟨prepared, hprepared, hresult⟩ := hresult
  have hbound' := hashQueryBound_after_preparation _ preparation cache q hbound prepared hprepared
  have hrun : simulateQ romImpl preparation = simulateQ randomOracle (prepareSigning sign) :=
    QueryImpl.simulateQ_add_liftM_right _ _ _
  rw [hrun] at hprepared
  have hknown := resolves_prepareSigning sign cache prepared hprepared
  exact (erases_memoize prepared.2 sign prepared.1 hknown computation ∅
    (fun request answer h => by simp at h)).hashQueryBound prepared.2 le_rfl q hbound' result hresult

end SphincsSecurity.Seeded
