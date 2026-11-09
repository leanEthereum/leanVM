module

public import XmssSecurity.Proof.RandomizedStatement
public import XmssSecurity.Proof.UniformFiniteTable

@[expose] public section

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

variable {D R : Type} [DecidableEq D]

def cacheFin : {n : Nat} → QueryCache (D →ₒ R) → (Fin n → D) → (Fin n → R) →
    QueryCache (D →ₒ R)
  | 0, cache, _, _ => cache
  | _ + 1, cache, inputs, outputs =>
      cacheFin (cache.cacheQuery (inputs 0) (outputs 0))
        (fun i => inputs i.succ) (fun i => outputs i.succ)

theorem cacheFin_apply_of_not_mem {n : Nat} (cache : QueryCache (D →ₒ R))
    (inputs : Fin n → D) (outputs : Fin n → R) (input : D)
    (hinput : ∀ i, input ≠ inputs i) : cacheFin cache inputs outputs input = cache input := by
  induction n generalizing cache with
  | zero => rfl
  | succ n ih =>
      rw [cacheFin, ih _ _ _ (fun i => hinput i.succ)]
      exact QueryCache.cacheQuery_of_ne cache (outputs 0) (hinput 0)

theorem cacheFin_apply {n : Nat} (cache : QueryCache (D →ₒ R))
    (inputs : Fin n → D) (hinj : Function.Injective inputs) (outputs : Fin n → R) (i : Fin n) :
    cacheFin cache inputs outputs (inputs i) = some (outputs i) := by
  induction n generalizing cache with
  | zero => exact i.elim0
  | succ n ih =>
      cases i using Fin.cases with
      | zero =>
          rw [cacheFin, cacheFin_apply_of_not_mem]
          · exact QueryCache.cacheQuery_self _ _ _
          · intro j h
            have := hinj h
            exact Fin.succ_ne_zero j this.symm
      | succ i =>
          exact ih _ _ (fun _ _ h => Fin.succ_injective _ (hinj h)) _ i

variable [SampleableType R]

/-- Distinct fresh inputs give independent full outputs and the cache that records them. -/
theorem run_sequenceFin_fresh {n : Nat} (inputs : Fin n → D)
    (hinj : Function.Injective inputs) (cache : QueryCache (D →ₒ R))
    (hfresh : ∀ i, cache (inputs i) = none) :
    (simulateQ randomOracle (Concrete.sequenceFin fun i =>
      (liftM ((D →ₒ R).query (inputs i)) : OracleComp (D →ₒ R) R))).run cache =
      (do
        let outputs ← Concrete.sequenceFin fun _ : Fin n => ($ᵗ R : ProbComp R)
        pure (outputs, cacheFin cache inputs outputs)) := by
  induction n generalizing cache with
  | zero => simp only [Concrete.sequenceFin, simulateQ_pure, StateT.run_pure, pure_bind, cacheFin]
  | succ n ih =>
      simp only [Concrete.sequenceFin, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [QueryImpl.withCaching_run_none _ (hfresh 0)]
      simp only [bind_map_left, simulateQ_pure, StateT.run_pure, bind_pure_comp, map_bind]
      change (($ᵗ R) >>= _) = (($ᵗ R) >>= _)
      apply bind_congr
      intro head
      have htail : ∀ i : Fin n, (cache.cacheQuery (inputs 0) head) (inputs i.succ) = none := by
        intro i
        rw [QueryCache.cacheQuery_of_ne]
        · exact hfresh i.succ
        · intro h
          exact Fin.succ_ne_zero i (hinj h)
      rw [ih (fun i => inputs i.succ) (fun _ _ h => Fin.succ_injective _ (hinj h)) _ htail]
      simp only [bind_pure_comp, Functor.map_map, cacheFin]
      rfl

theorem evalDist_sequenceFin_uniform [Fintype R] (n : Nat) :
    (Concrete.sequenceFin fun _ : Fin n => ($ᵗ R : ProbComp R)) =ᵈ ($ᵗ (Fin n → R)) := by
  classical
  induction n with
  | zero =>
      refine evalDistEq_iff_forall_prEvent_eq_output.mpr fun values => ?_
      have heq : values = Fin.elim0 := funext fun i => i.elim0
      simp [Concrete.sequenceFin, heq, Subsingleton.elim (default : Fin 0 → R) Fin.elim0,
        Finset.filter_singleton]

  | succ n ih =>
      calc
        _ =ᵈ (finHeadTailEquiv R n <$> (do
            let head ← $ᵗ R
            let tail ← $ᵗ (Fin n → R)
            pure (head, tail))) := by
          simp only [Concrete.sequenceFin, map_bind, finHeadTailEquiv,
            Equiv.coe_fn_mk, bind_pure_comp]
          refine EvalDistEq.bind_right _ fun head => (ih.map _).trans (.of_eq ?_)
          rw [Functor.map_map]
        _ =ᵈ (finHeadTailEquiv R n <$> ($ᵗ (R × (Fin n → R)))) :=
          evalDist_independent_uniform_pair.map _
        _ =ᵈ _ := SampleableType.map_uniformSample_evalDistEq_of_bijective
          (finHeadTailEquiv R n).bijective

end XmssSecurity.Seeded
