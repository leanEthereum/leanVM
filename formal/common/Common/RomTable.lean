module

public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.SimSemantics.SimulateQ.FinMOfFn
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import VCVio.OracleComp.EvalDist.Sum
public import VCVio.EvalDist.Monad.UniformTable
public import Common.EvalDistEq
import Common.RomComm

@[expose] public section

/-!
# Tables of a lazy random oracle

For a random oracle `D →ₒ R`, the schemes' proofs sample their key material by querying a table of
distinct fresh inputs, and move such queries before a computation:

* `evalDist_queryTable_fresh`: querying distinct fresh inputs `inputs : J → D` returns a uniform
  table `J → R` and the cache that records it (`cacheTable`).
* `evalDist_presample_computation`: in the random-oracle model `(D →ₒ R).romImpl`, running any
  computation first (and keeping its cache) leaves the output distribution of a later computation
  unchanged; it takes the model under a scheme's own name, which must unfold to it by `rfl`.
* `evalDistEq_uniformSample_bind_update`: overwriting one cell of a uniform table with an
  independent uniform value leaves it uniform.
-/

open OracleComp OracleSpec

namespace Common.RomTable

/-- A query through a stateful handler runs the continuation from the reached state. -/
theorem run'_query_bind {ι : Type*} {σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp)) (input : spec.Domain)
    (next : spec.Range input → OracleComp spec α) (state : σ) :
    (simulateQ impl (liftM (spec.query input) >>= next)).run' state =
      ((impl input).run state >>= fun result => (simulateQ impl (next result.1)).run' result.2) := by
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]

/-- Overwriting one cell of a uniform table with an independent uniform value leaves the table
uniform, before any continuation. -/
theorem evalDistEq_uniformSample_bind_update {D R α : Type} [Finite D] [DecidableEq D] [Finite R]
    [Nonempty R] [SampleableType R] [SampleableType (D → R)] (t : D) (f : (D → R) → ProbComp α) :
    ($ᵗ R >>= fun u => $ᵗ (D → R) >>= fun g => f (Function.update g t u)) =ᵈ
      ($ᵗ (D → R) >>= f) := by
  refine evalDistEq_iff_evalDist_eq.mpr ?_
  let : MeasurableSpace R := ⊤
  let : MeasurableSpace α := ⊤
  exact evalDist_bind_bind_update ($ᵗ R) ($ᵗ (D → R)) SampleableType.evalDist_uniformSample
    SampleableType.evalDist_uniformSample t f

/-! ### Tables of fresh queries -/

section Table

variable {D R : Type} [DecidableEq D]

/-- The cache with the answers `outputs` recorded at `inputs`, in index order. -/
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
          · exact fun j h => Fin.succ_ne_zero j (hinj h).symm
      | succ i => exact ih _ _ (fun _ _ h => Fin.succ_injective _ (hinj h)) _ i

variable {J : Type} [Fintype J]

/-- The cache with the table `outputs` recorded at the distinct inputs `inputs`. -/
noncomputable def cacheTable (cache : QueryCache (D →ₒ R)) (inputs : J → D) (outputs : J → R) :
    QueryCache (D →ₒ R) :=
  cacheFin cache (inputs ∘ (Fintype.equivFin J).symm) (outputs ∘ (Fintype.equivFin J).symm)

theorem cacheTable_apply (cache : QueryCache (D →ₒ R)) (inputs : J → D)
    (hinj : Function.Injective inputs) (outputs : J → R) (j : J) :
    cacheTable cache inputs outputs (inputs j) = some (outputs j) := by
  have h := cacheFin_apply cache (inputs ∘ (Fintype.equivFin J).symm)
    (hinj.comp (Fintype.equivFin J).symm.injective) (outputs ∘ (Fintype.equivFin J).symm)
    (Fintype.equivFin J j)
  simp only [Function.comp_apply] at h
  rw [(Fintype.equivFin J).symm_apply_apply] at h
  exact h

theorem cacheTable_apply_of_not_mem (cache : QueryCache (D →ₒ R)) (inputs : J → D)
    (outputs : J → R) (input : D) (hinput : ∀ j, input ≠ inputs j) :
    cacheTable cache inputs outputs input = cache input :=
  cacheFin_apply_of_not_mem _ _ _ _ (fun _ => hinput _)

/-- Query the oracle at every `inputs j`, in the order of `Fintype.equivFin J`. -/
noncomputable def queryTable (inputs : J → D) : OracleComp (D →ₒ R) (J → R) :=
  (Equiv.arrowCongr (Fintype.equivFin J).symm (Equiv.refl R)) <$> Fin.mOfFn _ fun i =>
    (liftM ((D →ₒ R).query (inputs ((Fintype.equivFin J).symm i))) : OracleComp (D →ₒ R) R)

variable [SampleableType R]

/-- Distinct fresh inputs give independent uniform outputs and the cache that records them. -/
theorem run_mOfFn_fresh {n : Nat} (inputs : Fin n → D)
    (hinj : Function.Injective inputs) (cache : QueryCache (D →ₒ R))
    (hfresh : ∀ i, cache (inputs i) = none) :
    (simulateQ randomOracle (Fin.mOfFn n fun i =>
      (liftM ((D →ₒ R).query (inputs i)) : OracleComp (D →ₒ R) R))).run cache =
      (do
        let outputs ← Fin.mOfFn n fun _ => ($ᵗ R : ProbComp R)
        pure (outputs, cacheFin cache inputs outputs)) := by
  induction n generalizing cache with
  | zero => simp only [Fin.mOfFn, simulateQ_pure, StateT.run_pure, pure_bind, cacheFin]
  | succ n ih =>
      simp only [Fin.mOfFn, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [QueryImpl.withCaching_run_none _ (hfresh 0)]
      simp only [bind_map_left, simulateQ_pure, StateT.run_pure, bind_pure_comp, map_bind]
      change (($ᵗ R) >>= _) = (($ᵗ R) >>= _)
      refine bind_congr fun head => ?_
      have htail : ∀ i : Fin n, (cache.cacheQuery (inputs 0) head) (inputs i.succ) = none :=
        fun i => (QueryCache.cacheQuery_of_ne _ _ fun h => Fin.succ_ne_zero i (hinj h)).trans
          (hfresh i.succ)
      rw [ih (fun i => inputs i.succ) (fun _ _ h => Fin.succ_injective _ (hinj h)) _ htail]
      simp only [bind_pure_comp, Functor.map_map, cacheFin]
      rfl

/-- `n` independent uniform draws are a uniform tuple. -/
theorem evalDist_mOfFn_uniform [Fintype R] (n : Nat) :
    (Fin.mOfFn n fun _ => ($ᵗ R : ProbComp R)) =ᵈ ($ᵗ (Fin n → R)) := by
  classical
  induction n with
  | zero =>
      refine OracleComp.evalDistEq_of_forall_prEvent_eq_output fun values => ?_
      have heq : values = Fin.elim0 := funext fun i => i.elim0
      simp [Fin.mOfFn, heq, Subsingleton.elim (default : Fin 0 → R) Fin.elim0, Finset.filter_eq']
  | succ n ih =>
      refine EvalDistEq.trans (my := Fin.consEquiv (fun _ => R) <$> (do
          let head ← $ᵗ R
          let tail ← $ᵗ (Fin n → R)
          pure (head, tail))) ?_ ?_
      · simp only [Fin.mOfFn, map_bind, Fin.consEquiv, Equiv.coe_fn_mk, bind_pure_comp]
        refine EvalDistEq.bind_right _ fun head => ?_
        simpa only [Functor.map_map] using ih.map (fun tail => (Fin.cons head tail : Fin (n + 1) → R))
      rw [← SampleableType.uniformSample_prod_eq_bind]
      exact SampleableType.map_uniformSample_evalDistEq_of_bijective
        (Fin.consEquiv (fun _ => R)).bijective

variable [Fintype R] [SampleableType (J → R)]

/-- **Querying a table of distinct fresh inputs** returns a uniform table and the cache that
records it. -/
theorem evalDist_queryTable_fresh (inputs : J → D) (hinj : Function.Injective inputs)
    (cache : QueryCache (D →ₒ R)) (hfresh : ∀ j, cache (inputs j) = none) :
    ((simulateQ randomOracle (queryTable inputs)).run cache) =ᵈ
      ((fun outputs => (outputs, cacheTable cache inputs outputs)) <$> ($ᵗ (J → R))) := by
  classical
  let e := Equiv.arrowCongr (Fintype.equivFin J).symm (Equiv.refl R)
  rw [queryTable, simulateQ_map, StateT.run_map,
    run_mOfFn_fresh (fun i => inputs ((Fintype.equivFin J).symm i))
      (fun _ _ h => (Fintype.equivFin J).symm.injective (hinj h)) cache (fun _ => hfresh _)]
  simp only [bind_pure_comp, Functor.map_map]
  refine ((evalDist_mOfFn_uniform _).map _).trans ?_
  refine (EvalDistEq.of_eq ?_).trans
    ((SampleableType.map_uniformSample_evalDistEq_of_bijective e.bijective).map
      fun outputs => (outputs, cacheTable cache inputs outputs))
  rw [Functor.map_map]
  congr 1
  funext outputs
  simp [cacheTable, e, Function.comp_def]

end Table

/-! ### Presampling in the random-oracle model -/

section Presample

variable {D R : Type} [DecidableEq D] [SampleableType R]

local notation "World" => unifSpec + (D →ₒ R)
local notation "rom" => OracleSpec.romImpl (D →ₒ R)

/-- **Presampling.** A computation run first, its cache kept, leaves the distribution of another
computation unchanged. `impl` is the random-oracle model `(D →ₒ R).romImpl` under a scheme's own
name; `himpl` is closed by `rfl`. -/
theorem evalDist_presample_computation (impl : QueryImpl World (StateT (QueryCache (D →ₒ R)) ProbComp))
    {α β : Type} (computation : OracleComp World α)
    (preparation : OracleComp World β) (cache : QueryCache (D →ₒ R)) (himpl : impl = rom := by rfl) :
    ((simulateQ impl computation).run' cache) =ᵈ
      ((simulateQ impl preparation).run cache >>= fun result =>
        (simulateQ impl computation).run' result.2) := by
  obtain rfl : impl = rom := himpl
  have h := (run_bind_bind_comm computation preparation (fun result _ => pure result) cache).map
    Prod.fst
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, bind_pure, map_bind,
    map_pure] at h
  rw [StateT.run'_eq, map_eq_bind_pure_comp]
  simp only [StateT.run'_eq]
  refine EvalDistEq.trans (EvalDistEq.bind_right _ fun result =>
    (EvalDistEq.bind_const _ _).symm) h

end Presample

end Common.RomTable
