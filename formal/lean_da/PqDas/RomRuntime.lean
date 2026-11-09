/-
# Random-oracle runtime

The semantics of computations in the random-oracle world used throughout this
development: the ambient monad `OracleComp (unifSpec + (ComVC →ₒ L))` provides
uniform sampling and a random oracle from (vector-commitment) commitments to
check randomness. `roRuntime` observes such computations by their successful-output measures,
interpreting the oracle as a fresh lazily-sampled random oracle: queries that
hit the cache return the cached value, misses are answered by fresh uniform
sampling and cached. The cache-parametric variant `roRuntimeWithCache` is the
hook for programming the oracle in reductions. Mirrors VCVio's
`FiatShamir.runtimeWithCache`.

`simulateRom` runs the same simulation as a plain probabilistic computation
(rather than observing its output measure); reductions use it to
internally simulate the random-oracle world for an adversary. By construction
the two agree: `evalDist_simulateRomWithCache`.

Benedikt Wagner's formalization (https://github.com/b-wagn/fv-pq-da), ported at 4475179c and
modified for VCVio afa6593.
-/
module

public import VCVio.OracleComp.HasQuery.Morphism
public import VCVio.OracleComp.ProbCompLift
public import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.Coercions.Add.Basic
public import VCVio.OracleComp.SimSemantics.StateT.BundledSemantics
public import PqDas.Defs

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace PqDas

section runtime

variable (ComVC L : Type) [DecidableEq ComVC] [SampleableType L]

/-- Runtime bundle for the random-oracle world, starting from a fixed initial
cache: random-oracle queries that hit the cache return the cached value,
misses are answered by fresh uniform sampling and cached. -/
noncomputable def roRuntimeWithCache (cache : (ComVC →ₒ L).QueryCache) :
    ProbCompRuntime (OracleComp (unifSpec + (ComVC →ₒ L))) :=
  ProbCompRuntime.withStateOracle
    (hashImpl := (randomOracle :
      QueryImpl (ComVC →ₒ L) (StateT ((ComVC →ₒ L).QueryCache) ProbComp)))
    cache

/-- Runtime bundle for the random-oracle world: a fresh random oracle (empty
initial cache). -/
noncomputable def roRuntime : ProbCompRuntime (OracleComp (unifSpec + (ComVC →ₒ L))) :=
  roRuntimeWithCache ComVC L ∅

variable {ComVC L}

/-- The simulation and the runtime semantics agree: observing `simulateRom` as
an output measure is the same as observing the original computation through
the runtime. -/
lemma evalDist_simulateRomWithCache (cache : (ComVC →ₒ L).QueryCache) {α : Type}
    [MeasurableSpace α] (oa : OracleComp (unifSpec + (ComVC →ₒ L)) α) :
    𝒟[simulateRomWithCache cache oa] = (roRuntimeWithCache ComVC L cache).evalDist oa := rfl

/-- Fresh-oracle case of `evalDist_simulateRomWithCache`. -/
lemma evalDist_simulateRom {α : Type} [MeasurableSpace α] (oa : OracleComp (unifSpec + (ComVC →ₒ L)) α) :
    𝒟[simulateRom oa] = (roRuntime ComVC L).evalDist oa := rfl

/-- The mass a plain probabilistic computation's output measure puts on a
singleton is the probability of returning it. -/
lemma evalDist_singleton_eq_prEvent {α : Type} [MeasurableSpace α]
    [MeasurableSingletonClass α] (oa : ProbComp α) (a : α) :
    𝒟[oa] {a} = Pr{let x ← oa}[x = a] :=
  (prEvent_eq_evalDist_singleton oa a).symm

/-! ### Compositional simulation lemmas

These decompose `simulateRomWithCache` along the program structure, exposing
the oracle cache as it threads through: reductions and game-hop proofs use
them to align a simulated random-oracle computation with an explicitly staged
probabilistic program. -/

variable {α β : Type}

@[simp]
lemma simulateRomWithCache_pure (cache : (ComVC →ₒ L).QueryCache) (a : α) :
    simulateRomWithCache cache (pure a : OracleComp (unifSpec + (ComVC →ₒ L)) α) =
      pure a := by
  simp [simulateRomWithCache]

/-- A bind splits into simulating the prefix (keeping its final cache) and
simulating the continuation from that cache. -/
lemma simulateRomWithCache_bind (cache : (ComVC →ₒ L).QueryCache)
    (oa : OracleComp (unifSpec + (ComVC →ₒ L)) α)
    (f : α → OracleComp (unifSpec + (ComVC →ₒ L)) β) :
    simulateRomWithCache cache (oa >>= f) =
      (simulateQ (romImpl ComVC L) oa).run cache >>= fun x =>
        simulateRomWithCache x.2 (f x.1) := by
  simp only [simulateRomWithCache, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]

/-- Binding a plain continuation onto a simulated computation: the simulation
runs from the given cache and the continuation sees only the value (the final
cache is discarded). Used to align a reduction (which discards the cache) with
a game (which threads it, cf. `simulateRomWithCache_bind`). -/
lemma bind_simulateRomWithCache (cache : (ComVC →ₒ L).QueryCache)
    (oa : OracleComp (unifSpec + (ComVC →ₒ L)) α) (g : α → ProbComp β) :
    simulateRomWithCache cache oa >>= g =
      (simulateQ (romImpl ComVC L) oa).run cache >>= fun x => g x.1 := by
  simp [simulateRomWithCache, StateT.run'_eq, bind_map_left]

/-- Simulation commutes with mapping a function over the result. -/
lemma simulateRomWithCache_map (cache : (ComVC →ₒ L).QueryCache)
    (oa : OracleComp (unifSpec + (ComVC →ₒ L)) α) (f : α → β) :
    simulateRomWithCache cache (f <$> oa) = f <$> simulateRomWithCache cache oa := by
  simp only [simulateRomWithCache, simulateQ_map, StateT.run'_eq, StateT.run_map,
    Functor.map_map]

/-- A lifted plain probabilistic computation passes through the simulation
without touching the cache. -/
lemma simulateRomWithCache_liftM_bind (cache : (ComVC →ₒ L).QueryCache)
    (oa : ProbComp α) (f : α → OracleComp (unifSpec + (ComVC →ₒ L)) β) :
    simulateRomWithCache cache (liftM oa >>= f) =
      oa >>= fun x => simulateRomWithCache cache (f x) := by
  simp only [simulateRomWithCache, simulateQ_bind]
  exact roSim.run'_liftM_bind _ oa _ cache

/-- A random-oracle query is answered by the caching oracle implementation on
the current cache. -/
lemma simulateRomWithCache_query_bind (cache : (ComVC →ₒ L).QueryCache)
    (q : ComVC) (f : L → OracleComp (unifSpec + (ComVC →ₒ L)) β) :
    simulateRomWithCache cache
      (HasQuery.query (spec := (ComVC →ₒ L)) q >>= f) =
      ((randomOracle : QueryImpl (ComVC →ₒ L)
          (StateT ((ComVC →ₒ L).QueryCache) ProbComp)) q).run cache >>= fun x =>
        simulateRomWithCache x.2 (f x.1) := by
  simp only [simulateRomWithCache, romImpl, simulateQ_bind,
    roSim.simulateQ_HasQuery_query, StateT.run'_eq, StateT.run_bind, map_bind]

/-! ### Behaviour of the caching oracle on hits and misses -/

/-- A cache hit returns the recorded answer and leaves the cache unchanged. -/
lemma randomOracle_run_hit {q : ComVC} {cache : (ComVC →ₒ L).QueryCache} {r : L}
    (h : cache q = some r) :
    ((randomOracle : QueryImpl (ComVC →ₒ L)
        (StateT ((ComVC →ₒ L).QueryCache) ProbComp)) q).run cache = pure (r, cache) := by
  simp [randomOracle, QueryImpl.withCaching_apply, StateT.run_bind, StateT.run_get, h]

/-- A cache miss samples a fresh uniform answer and records it. -/
lemma randomOracle_run_miss {q : ComVC} {cache : (ComVC →ₒ L).QueryCache}
    (h : cache q = none) :
    ((randomOracle : QueryImpl (ComVC →ₒ L)
        (StateT ((ComVC →ₒ L).QueryCache) ProbComp)) q).run cache =
      ($ᵗ L) >>= fun r => pure (r, cache.cacheQuery q r) := by
  simp only [randomOracle, QueryImpl.withCaching_apply, StateT.run_bind, StateT.run_get,
    pure_bind, uniformSampleImpl, h, liftM, MonadLiftT.monadLift, MonadLift.monadLift]
  simp only [StateT.run_lift, StateT.run_modifyGet]
  rw [bind_assoc]
  simp only [pure_bind]

end runtime

end PqDas
