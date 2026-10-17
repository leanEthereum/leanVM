import XmssSecurity.Proof.Bridge.Derivation

/-!
# The programmed derivation cache

Answering every derivation of a seed up front is one uniform draw of a derivation table, recorded in
`progCache`. The cache holds only inputs naming the seed, and no tweakable input.
-/

open OracleComp OracleSpec

namespace XmssSecurity.Bridge

open Seeded DeterministicSigning

set_option backward.isDefEq.respectTransparency false

noncomputable opaque bottomSampleable : SampleableType (BottomPos → HashOutput) :=
  SampleableType.ofFintype (BottomPos → HashOutput)

noncomputable opaque topOtsSampleable : SampleableType (TopOtsPos → HashOutput) :=
  SampleableType.ofFintype (TopOtsPos → HashOutput)

noncomputable opaque topRndSampleable : SampleableType (TopRndPos → HashOutput) :=
  SampleableType.ofFintype (TopRndPos → HashOutput)

noncomputable def sampleBottom : ProbComp (BottomPos → HashOutput) :=
  @uniformSample _ bottomSampleable

noncomputable def sampleTopOts : ProbComp (TopOtsPos → HashOutput) :=
  @uniformSample _ topOtsSampleable

noncomputable def sampleTopRnd : ProbComp (TopRndPos → HashOutput) :=
  @uniformSample _ topRndSampleable

/-- The parameter a derivation table fixes. -/
def Derivations.parameter (d : Derivations) : PublicParameter := truncateHash d.param

def paramCache (seed : MasterSeed) (param : HashOutput) : QueryCache HashSpec :=
  (∅ : QueryCache HashSpec).cacheQuery (paramInput seed) param

noncomputable def bottomCache (seed : MasterSeed) (d : Derivations) : QueryCache HashSpec :=
  cacheTable (paramCache seed d.param) (bottomInput d.parameter seed) d.bottom

noncomputable def topCache (seed : MasterSeed) (d : Derivations) : QueryCache HashSpec :=
  cacheTable (bottomCache seed d) (topInput d.parameter seed) d.top

noncomputable def rndCache (seed : MasterSeed) (d : Derivations) : QueryCache HashSpec :=
  cacheTable (topCache seed d) (rndInput d.parameter seed) d.rnd

/-- Every derivation of `seed`, answered by `d`. -/
noncomputable def progCache (seed : MasterSeed) (d : Derivations) : QueryCache HashSpec :=
  cacheTable (rndCache seed d) (topRndInput d.parameter seed) d.topRnd

/-! ## Entries -/

theorem paramCache_of_ne {seed : MasterSeed} {param : HashOutput} {x : HashInput}
    (hx : x ≠ paramInput seed) : paramCache seed param x = none := by
  rw [paramCache, QueryCache.cacheQuery_of_ne _ _ hx]
  rfl

theorem bottomCache_of_not {seed : MasterSeed} {d : Derivations} {x : HashInput}
    (hp : x ≠ paramInput seed) (hb : ∀ pos, x ≠ bottomInput d.parameter seed pos) :
    bottomCache seed d x = none := by
  rw [bottomCache, cacheTable_apply_of_not_mem _ _ _ _ hb, paramCache_of_ne hp]

theorem topCache_of_not {seed : MasterSeed} {d : Derivations} {x : HashInput}
    (hp : x ≠ paramInput seed) (hb : ∀ pos, x ≠ bottomInput d.parameter seed pos)
    (ht : ∀ pos, x ≠ topInput d.parameter seed pos) : topCache seed d x = none := by
  rw [topCache, cacheTable_apply_of_not_mem _ _ _ _ ht, bottomCache_of_not hp hb]

theorem rndCache_of_not {seed : MasterSeed} {d : Derivations} {x : HashInput}
    (hp : x ≠ paramInput seed) (hb : ∀ pos, x ≠ bottomInput d.parameter seed pos)
    (ht : ∀ pos, x ≠ topInput d.parameter seed pos) (hr : ∀ request, x ≠ rndInput d.parameter seed request) :
    rndCache seed d x = none := by
  rw [rndCache, cacheTable_apply_of_not_mem _ _ _ _ hr, topCache_of_not hp hb ht]

theorem progCache_of_not {seed : MasterSeed} {d : Derivations} {x : HashInput}
    (hp : x ≠ paramInput seed) (hb : ∀ pos, x ≠ bottomInput d.parameter seed pos)
    (ht : ∀ pos, x ≠ topInput d.parameter seed pos) (hr : ∀ request, x ≠ rndInput d.parameter seed request)
    (htr : ∀ pos, x ≠ topRndInput d.parameter seed pos) : progCache seed d x = none := by
  rw [progCache, cacheTable_apply_of_not_mem _ _ _ _ htr, rndCache_of_not hp hb ht hr]

theorem topRnd_ne_bottom (parameter : PublicParameter) (seed : MasterSeed) (pos : TopRndPos)
    (pos' : BottomPos) : topRndInput parameter seed pos ≠ bottomInput parameter seed pos' := by
  rw [bottomInput_eq]
  exact topRndInput_ne_keygen _ _ _ _ _ _ (Or.inl rfl)

theorem topRnd_ne_top (parameter : PublicParameter) (seed : MasterSeed) (pos : TopRndPos)
    (pos' : TopOtsPos) : topRndInput parameter seed pos ≠ topInput parameter seed pos' := by
  rw [topInput_eq]
  exact topRndInput_ne_keygen _ _ _ _ _ _ (Or.inl rfl)

theorem topRnd_ne_param (parameter : PublicParameter) (seed seed' : MasterSeed) (pos : TopRndPos) :
    topRndInput parameter seed pos ≠ paramInput seed' := by
  rw [paramInput_eq]
  exact topRndInput_ne_keygen _ _ _ _ _ _ (Or.inr rfl)

theorem rnd_ne_bottom (parameter : PublicParameter) (seed : MasterSeed) (request : SignRequest)
    (pos' : BottomPos) : rndInput parameter seed request ≠ bottomInput parameter seed pos' := by
  rw [bottomInput_eq]
  exact rndInput_ne_keygen _ _ _ _ _ _ (Or.inl rfl)

theorem rnd_ne_top (parameter : PublicParameter) (seed : MasterSeed) (request : SignRequest)
    (pos' : TopOtsPos) : rndInput parameter seed request ≠ topInput parameter seed pos' := by
  rw [topInput_eq]
  exact rndInput_ne_keygen _ _ _ _ _ _ (Or.inl rfl)

theorem rnd_ne_param (parameter : PublicParameter) (seed seed' : MasterSeed) (request : SignRequest) :
    rndInput parameter seed request ≠ paramInput seed' := by
  rw [paramInput_eq]
  exact rndInput_ne_keygen _ _ _ _ _ _ (Or.inr rfl)

theorem progCache_param (seed : MasterSeed) (d : Derivations) :
    progCache seed d (paramInput seed) = some d.param := by
  rw [progCache, cacheTable_apply_of_not_mem _ _ _ _ fun pos h => topRnd_ne_param _ _ _ _ h.symm,
    rndCache, cacheTable_apply_of_not_mem _ _ _ _ fun pos h => rnd_ne_param _ _ _ _ h.symm,
    topCache, cacheTable_apply_of_not_mem _ _ _ _ fun pos h => topInput_ne_param _ _ _ _ h.symm,
    bottomCache, cacheTable_apply_of_not_mem _ _ _ _ fun pos h => bottomInput_ne_param _ _ _ _ h.symm,
    paramCache, QueryCache.cacheQuery_self]

theorem progCache_bottom (seed : MasterSeed) (d : Derivations) (pos : BottomPos) :
    progCache seed d (bottomInput d.parameter seed pos) = some (d.bottom pos) := by
  rw [progCache, cacheTable_apply_of_not_mem _ _ _ _ fun pos' h => topRnd_ne_bottom _ _ _ _ h.symm,
    rndCache, cacheTable_apply_of_not_mem _ _ _ _ fun pos' h => rnd_ne_bottom _ _ _ _ h.symm,
    topCache, cacheTable_apply_of_not_mem _ _ _ _ fun pos' h => topInput_ne_bottom _ _ _ _ h.symm,
    bottomCache, cacheTable_apply _ _ (bottomInput_injective _ _)]

theorem progCache_top (seed : MasterSeed) (d : Derivations) (pos : TopOtsPos) :
    progCache seed d (topInput d.parameter seed pos) = some (d.top pos) := by
  rw [progCache, cacheTable_apply_of_not_mem _ _ _ _ fun pos' h => topRnd_ne_top _ _ _ _ h.symm,
    rndCache, cacheTable_apply_of_not_mem _ _ _ _ fun pos' h => rnd_ne_top _ _ _ _ h.symm,
    topCache, cacheTable_apply _ _ (topInput_injective _ _)]

theorem progCache_rnd (seed : MasterSeed) (d : Derivations) (request : SignRequest) :
    progCache seed d (rndInput d.parameter seed request) = some (d.rnd request) := by
  rw [progCache, cacheTable_apply_of_not_mem _ _ _ _ fun pos' h => topRndInput_ne_rnd _ _ _ _ h.symm,
    rndCache, cacheTable_apply _ _ (rndInput_injective _ _)]

theorem progCache_topRnd (seed : MasterSeed) (d : Derivations) (pos : TopRndPos) :
    progCache seed d (topRndInput d.parameter seed pos) = some (d.topRnd pos) := by
  rw [progCache, cacheTable_apply _ _ (topRndInput_injective _ _)]

theorem progCache_tweakable {seed : MasterSeed} {d : Derivations} {x : HashInput} (hx : Tweakable x) :
    progCache seed d x = none :=
  progCache_of_not (fun h => paramInput_not_tweakable seed (h ▸ hx))
    (fun pos h => bottomInput_not_tweakable _ seed pos (h ▸ hx))
    (fun pos h => topInput_not_tweakable _ seed pos (h ▸ hx))
    (fun request h => rndInput_not_tweakable _ seed request (h ▸ hx))
    (fun pos h => topRndInput_not_tweakable _ seed pos (h ▸ hx))

/-- Every programmed entry names the seed. -/
theorem seedHit_of_progCache {seed : MasterSeed} {d : Derivations} {x : HashInput}
    (hx : progCache seed d x ≠ none) : DerivationSeedHit x seed := by
  by_contra hhit
  apply hx
  exact progCache_of_not (fun h => hhit (h ▸ paramInput_seedHit seed))
    (fun pos h => hhit (h ▸ bottomInput_seedHit _ seed pos))
    (fun pos h => hhit (h ▸ topInput_seedHit _ seed pos))
    (fun request h => hhit (h ▸ rndInput_seedHit _ seed request))
    (fun pos h => hhit (h ▸ topRndInput_seedHit _ seed pos))

theorem agreeOutside_overlay_progCache (seed : MasterSeed) (d : Derivations) (cache : QueryCache HashSpec) :
    AgreeOutside (fun input => SeedHit input seed) (overlay (progCache seed d) cache) cache := by
  intro x hx
  by_cases h : progCache seed d x = none
  · exact overlay_of_none h
  · exact absurd (seedHit_of_progCache h) hx

/-! ## Presampling -/

/-- Query every derivation of `seed`. -/
noncomputable def programDerivations (seed : MasterSeed) : OracleComp HashSpec Derivations := do
  let param ← Concrete.oracleHash (paramInput seed)
  let bottom ← queryTable (bottomInput (truncateHash param) seed)
  let top ← queryTable (topInput (truncateHash param) seed)
  let rnd ← queryTable (rndInput (truncateHash param) seed)
  let topRnd ← queryTable (topRndInput (truncateHash param) seed)
  return ⟨param, bottom, top, rnd, topRnd⟩

/-- A uniform derivation table. -/
noncomputable def drawDerivations : ProbComp Derivations := do
  let param ← $ᵗ HashOutput
  let bottom ← sampleBottom
  let top ← sampleTopOts
  let rnd ← sampleRandomizerOutputs
  let topRnd ← sampleTopRnd
  pure ⟨param, bottom, top, rnd, topRnd⟩

theorem evalDist_run_bind_of {α β σ : Type} {c : OracleComp HashSpec α} {cache : QueryCache HashSpec}
    {sampler : ProbComp σ} {g : σ → α × QueryCache HashSpec}
    (h : 𝒟[(simulateQ randomOracle c).run cache] = 𝒟[g <$> sampler])
    (k : α → OracleComp HashSpec β) :
    𝒟[(simulateQ randomOracle (c >>= k)).run cache] =
      𝒟[sampler >>= fun s => (simulateQ randomOracle (k (g s).1)).run (g s).2] := by
  rw [simulateQ_bind, StateT.run_bind, evalDist_bind, h, ← evalDist_bind, bind_map_left]

/-- Answering the derivations one by one is drawing the table at once. -/
theorem evalDist_programDerivations (seed : MasterSeed) :
    𝒟[(simulateQ randomOracle (programDerivations seed)).run ∅] =
      𝒟[do
        let param ← $ᵗ HashOutput
        let bottom ← sampleBottom
        let top ← sampleTopOts
        let rnd ← sampleRandomizerOutputs
        let topRnd ← sampleTopRnd
        pure ((⟨param, bottom, top, rnd, topRnd⟩ : Derivations),
          progCache seed ⟨param, bottom, top, rnd, topRnd⟩)] := by
  unfold programDerivations
  have hparam : 𝒟[(simulateQ randomOracle (Concrete.oracleHash (paramInput seed) :
      OracleComp HashSpec HashOutput)).run ∅] =
        𝒟[(fun param => (param, paramCache seed param)) <$> ($ᵗ HashOutput)] := by
    change 𝒟[(randomOracle (spec := HashSpec) (paramInput seed)).run ∅] = _
    rw [QueryImpl.withCaching_run_none _ (QueryCache.empty_apply _)]
    rfl
  rw [evalDist_run_bind_of hparam]
  apply evalDist_bind_congr'
  intro param
  rw [evalDist_run_bind_of (evalQ_fresh_bottom seed param)]
  apply evalDist_bind_congr'
  intro bottom
  rw [evalDist_run_bind_of (evalQ_fresh_top seed param bottom)]
  apply evalDist_bind_congr'
  intro top
  rw [evalDist_run_bind_of (evalQ_fresh_rnd seed param bottom top)]
  apply evalDist_bind_congr'
  intro rnd
  rw [evalDist_run_bind_of (evalQ_fresh_topRnd seed param bottom top rnd)]
  apply evalDist_bind_congr'
  intro topRnd
  rw [simulateQ_pure, StateT.run_pure]
  unfold progCache rndCache topCache bottomCache Derivations.parameter
  dsimp only
where
  evalQ_fresh_bottom (seed : MasterSeed) (param : HashOutput) :
      𝒟[(simulateQ randomOracle (queryTable (bottomInput (truncateHash param) seed))).run
        (paramCache seed param)] =
      𝒟[(fun bottom => (bottom, cacheTable (paramCache seed param)
        (bottomInput (truncateHash param) seed) bottom)) <$> sampleBottom] :=
    letI := bottomSampleable
    evalDist_queryTable_fresh _ (bottomInput_injective _ _) _
      fun pos => paramCache_of_ne (bottomInput_ne_param _ _ _ _)
  evalQ_fresh_top (seed : MasterSeed) (param : HashOutput) (bottom : BottomPos → HashOutput) :
      𝒟[(simulateQ randomOracle (queryTable (topInput (truncateHash param) seed))).run
        (cacheTable (paramCache seed param) (bottomInput (truncateHash param) seed) bottom)] =
      𝒟[(fun top => (top, cacheTable (cacheTable (paramCache seed param)
        (bottomInput (truncateHash param) seed) bottom) (topInput (truncateHash param) seed) top)) <$>
          sampleTopOts] :=
    letI := topOtsSampleable
    evalDist_queryTable_fresh _ (topInput_injective _ _) _ fun pos => by
      rw [cacheTable_apply_of_not_mem _ _ _ _ fun pos' => topInput_ne_bottom _ _ _ _,
        paramCache_of_ne (topInput_ne_param _ _ _ _)]
  evalQ_fresh_rnd (seed : MasterSeed) (param : HashOutput) (bottom : BottomPos → HashOutput)
      (top : TopOtsPos → HashOutput) :
      𝒟[(simulateQ randomOracle (queryTable (rndInput (truncateHash param) seed))).run
        (cacheTable (cacheTable (paramCache seed param) (bottomInput (truncateHash param) seed) bottom)
          (topInput (truncateHash param) seed) top)] =
      𝒟[(fun rnd => (rnd, cacheTable (cacheTable (cacheTable (paramCache seed param)
        (bottomInput (truncateHash param) seed) bottom) (topInput (truncateHash param) seed) top)
          (rndInput (truncateHash param) seed) rnd)) <$> sampleRandomizerOutputs] :=
    letI := randomizerOutputsSampleableType
    evalDist_queryTable_fresh _ (rndInput_injective _ _) _ fun request => by
      rw [cacheTable_apply_of_not_mem _ _ _ _ fun pos' => rnd_ne_top _ _ _ _,
        cacheTable_apply_of_not_mem _ _ _ _ fun pos' => rnd_ne_bottom _ _ _ _,
        paramCache_of_ne (rnd_ne_param _ _ _ _)]
  evalQ_fresh_topRnd (seed : MasterSeed) (param : HashOutput) (bottom : BottomPos → HashOutput)
      (top : TopOtsPos → HashOutput) (rnd : RandomizerOutputs) :
      𝒟[(simulateQ randomOracle (queryTable (topRndInput (truncateHash param) seed))).run
        (cacheTable (cacheTable (cacheTable (paramCache seed param)
          (bottomInput (truncateHash param) seed) bottom) (topInput (truncateHash param) seed) top)
            (rndInput (truncateHash param) seed) rnd)] =
      𝒟[(fun topRnd => (topRnd, cacheTable (cacheTable (cacheTable (cacheTable (paramCache seed param)
        (bottomInput (truncateHash param) seed) bottom) (topInput (truncateHash param) seed) top)
          (rndInput (truncateHash param) seed) rnd) (topRndInput (truncateHash param) seed) topRnd)) <$>
            sampleTopRnd] :=
    letI := topRndSampleable
    evalDist_queryTable_fresh _ (topRndInput_injective _ _) _ fun pos => by
      rw [cacheTable_apply_of_not_mem _ _ _ _ fun request => topRndInput_ne_rnd _ _ _ _,
        cacheTable_apply_of_not_mem _ _ _ _ fun pos' => topRnd_ne_top _ _ _ _,
        cacheTable_apply_of_not_mem _ _ _ _ fun pos' => topRnd_ne_bottom _ _ _ _,
        paramCache_of_ne (topRnd_ne_param _ _ _ _)]

theorem evalDist_programDerivations_draw (seed : MasterSeed) {α : Type}
    (k : Derivations × QueryCache HashSpec → ProbComp α) :
    𝒟[(simulateQ randomOracle (programDerivations seed)).run ∅ >>= k] =
      𝒟[drawDerivations >>= fun d => k (d, progCache seed d)] := by
  rw [evalDist_bind, evalDist_programDerivations, ← evalDist_bind]
  congr 1
  unfold drawDerivations
  simp only [bind_assoc, pure_bind]

theorem mem_support_drawDerivations (d : Derivations) : d ∈ support drawDerivations := by
  obtain ⟨param, bottom, top, rnd, topRnd⟩ := d
  have hall : ∀ {α : Type} (sampler : ProbComp α) (x : α),
      (∀ y, Pr[= y | sampler] ≠ 0) → x ∈ support sampler := fun sampler x h => by
    rw [mem_support_iff]; exact h x
  have hu : ∀ {α : Type} (inst : SampleableType α) [Fintype α] (x : α), x ∈ support (@uniformSample α inst) :=
    fun inst _ x => hall _ x fun y => by
      rw [@probOutput_uniformSample _ inst]
      exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  unfold drawDerivations
  rw [mem_support_bind_iff]
  refine ⟨param, hu _ param, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨bottom, hu bottomSampleable bottom, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨top, hu topOtsSampleable top, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨rnd, hu randomizerOutputsSampleableType rnd, ?_⟩
  rw [mem_support_bind_iff]
  exact ⟨topRnd, hu topRndSampleable topRnd, by simp⟩

end XmssSecurity.Bridge
