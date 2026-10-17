import Sphincs.BridgeForsAssembly

/-! Exposing chain values at the start. The stopped experiment may start from any knowledge that
agrees with the coordinate table, in particular one that also exposes the chain values at and
above the prepared word of every landed leaf. Sampling those values first and completing the
rest is the same law as completing the table and reading them off. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.HiddenBridge

open HiddenReveal HiddenCost Eager Short Concrete

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

section Generic

variable {ι : Type} [Fintype ι]
noncomputable local instance exposeDecEqCoordinate : DecidableEq ι := Classical.decEq _

/-- Exposing a list of coordinates of a table. -/
noncomputable def exposeT (table : ι → Digest) : List ι → Knowledge ι → Knowledge ι
  | [], known => known
  | c :: cs, known => exposeT table cs (known.cacheQuery c (table c))

/-- Sampling a list of coordinates. -/
noncomputable def exposeR : List ι → Knowledge ι → ProbComp (Knowledge ι)
  | [], known => pure known
  | c :: cs, known => (randomOracle (spec := ι →ₒ Digest) c).run known >>= fun r => exposeR cs r.2

omit [Fintype ι] in
theorem knownAgrees_exposeT (table : ι → Digest) :
    ∀ (cs : List ι) (known : Knowledge ι), HiddenRows.KnownAgrees table known →
      HiddenRows.KnownAgrees table (exposeT table cs known)
  | [], _, h => h
  | c :: cs, _, h => knownAgrees_exposeT table cs _ (h.reveal c)

/-- **Exposure commutes with completion.** -/
theorem evalDist_completion_exposeT {β : Type} (next : (ι → Digest) → Knowledge ι → ProbComp β) :
    ∀ (cs : List ι) (known : Knowledge ι),
      𝒟[completion known >>= fun table => next table (exposeT table cs known)] =
        𝒟[exposeR cs known >>= fun known' => completion known' >>= fun table => next table known']
  | [], _ => by simp only [exposeT, exposeR, pure_bind]
  | c :: cs, known => by
      simp only [exposeT, exposeR, bind_assoc]
      rw [completion_reveal known c (fun value table => next table (exposeT table cs (known.cacheQuery c value)))]
      apply evalDist_bind_congr
      rintro ⟨value, known'⟩ hr
      have hcache := HiddenDebt.randomOracle_known_support known c _ hr
      dsimp only at hcache ⊢
      rw [← hcache]
      exact evalDist_completion_exposeT next cs known'

end Generic

open Completeness SeedModel Graph Assembly Reduce HiddenGraph Internalize GraphView

variable [Params]

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

set_option maxRecDepth 100000 in
/-- **Seed-free to stopped, with exposure.** The stopped experiment may start from the known
coordinates together with any list of table coordinates, chosen from the public, structural and
outside samples. -/
theorem seedFree_le_expose (adversary : Adversary) (q : Nat)
    (event : Option Bool × List (HiddenCost.Entry HashInput) → Prop)
    (cs : HashOutput → HiddenGraph.Table → CoordinateHighs → RemainingOutputs → Eager.Table → List Coordinate) :
    Pr[event | seedFreeExperiment adversary q] ≤
      Pr[HiddenReveal.StopOr event | do
        let parameterOutput ← $ᵗ HashOutput
        let fixed ← $ᵗ HiddenGraph.Table
        let highs ← $ᵗ CoordinateHighs
        let remaining ← $ᵗ RemainingOutputs
        let outsideTable ← $ᵗ Eager.Table
        let known ← exposeR (cs parameterOutput fixed highs remaining outsideTable)
          (knownOf (truncateHash parameterOutput) fixed)
        HiddenRows.stoppedExperiment (sampleModel parameterOutput highs)
          (outsideFn (splitMaterial parameterOutput highs remaining fixed)
            (splitAnswers highs remaining fixed) outsideTable)
          (HiddenCost.erase (HiddenCost.trace
            (sampleProgram adversary q parameterOutput fixed highs remaining)))
          known] := by
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_seedFree_completion adversary q)]
  refine probEvent_bind_mono_support _ _ _ _ _ fun parameterOutput _ => ?_
  refine probEvent_bind_mono_support _ _ _ _ _ fun fixed _ => ?_
  refine probEvent_bind_mono_support _ _ _ _ _ fun highs _ => ?_
  refine probEvent_bind_mono_support _ _ _ _ _ fun remaining _ => ?_
  refine probEvent_bind_mono_support _ _ _ _ _ fun outsideTable _ => ?_
  unfold HiddenRows.stoppedExperiment
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_completion_exposeT
    (fun table known => HiddenRows.stopped (sampleModel parameterOutput highs) table
      (outsideFn (splitMaterial parameterOutput highs remaining fixed)
        (splitAnswers highs remaining fixed) outsideTable)
      (HiddenCost.erase (HiddenCost.trace (sampleProgram adversary q parameterOutput fixed highs remaining)))
      known)
    (cs parameterOutput fixed highs remaining outsideTable) (knownOf (truncateHash parameterOutput) fixed)).symm]
  refine probEvent_bind_mono_support _ _ _ _ _ fun table htable => ?_
  have hagree : HiddenRows.KnownAgrees table (knownOf (truncateHash parameterOutput) fixed) := by
    unfold completion at htable
    rw [support_map] at htable
    obtain ⟨t, _, rfl⟩ := htable
    exact HiddenRows.knownAgrees_completion _ t
  rw [hiddenRun_eq]
  exact costRun_le_stopped (sampleModel parameterOutput highs) table
    (outsideFn (splitMaterial parameterOutput highs remaining fixed) (splitAnswers highs remaining fixed) outsideTable)
    (sampleProgram adversary q parameterOutput fixed highs remaining) _
    (knownAgrees_exposeT table _ _ hagree) event

/-- The preparation's search results read off an answer function. -/
noncomputable def resultsOf (parameter : PublicParameter) (forsKey : Index → Digest) (f : QueryImpl HashSpec Id) :
    Index → Option (Counter × Encoding) :=
  fun leaf => Prefix.firstEncoding f parameter topLayer rootTree leaf (forsKey leaf) encodingAttemptLimit 0

omit [Params] in
theorem extend_agrees (cache : QueryCache HashSpec) (table : Eager.Table) :
    cache.AgreesWithFn (extend cache table) := fun input answer h => by
  simp [extend, h]

omit [Params] in
/-- **Preparation with exposure.** -/
theorem evalDist_expose_prep {A α : Type}
    (model : HiddenRows.Model HashInput HashOutput A HiddenGraph.Coordinate)
    (base : QueryCache HashSpec) (parameter : PublicParameter) (forsKey : Index → Digest)
    (computation : OracleComp (HiddenRows.SourceSpec HashInput HashOutput HiddenGraph.Coordinate) α)
    (hshort : OnlyShort computation) (known : HiddenReveal.Knowledge HiddenGraph.Coordinate)
    (cs : (Index → Option (Counter × Encoding)) → List Coordinate) :
    𝒟[($ᵗ Eager.Table) >>= fun outside =>
        exposeR (cs (resultsOf parameter forsKey (extend base outside))) known >>= fun known' =>
          HiddenRows.stoppedExperiment model (extend base outside) computation known'] =
      𝒟[(simulateQ randomOracle (searchAll parameter forsKey)).run base >>= fun prepared =>
        exposeR (cs prepared.1) known >>= fun known' =>
          Option.map Prod.fst <$> HiddenOutside.stoppedExperiment model computation known' prepared.2] := by
  rw [evalDist_eager_prefix (searchAll parameter forsKey) (Only.searchAll parameter forsKey) base
    (fun f => exposeR (cs (resultsOf parameter forsKey f)) known >>= fun known' =>
      HiddenRows.stoppedExperiment model f computation known')]
  apply evalDist_bind_congr
  intro prepared hprepared
  have hres : ∀ outside, resultsOf parameter forsKey (extend prepared.2 outside) = prepared.1 := by
    intro outside
    funext leaf
    exact (preparation_support parameter forsKey base prepared hprepared (extend prepared.2 outside)
      (extend_agrees _ _)).2 leaf
  simp only [hres]
  rw [evalDist_bind_bind_swap]
  apply evalDist_bind_congr'
  intro known'
  exact evalDist_stoppedExperiment_lazy model _ computation hshort known'

/-- The prepared word of a leaf (the dummy word when the search failed). -/
noncomputable def preparedWord (results : Index → Option (Counter × Encoding)) (leaf : Index) : Encoding :=
  ((results leaf).map Prod.snd).getD ReferenceChoice.dummyWord

/-- Root-tree chain coordinates at and above the prepared word of a landed leaf. -/
def AboveWord (parameter : PublicParameter) (results : Index → Option (Counter × Encoding)) :
    Coordinate → Prop
  | .chain lay tree leaf chain position =>
      lay = topLayer ∧ tree = rootTree ∧ Landed parameter leaf ∧ (preparedWord results leaf chain).val ≤ position.val
  | _ => False

/-- The above-word coordinates as a list. -/
noncomputable def aboveList (parameter : PublicParameter) (results : Index → Option (Counter × Encoding)) :
    List Coordinate :=
  (Finset.univ.filter (AboveWord parameter results)).toList

theorem mem_aboveList {parameter : PublicParameter} {results : Index → Option (Counter × Encoding)}
    {c : Coordinate} : c ∈ aboveList parameter results ↔ AboveWord parameter results c := by
  simp [aboveList]

end Sphincs.Security.HiddenBridge
