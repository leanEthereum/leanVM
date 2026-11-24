module

public import FORS.LazyRun.PreparedRun

@[expose] public section

/-! Exposing chain values at the start. The stopped experiment may start from any knowledge that
agrees with the coordinate table, in particular one that also exposes the chain values at and
above the prepared word of every retained key. Sampling those values first and completing the
rest is the same law as completing the table and reading them off. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.HiddenBridge

variable [Params]

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
      (completion known >>= fun table => next table (exposeT table cs known)) =ᵈ (exposeR cs known >>= fun known' => completion known' >>= fun table => next table known')
  | [], _ => by simp only [exposeT, exposeR, pure_bind, EvalDistEq.refl]
  | c :: cs, known => by
      simp only [exposeT, exposeR, bind_assoc]
      refine (completion_reveal known c
        (fun value table => next table (exposeT table cs (known.cacheQuery c value)))).trans ?_
      refine OracleComp.EvalDistEq.bind_congr_of_support _ ?_
      rintro ⟨value, known'⟩ hr
      have hcache := HiddenDebt.randomOracle_known_support known c _ hr
      dsimp only at hcache ⊢
      rw [← hcache]
      exact evalDist_completion_exposeT next cs known'

end Generic

open Completeness SeedModel _root_.FORS.Security.Graph Assembly Reduce HiddenGraph Internalize GraphView

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

/-- The preparation's search results read off an answer function. -/
noncomputable def resultsOf (parameter : PublicParameter) (message : OtsKey → HashInput)
    (f : QueryImpl HashSpec Id) : OtsKey → Option (Counter × Encoding) :=
  fun key => Prefix.firstEncoding f parameter key.1 key.2.1 key.2.2 (message key) encodingAttemptLimit 0

theorem extend_agrees (cache : QueryCache HashSpec) (table : Eager.Table) :
    cache.AgreesWithFn (extend cache table) := fun input answer h => by
  simp [extend, h]

/-- **Preparation with exposure.** -/
theorem evalDist_expose_prep {A α : Type}
    (model : HiddenRows.Model HashInput HashOutput A HiddenGraph.Coordinate)
    (base : QueryCache HashSpec) (parameter : PublicParameter) (message : OtsKey → HashInput)
    (hmessage : ∀ key, Short.ShortMessage (message key))
    (computation : OracleComp (HiddenRows.SourceSpec HashInput HashOutput HiddenGraph.Coordinate) α)
    (hshort : OnlyShort computation) (known : HiddenReveal.Knowledge HiddenGraph.Coordinate)
    (cs : (OtsKey → Option (Counter × Encoding)) → List Coordinate) :
    (($ᵗ Eager.Table) >>= fun outside =>
        exposeR (cs (resultsOf parameter message (extend base outside))) known >>= fun known' =>
          HiddenRows.stoppedExperiment model (extend base outside) computation known') =ᵈ ((simulateQ randomOracle (searchAll parameter message)).run base >>= fun prepared =>
        exposeR (cs prepared.1) known >>= fun known' =>
          Option.map Prod.fst <$> HiddenOutside.stoppedExperiment model computation known' prepared.2) := by
  refine (evalDist_eager_prefix (searchAll parameter message) (Only.searchAll parameter message hmessage) base
    (fun f => exposeR (cs (resultsOf parameter message f)) known >>= fun known' =>
      HiddenRows.stoppedExperiment model f computation known')).trans ?_
  refine OracleComp.EvalDistEq.bind_congr_of_support _ fun prepared hprepared => ?_
  have hres : ∀ outside, resultsOf parameter message (extend prepared.2 outside) = prepared.1 := by
    intro outside
    funext key
    exact (preparation_support parameter message base prepared hprepared (extend prepared.2 outside)
      (extend_agrees _ _)).2 key
  simp only [hres]
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  exact EvalDistEq.bind_right _ fun known' =>
    evalDist_stoppedExperiment_lazy model _ computation hshort known'

/-- The prepared word of a key (the dummy word when the search failed). -/
noncomputable def preparedWord (results : OtsKey → Option (Counter × Encoding)) (key : OtsKey) : Encoding :=
  ((results key).map Prod.snd).getD ReferenceChoice.dummyWord

/-- Chain coordinates of a retained key at and above its prepared word. -/
def AboveWord (parameter : PublicParameter) (results : OtsKey → Option (Counter × Encoding)) :
    Coordinate → Prop
  | .chain lay tree leaf chain position =>
      PrunedGraph.KeyActive parameter lay tree leaf ∧ (preparedWord results (lay, tree, leaf) chain).val ≤ position.val
  | _ => False

/-- The above-word coordinates as a list. -/
noncomputable def aboveList (parameter : PublicParameter) (results : OtsKey → Option (Counter × Encoding)) :
    List Coordinate :=
  (Finset.univ.filter (AboveWord parameter results)).toList

theorem mem_aboveList {parameter : PublicParameter} {results : OtsKey → Option (Counter × Encoding)}
    {c : Coordinate} : c ∈ aboveList parameter results ↔ AboveWord parameter results c := by
  simp [aboveList]

end FORS.Security.HiddenBridge
