import XmssSecurity.Proof.FirstLaneEagerBound

open OracleComp OracleSpec

namespace XmssSecurity

def CacheGrowthRepresented
    (target : Key → HashInput) (observe : Key → HashOutput → Action)
    (initial final : QueryCache HashSpec) (trace : List Action) : Prop :=
  initial ≤ final ∧
    ∀ key output, initial (target key) = none →
      final (target key) = some output → observe key output ∈ trace

theorem CacheGrowthRepresented.refl
    (target : Key → HashInput) (observe : Key → HashOutput → Action)
    (cache : QueryCache HashSpec) :
    CacheGrowthRepresented target observe cache cache [] := by
  constructor
  · exact le_rfl
  · intro key output hfresh hfinal
    rw [hfresh] at hfinal
    contradiction

theorem CacheGrowthRepresented.cacheQuery
    {target : Key → HashInput} {observe : Key → HashOutput → Action}
    (cache : QueryCache HashSpec) (key : Key) (output : HashOutput)
    (hfresh : cache (target key) = none)
    (hobserve : ∀ candidate,
      target candidate = target key →
        observe candidate output = observe key output) :
    CacheGrowthRepresented target observe cache
      (cache.cacheQuery (target key) output) [observe key output] := by
  constructor
  · exact QueryCache.le_cacheQuery cache hfresh
  · intro candidate targetOutput hcandidate hfinal
    by_cases heq : target candidate = target key
    · rw [heq, QueryCache.cacheQuery_self] at hfinal
      have : output = targetOutput := Option.some.inj hfinal
      subst targetOutput
      simp [hobserve candidate heq]
    · rw [QueryCache.cacheQuery_of_ne _ _ heq, hcandidate] at hfinal
      contradiction

theorem CacheGrowthRepresented.trans
    {target : Key → HashInput} {observe : Key → HashOutput → Action}
    {initial middle final : QueryCache HashSpec} {head tail : List Action}
    (hhead : CacheGrowthRepresented target observe initial middle head)
    (htail : CacheGrowthRepresented target observe middle final tail) :
    CacheGrowthRepresented target observe initial final (head ++ tail) := by
  constructor
  · exact hhead.1.trans htail.1
  · intro key output hfresh hfinal
    cases hmiddle : middle (target key) with
    | none => exact List.mem_append_right head (htail.2 key output hmiddle hfinal)
    | some middleOutput =>
        have hmiddleFinal : final (target key) = some middleOutput :=
          htail.1 hmiddle
        have : middleOutput = output :=
          Option.some.inj (hmiddleFinal.symm.trans hfinal)
        subst middleOutput
        exact List.mem_append_left tail (hhead.2 key output hfresh hmiddle)

theorem simulateQ_eagerTrace_support_invariant
    {spec : OracleSpec ι} {State : Type}
    [Fintype Index] [DecidableEq Index]
    (table : Index → Digest)
    (impl : QueryImpl spec
      (StateT State (OracleComp (FirstLaneOracleSimulation.World Index))))
    (Invariant : State →
      FirstLaneOracleSimulation.ActionTrace Index → State → Prop)
    (empty : ∀ state, Invariant state [] state)
    (append : ∀ initial middle final headTrace tailTrace,
      Invariant initial headTrace middle →
      Invariant middle tailTrace final →
      Invariant initial (headTrace ++ tailTrace) final)
    (step : ∀ (input : spec.Domain) (state : State)
      (result : (spec.Range input × State) ×
        FirstLaneOracleSimulation.ActionTrace Index),
      result ∈ support
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          ((impl input).run state)).run) →
      Invariant state result.2 result.1.2)
    (computation : OracleComp spec α) (initialState : State)
    (result : (α × State) ×
      FirstLaneOracleSimulation.ActionTrace Index)
    (hresult : result ∈ support
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
        ((simulateQ impl computation).run initialState)).run)) :
    Invariant initialState result.2 result.1.2 := by
  induction computation using OracleComp.inductionOn generalizing
      initialState result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure',
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact empty initialState
  | query_bind input next ih =>
      rw [simulateQ_bind, StateT.run_bind, simulateQ_bind,
        WriterT.run_bind', mem_support_bind_iff] at hresult
      obtain ⟨⟨⟨output, middleState⟩, headTrace⟩, hhead,
        hrestMapped⟩ := hresult
      rw [support_map] at hrestMapped
      obtain ⟨suffixResult, hsuffix, heq⟩ := hrestMapped
      rw [simulateQ_spec_query] at hhead
      have hfirst := step input initialState
        ((output, middleState), headTrace) hhead
      have hrest := ih output middleState suffixResult hsuffix
      have hcomposed := append initialState middleState suffixResult.1.2
        headTrace suffixResult.2 hfirst hrest
      simpa using Eq.mp (congrArg (fun candidate =>
        Invariant initialState candidate.2 candidate.1.2) heq) hcomposed

end XmssSecurity
