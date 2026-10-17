import SphincsFors.BridgeLazy

/-! The graph-view cost program of an internalized adversary queries only short ordinary
inputs, and so do its capped, traced and erased forms. -/

open OracleComp OracleSpec ENNReal

namespace SphincsFors.Security.HiddenBridge

open Short Internalize GraphView HiddenCost Concrete

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

def LongCost : CostSpec.Domain → Prop
  | .inl (.inr (.inl bytes)) => ¬IsShort bytes
  | _ => False

/-- Every ordinary query of a cost program is short. -/
def OnlyC {α : Type} (computation : OracleComp CostSpec α) : Prop :=
  computation.IsQueryBoundP LongCost 0

theorem OnlyC.pure' {α : Type} (value : α) : OnlyC (pure value : OracleComp CostSpec α) := trivial

theorem OnlyC.bind {α β : Type} {oa : OracleComp CostSpec α} {next : α → OracleComp CostSpec β}
    (h : OnlyC oa) (hnext : ∀ value, OnlyC (next value)) : OnlyC (oa >>= next) := by
  have := isQueryBoundP_bind (n := 0) (m := 0) h (fun value _ => hnext value)
  simpa [OnlyC] using this

theorem OnlyC.map {α β : Type} {oa : OracleComp CostSpec α} (f : α → β) (h : OnlyC oa) :
    OnlyC (f <$> oa) := by
  rw [OnlyC, isQueryBoundP_map_iff]
  exact h

theorem OnlyC.query {input : CostSpec.Domain} (h : ¬LongCost input) :
    OnlyC (liftM (CostSpec.query input) : OracleComp CostSpec _) := by
  rw [OnlyC, isQueryBoundP_query_iff]
  intro hlong
  exact absurd hlong h

theorem OnlyC.liftHash {α : Type} {oa : OracleComp HashSpec α} (h : Short.Only oa) :
    OnlyC (liftM oa : OracleComp CostSpec α) := by
  induction oa using OracleComp.inductionOn with
  | pure value => exact OnlyC.pure' _
  | query_bind input next ih =>
      rw [Short.Only, isQueryBoundP_query_bind_iff] at h
      rw [liftM_bind]
      refine OnlyC.bind ?_ (fun answer => ih answer ?_)
      · change OnlyC (liftM (CostSpec.query (.inl (.inr (.inl input)))) : OracleComp CostSpec _)
        apply OnlyC.query
        intro hlong
        rcases h.1 with hshort | hzero
        · exact hshort hlong
        · omega
      · have hnext := h.2 answer
        split at hnext <;> simpa [Short.Only] using hnext

theorem OnlyC.liftProb {α : Type} (oa : ProbComp α) : OnlyC (liftM oa : OracleComp CostSpec α) := by
  induction oa using OracleComp.inductionOn with
  | pure value => exact OnlyC.pure' _
  | query_bind input next ih =>
      rw [liftM_bind]
      refine OnlyC.bind ?_ ih
      change OnlyC (liftM (CostSpec.query (.inl (.inl input))) : OracleComp CostSpec _)
      exact OnlyC.query (fun h => h)

theorem OnlyC.tick (amount : Nat) :
    OnlyC (HiddenCost.tick (D := HashInput) (R := HashOutput) (ι := HiddenGraph.Coordinate) amount) :=
  OnlyC.query (fun h => h)

theorem OnlyC.reveal (coordinate : HiddenGraph.Coordinate) :
    OnlyC (HiddenCost.reveal (D := HashInput) (R := HashOutput) coordinate) :=
  OnlyC.query (fun h => h)

theorem OnlyC.sequenceFin {α : Type} {n : Nat} (computation : Fin n → OracleComp CostSpec α)
    (h : ∀ index, OnlyC (computation index)) : OnlyC (Concrete.sequenceFin computation) := by
  induction n with
  | zero => exact OnlyC.pure' _
  | succ n ih =>
      rw [Concrete.sequenceFin]
      exact OnlyC.bind (h 0) (fun _ => OnlyC.bind (ih _ fun index => h index.succ) (fun _ => OnlyC.pure' _))

theorem OnlyC.writerLift {α : Type} {oa : OracleComp CostSpec α} (h : OnlyC oa) :
    OnlyC (liftM oa : WriterT (QueryLog SigningSpec) (OracleComp CostSpec) α).run := by
  rw [WriterT.run_liftM]
  exact OnlyC.map _ h

theorem Only.search (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : FtsTops) : ∀ attempts start,
    Short.Only (ReferenceChoice.search parameter lay tree leaf message attempts start)
  | 0, _ => Short.Only.pure' _
  | attempts + 1, start => by
      rw [ReferenceChoice.search]
      refine Short.Only.bind (Short.Only.encode _ _ _ _ _ _) (fun found => ?_)
      cases found with
      | none => exact Only.search parameter lay tree leaf message attempts (start + 1)
      | some _ => exact Short.Only.pure' _

theorem onlyC_query_bind {α : Type} {input : CostSpec.Domain} {next : CostSpec.Range input → OracleComp CostSpec α}
    (h : OnlyC (liftM (CostSpec.query input) >>= next)) :
    ¬LongCost input ∧ ∀ value, OnlyC (next value) := by
  rw [OnlyC, isQueryBoundP_query_bind_iff] at h
  refine ⟨fun hlong => ?_, fun value => ?_⟩
  · rcases h.1 with hnot | hzero
    · exact hnot hlong
    · omega
  · have := h.2 value
    split at this <;> simpa [OnlyC] using this

theorem OnlyC.cap {α : Type} {computation : OracleComp CostSpec α} (h : OnlyC computation) (budget : Nat) :
    OnlyC (HiddenCost.cap computation budget) := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value => exact OnlyC.pure' _
  | query_bind input next ih =>
      obtain ⟨hinput, hnext⟩ := onlyC_query_bind h
      rw [Stop.cap_query_bind']
      split
      · exact OnlyC.bind (OnlyC.query hinput) (fun value => ih value (hnext value) _)
      · exact OnlyC.pure' _

theorem OnlyC.trace {α : Type} {computation : OracleComp CostSpec α} (h : OnlyC computation) :
    OnlyC (HiddenCost.trace computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact OnlyC.pure' _
  | query_bind input next ih =>
      obtain ⟨hinput, hnext⟩ := onlyC_query_bind h
      rw [HiddenCost.trace_query_bind]
      exact OnlyC.bind (OnlyC.query hinput) (fun value => OnlyC.map _ (ih value (hnext value)))

theorem OnlyC.erase {α : Type} {computation : OracleComp CostSpec α} (h : OnlyC computation) :
    OnlyShort (HiddenCost.erase computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [OnlyShort, HiddenCost.erase]
  | query_bind input next ih =>
      obtain ⟨hinput, hnext⟩ := onlyC_query_bind h
      have hbind : OnlyShort (HiddenCost.eraseQuery input >>= fun value => HiddenCost.erase (next value)) := by
        have hfirst : OnlyShort (HiddenCost.eraseQuery (D := HashInput) (R := HashOutput)
            (ι := HiddenGraph.Coordinate) input) := by
          rcases input with source | amount
          · change OnlyShort (liftM ((HiddenRows.SourceSpec HashInput HashOutput HiddenGraph.Coordinate).query
              source) : OracleComp _ _)
            rw [OnlyShort, isQueryBoundP_query_iff]
            intro hlong
            rcases source with draw | (bytes | coordinate)
            · exact hlong.elim
            · exact (hinput hlong).elim
            · exact hlong.elim
          · exact (trivial : (pure () : OracleComp (HiddenRows.SourceSpec HashInput HashOutput
              HiddenGraph.Coordinate) Unit).IsQueryBoundP LongSource 0)
        have := isQueryBoundP_bind (n := 0) (m := 0) hfirst (fun value _ => ih value (hnext value))
        simpa [OnlyShort] using this
      simpa only [HiddenCost.erase, simulateQ_bind, simulateQ_spec_query] using hbind

variable [Params]

attribute [local irreducible] ReferenceChoice.search encodingAttemptLimit digestAttemptLimit
  Concrete.messageDigest Concrete.messageDigestCall

theorem OnlyC.finishCostSource (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness) : OnlyC (GraphView.finishCostSource parameter data message randomness) := by
  unfold GraphView.finishCostSource
  refine OnlyC.bind (OnlyC.liftHash (Short.Only.messageDigest _ _ _ _)) (fun digest => ?_)
  refine OnlyC.bind (OnlyC.tick _) (fun _ => ?_)
  refine OnlyC.bind (OnlyC.liftHash (Only.search _ _ _ _ _ _ _)) (fun found => ?_)
  rcases found with _ | ⟨counter, word⟩
  · exact OnlyC.pure' _
  · refine OnlyC.bind (OnlyC.sequenceFin _ fun _ => OnlyC.reveal _) (fun _ => ?_)
    refine OnlyC.bind (OnlyC.sequenceFin _ fun _ => OnlyC.reveal _) (fun _ => ?_)
    exact OnlyC.bind (OnlyC.tick _) (fun _ => OnlyC.pure' _)

theorem OnlyC.signCostSourceWalk (parameter : PublicParameter) (data : PublicData) (message : Message) :
    ∀ attempts randomness,
      OnlyC (GraphView.signCostSourceWalk parameter data message attempts randomness)
  | 0, _ => OnlyC.pure' _
  | attempts + 1, randomness => by
      rw [GraphView.signCostSourceWalk]
      refine OnlyC.bind (OnlyC.liftHash (Short.Only.messageDigestCall _ _ _ _ _)) (fun first => ?_)
      split
      · exact OnlyC.finishCostSource _ _ _ _
      · exact OnlyC.signCostSourceWalk parameter data message attempts (randomness + 1)

theorem OnlyC.signCostSourceLoop (parameter : PublicParameter) (data : PublicData) (message : Message)
    (attempts : Nat) : OnlyC (GraphView.signCostSourceLoop parameter data message attempts) := by
  rw [GraphView.signCostSourceLoop]
  exact OnlyC.bind (OnlyC.liftProb _) (fun _ => OnlyC.signCostSourceWalk _ _ _ _ _)

theorem OnlyC.signCostSource (parameter : PublicParameter) (data : PublicData) (message : Message) :
    OnlyC (GraphView.signCostSource parameter data message) :=
  OnlyC.signCostSourceLoop parameter data message _

theorem OnlyC.costInteraction (parameter : PublicParameter) (data : PublicData) {β : Type}
    (M : OracleComp AdvSpec β) (h : OnlyAdv M) :
    OnlyC (simulateQ (costInteraction parameter data) M).run := by
  induction M using OracleComp.inductionOn with
  | pure value => exact OnlyC.pure' _
  | query_bind input next ih =>
      rw [OnlyAdv, isQueryBoundP_query_bind_iff] at h
      have hnext : ∀ answer, OnlyAdv (next answer) := fun answer => by
        have := h.2 answer
        split at this <;> simpa [OnlyAdv] using this
      rw [simulateQ_bind, WriterT.run_bind]
      refine OnlyC.bind ?_ (fun result => OnlyC.map _ (ih result.1 (hnext result.1)))
      rw [simulateQ_spec_query]
      rcases input with (draw | bytes) | message
      · change OnlyC (liftM (liftM (CostSpec.query (.inl (.inl draw))) : OracleComp CostSpec _) :
          WriterT (QueryLog SigningSpec) (OracleComp CostSpec) _).run
        exact OnlyC.writerLift (OnlyC.query (fun h => h))
      · have hshort : IsShort bytes := by
          rcases h.1 with hnot | hzero
          · simpa [LongAdv] using hnot
          · omega
        change OnlyC (liftM (liftM (CostSpec.query (.inl (.inr (.inl bytes)))) : OracleComp CostSpec _) :
          WriterT (QueryLog SigningSpec) (OracleComp CostSpec) _).run
        exact OnlyC.writerLift (OnlyC.query (fun hlong => hlong hshort))
      · change OnlyC ((QueryImpl.withLogging (spec := SigningSpec) (m := OracleComp CostSpec)
          (fun message => GraphView.signCostSource parameter data message)) message).run
        rw [QueryImpl.run_withLogging_apply]
        exact OnlyC.bind (OnlyC.signCostSource _ _ _) (fun _ => OnlyC.pure' _)

theorem OnlyC.costGame (parameter : PublicParameter) (data : PublicData) (adversary : Adversary) :
    OnlyC (GraphView.costGame parameter data (internalize adversary)) := by
  unfold GraphView.costGame GraphView.costRest
  refine OnlyC.bind (OnlyC.tick _) (fun _ => ?_)
  refine OnlyC.bind ?_ (fun output => ?_)
  · exact OnlyC.costInteraction _ _ _ (OnlyAdv.map _ (OnlyAdv.internal _ _))
  · exact OnlyC.bind (OnlyC.liftHash (Short.Only.verify _ _ _)) (fun _ => OnlyC.pure' _)

end SphincsFors.Security.HiddenBridge
