import FORS.CoverPotential.Game
import FORS.LazyRun.Replay

/-! Shared pieces of the routes that run saturation and the FORS potential on the same lazy run:
the start state, from the stopped experiment to the interpreted run, failing indices of the
prepared encoding searches and their expected share (at most `2^-201`), the prepared cache holding
no message-digest input, and the targeting facts of one prepared sample. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.ForsPotential

variable [Params]

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal FORS.Base.Domination

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable


section Rest

variable (parameter : PublicParameter) (data : PublicData) (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- A FORS cover of a completed run. -/
def CoverOf (out : Run HashInput Coordinate HiddenBridge.Outcome × State) : Prop :=
  ∃ outcome, out.1.1 = some outcome ∧
    HiddenBridge.ForsCover parameter data.root outcome out.1.2.1 out.2.cache

theorem start_pinv (hclean : ∀ p call, initial (pblk parameter data p call) = none)
    (known : Knowledge Coordinate) : PInv parameter data (DebtState.start initial known) [] := by
  have hnone : ∀ p call, (DebtState.start initial known).cache (pblk parameter data p call) = none := by
    intro p call
    change initial (pblk parameter data p call) = none
    exact hclean p call
  have hnot : ∀ p, ¬LandedIn parameter data (DebtState.start initial known) p := by
    rintro p ⟨u, hu, -⟩
    rw [hnone p firstCall] at hu
    cases hu
  exact ⟨List.nodup_nil, fun p => ⟨fun h => absurd h (by simp), fun h => absurd h (hnot p)⟩,
    fun p h => absurd h (hnot p), fun p _ call => hnone p call⟩

theorem start_count (hclean : ∀ p call, initial (pblk parameter data p call) = none) (known : Knowledge Coordinate)
    (budget : ℕ) : CountInv parameter data budget (DebtState.start initial known) budget := by
  intro m
  have : cachedCount parameter data m (DebtState.start initial known) = 0 := by
    unfold cachedCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro ρ _ h
    exact h (hclean (m, ρ) firstCall)
  rw [this, zero_add]

theorem start_prepared (known : Knowledge Coordinate) : Prepared initial (DebtState.start initial known) :=
  fun _ _ h => h

end Rest

section Tick

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- A leading tick only shortens the budget. -/
theorem interp_tick_bind {β : Type} (amount : ℕ) (next : Unit → OracleComp CostSpec β) (budget : ℕ) (s : State)
    (h : amount ≤ budget) :
    interp tg initial model (HiddenCost.tick amount >>= next) budget s =
      (fun out => ((out.1.1, out.1.2.1, Sum.inr amount :: out.1.2.2.1, out.1.2.2.2), out.2)) <$>
        interp tg initial model (next ()) (budget - amount) s := by
  unfold HiddenCost.tick
  rw [interp_query_bind]
  split_ifs with hc
  · change (pure ((), s) : ProbComp _) >>= _ = _
    rw [pure_bind]
    rfl
  · exact absurd h hc

theorem interp_tick_bind_abort {β : Type} (amount : ℕ) (next : Unit → OracleComp CostSpec β) (budget : ℕ) (s : State)
    (h : ¬amount ≤ budget) :
    interp tg initial model (HiddenCost.tick amount >>= next) budget s = pure ((none, [], [], []), s) := by
  unfold HiddenCost.tick
  rw [interp_query_bind]
  split_ifs with hc
  · exact absurd hc h
  · rfl

/-- No hit is decided at the start, and nothing is owed. -/
theorem not_hit_start (known : Knowledge Coordinate) (table : Coordinate → Digest) :
    ¬Hit tg initial table (DebtState.start initial known) := by
  rintro (hr | ⟨c, _, hc⟩)
  · rcases hr with ⟨input, output, value, hcache, hinit, _, _⟩ | ⟨c, v, _, hv⟩
    · change initial input = some output at hcache
      rw [hcache] at hinit; cases hinit
    · rw [debts_start] at hv; exact hv
  · rw [debts_start] at hc; exact hc

end Tick

section Chain

open HiddenBridge Completeness SeedModel Graph Assembly Reduce Internalize

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

theorem agrees_iff_extending (known : Knowledge Coordinate) (table : Coordinate → Digest) :
    Agrees known table ↔ tableExtending known table = table := by
  constructor
  · intro h
    funext c
    simp only [tableExtending]
    cases hc : known c with
    | none => rfl
    | some v => exact (h c v hc).symm
  · intro h c v hc
    rw [← h]
    simp [tableExtending, hc]

/-- The weakened bad event of one table. -/
def badFor (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (results : OtsKey → Option (Counter × Encoding)) (table : Coordinate → Digest)
    (v : ((Option HiddenBridge.Outcome × List Coordinate) × List (Entry HashInput)) × QueryCache HashSpec) : Prop :=
  CacheMatch.Bad (TargetAssignment.targets (truncateHash parameterOutput)
      (compTable parameterOutput fixed highs remaining table results)) v.2 ∨
    ∃ outcome, v.1.1.1 = some outcome ∧
      ForsCover (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining).root outcome v.1.1.2 v.2

/-- One table: the stopped run against the comparison run. -/
theorem stopped_table_le (hb : 0 < keptHeight topLayer) (adversary : Adversary) (q : ℕ) (hq : q < 2 ^ 256)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (steps : Message → Randomness)
    (prepared : (OtsKey → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (table : Coordinate → Digest) (hagree : Agrees (knownOf (truncateHash parameterOutput) fixed) table) :
    Pr[HiddenReveal.StopOr RichWin | HiddenOutside.stopped (sampleModel parameterOutput highs) table
        (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
          (sampleData parameterOutput fixed highs remaining steps))))
        (knownOf (truncateHash parameterOutput) fixed) prepared.2] ≤
      Pr[fun r => CorrectGuess table r.2 ∨
          badFor parameterOutput fixed highs remaining prepared.1 table (r.1, r.2.cache) |
        fixedRun (sampleModel parameterOutput highs) table
          (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
            (sampleData parameterOutput fixed highs remaining steps))))
          (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed))] := by
  have htable := (agrees_iff_extending _ table).1 hagree
  refine le_trans (probEvent_mono fun r hr hwin => ?_)
    (stopped_le_fixedRun (sampleModel parameterOutput highs) table _ _
      (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed)) hagree)
  rcases r with _ | ⟨⟨⟨res, reveals⟩, entries⟩, cacheF⟩
  · trivial
  · obtain ⟨outcome, hres, hw⟩ := hwin
    simp only at hres
    subst hres
    rcases win_implies_bad hb adversary q hq parameterOutput fixed highs remaining steps prepared hprepared table htable
      outcome reveals entries cacheF hr hw with h | h
    · exact Or.inl h
    · exact Or.inr ⟨outcome, rfl, h⟩

set_option maxRecDepth 100000 in
/-- **From the stopped experiment to the interpreted run.** -/
theorem stopped_le_interp (hb : 0 < keptHeight topLayer) (adversary : Adversary) (q : ℕ) (hq : q < 2 ^ 256)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (steps : Message → Randomness)
    (prepared : (OtsKey → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (tg : Targeting HashInput HashOutput Coordinate) :
    Pr[HiddenReveal.StopOr RichWin | HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
        (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
          (sampleData parameterOutput fixed highs remaining steps))))
        (knownOf (truncateHash parameterOutput) fixed) prepared.2] ≤
      Pr[fun x => CorrectGuess x.1 x.2.2 ∨
          badFor parameterOutput fixed highs remaining prepared.1 x.1 (((x.2.1.1, x.2.1.2.1), x.2.1.2.2.1), x.2.2.cache) |
        interp tg prepared.2 (sampleModel parameterOutput highs)
          (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps)
            (internalize adversary)) q (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed)) >>=
          fun result => (fun table => (table, result)) <$> completion result.2.known] := by
  unfold HiddenOutside.stoppedExperiment
  rw [probEvent_bind_eq_tsum]
  calc _ ≤ ∑' table, Pr[= table | completion (knownOf (truncateHash parameterOutput) fixed)] *
        Pr[fun r => CorrectGuess table r.2 ∨
            badFor parameterOutput fixed highs remaining prepared.1 table (r.1, r.2.cache) |
          fixedRun (sampleModel parameterOutput highs) table
            (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
              (sampleData parameterOutput fixed highs remaining steps))))
            (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed))] := by
        refine ENNReal.tsum_le_tsum fun table => ?_
        by_cases htab : table ∈ support (completion (knownOf (truncateHash parameterOutput) fixed))
        · have hag : Agrees (knownOf (truncateHash parameterOutput) fixed) table := by
            unfold completion at htab
            rw [support_map] at htab
            obtain ⟨t, _, rfl⟩ := htab
            exact fun c v hc => completion_known _ c v hc t
          have := stopped_table_le hb adversary q hq parameterOutput fixed highs remaining steps prepared
            hprepared table hag
          exact mul_le_mul_right this _
        · rw [probOutput_eq_zero_of_not_mem_support htab, zero_mul, zero_mul]
    _ = Pr[fun x => CorrectGuess x.1 x.2.2 ∨
            badFor parameterOutput fixed highs remaining prepared.1 x.1 (x.2.1, x.2.2.cache) |
          withTable (fun table => fixedRun (sampleModel parameterOutput highs) table
            (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
              (sampleData parameterOutput fixed highs remaining steps))))
            (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed)))
            (knownOf (truncateHash parameterOutput) fixed)] := by
        unfold withTable
        rw [probEvent_bind_eq_tsum]
        refine tsum_congr fun table => ?_
        rw [probEvent_map]
        rfl
    _ = Pr[fun x => CorrectGuess x.1 x.2.2 ∨
            badFor parameterOutput fixed highs remaining prepared.1 x.1 (x.2.1, x.2.2.cache) |
          lazyRun (sampleModel parameterOutput highs)
            (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
              (sampleData parameterOutput fixed highs remaining steps))))
            (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed)) >>= fun result =>
              (fun table => (table, result)) <$> completion result.2.known] :=
        probEvent_congr' (fun _ _ => Iff.rfl) (withTable_fixedRun _ _ _)
    _ = _ := by
        unfold richProgram
        rw [lazyRun_wrapped tg prepared.2]
        have hcomp : ((fun out : Run HashInput Coordinate HiddenBridge.Outcome × State =>
              (((out.1.1, out.1.2.1), out.1.2.2.1), out.2)) <$>
            interp tg prepared.2 (sampleModel parameterOutput highs)
              (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps)
                (internalize adversary)) q (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed))) >>=
              (fun result => (fun table => (table, result)) <$> completion result.2.known) =
            (fun x : (Coordinate → Digest) × (Run HashInput Coordinate HiddenBridge.Outcome × State) =>
              (x.1, (((x.2.1.1, x.2.1.2.1), x.2.1.2.2.1), x.2.2))) <$>
            (interp tg prepared.2 (sampleModel parameterOutput highs)
              (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps)
                (internalize adversary)) q (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed)) >>=
              fun result => (fun table => (table, result)) <$> completion result.2.known) := by
          rw [bind_map_left, map_bind]
          refine bind_congr fun out => ?_
          rw [Functor.map_map]
        rw [hcomp, probEvent_map]
        rfl

/-- Keygen cost credited before the adversary runs. -/
abbrev keygenCost : ℕ := Prefix.keygenHashCost

end Chain

/-! ### Failing indices of the prepared searches -/

section FailSet

open HiddenBridge Completeness SeedModel Graph Assembly Reduce Internalize

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

theorem noQ_bind {bad : HashInput → Prop} [DecidablePred bad] {α β : Type} {oa : OracleComp HashSpec α}
    {next : α → OracleComp HashSpec β} (h : oa.IsQueryBoundP bad 0)
    (hnext : ∀ value, (next value).IsQueryBoundP bad 0) : (oa >>= next).IsQueryBoundP bad 0 := by
  have := isQueryBoundP_bind (n := 0) (m := 0) h (fun value _ => hnext value)
  simpa using this

/-- The encoding search queries only encoding inputs. -/
theorem noQ_search {bad : HashInput → Prop} [DecidablePred bad]
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : HashInput)
    (hbad : ∀ payload, ¬bad (tweakableHashInput parameter (.encoding lay tree leaf) payload)) :
    ∀ attempts start, (ReferenceChoice.search parameter lay tree leaf message attempts start :
      OracleComp HashSpec (Option (Counter × Encoding))).IsQueryBoundP bad 0
  | 0, _ => trivial
  | attempts + 1, start => by
      rw [ReferenceChoice.search]
      refine noQ_bind ?_ fun found => ?_
      · unfold Concrete.encode Concrete.tweakableHash
        refine noQ_bind (noQ_bind ?_ fun _ => trivial) fun _ => trivial
        simp only [oracleHash, HasQuery.query]
        rw [isQueryBoundP_query_iff]
        exact fun hm => absurd hm (hbad _)
      · cases found with
        | none => exact noQ_search parameter lay tree leaf message hbad attempts (start + 1)
        | some _ => trivial

/-- Encoding inputs are not hidden rows. -/
theorem not_row_encoding (parameterOutput : HashOutput) (highs : CoordinateHighs) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (payload : HashInput) :
    (sampleModel parameterOutput highs).parse (tweakableHashInput parameter (.encoding lay tree leaf) payload) = none := by
  rw [sampleModel_parse]
  cases h : HiddenGraph.parse (truncateHash parameterOutput) (candidateActive (truncateHash parameterOutput))
      (tweakableHashInput parameter (.encoding lay tree leaf) payload) with
  | none => rfl
  | some query =>
      obtain ⟨heq, _⟩ := (HiddenGraph.parse_some_iff _ _ _ query).1 h
      have hfields := (tweakableInput_injective heq).1
      have htag := congrArg TweakFields.tag hfields
      rcases query with ⟨address, value⟩
      cases address <;> simp [Address.position, Position.domain, hashDomainFields, tweakFields, treeFields] at htag

/-- Every prepared search result was recorded inside the prepared cache. -/
theorem preparation_parts (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (prepared : (OtsKey → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining)) (key : OtsKey) :
    ∃ c0, ∃ r ∈ support ((simulateQ (randomOracle (spec := HashSpec))
        (ReferenceChoice.search (truncateHash parameterOutput) key.1 key.2.1 key.2.2
          (keyMessages (sampleData parameterOutput fixed highs remaining) key) encodingAttemptLimit 0)).run c0),
      r.1 = prepared.1 key ∧ ∀ x v, r.2 x = some v → prepared.2 x = some v := by
  have hrun := hprepared
  unfold preparation searchAll at hrun
  simp only [simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion, simulateQ_pure, StateT.run_pure,
    support_pure, Set.mem_singleton_iff] at hrun
  obtain ⟨res, hres, rfl⟩ := hrun
  obtain ⟨c1, r1, hr1, h11, h12⟩ := sequenceFin_parts (D := HashInput) (R := HashOutput) _ _ res hres key.1
  obtain ⟨c2, r2, hr2, h21, h22⟩ := sequenceFin_parts (D := HashInput) (R := HashOutput) _ _ r1 hr1 key.2.1
  obtain ⟨c3, r3, hr3, h31, h32⟩ := sequenceFin_parts (D := HashInput) (R := HashOutput) _ _ r2 hr2 key.2.2
  refine ⟨c3, r3, hr3, ?_, fun x v hx => h12 x v (h22 x v (h32 x v hx))⟩
  rw [h31, h21, h11]

/-- Local indices of some index one of whose prepared searches failed. -/
noncomputable def failSet (results : OtsKey → Option (Counter × Encoding)) : Finset (Fin (2 ^ subtreeHeight)) :=
  Finset.univ.filter fun l => ∃ i : Index, ForsPotential.localIdx i = l ∧ ∃ lay, results (keyAt i lay) = none

section Dep

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- A sequence of searches that fails under the interpreter has a failing step. -/
theorem interp_sequenceDep_none (Inv : State → Prop) : ∀ {n : ℕ} {α : Fin n → Type}
    (computation : (i : Fin n) → OracleComp CostSpec (Option (α i))) (Bad : Fin n → Prop),
    (∀ i budget s, Inv s → ∀ out ∈ support (interp tg initial model (computation i) budget s), Inv out.2) →
    (∀ i budget s, Inv s → ∀ out ∈ support (interp tg initial model (computation i) budget s),
      out.1.1 = some none → Bad i) →
    ∀ budget s, Inv s → ∀ out ∈ support (interp tg initial model (sequenceDep computation) budget s),
      out.1.1 = some none → ∃ i, Bad i
  | 0, _, _, _, _, _, budget, s, _, out, hout, hnone => by
      change out ∈ support (interp tg initial model (pure _) budget s) at hout
      rw [interp_pure, support_pure, Set.mem_singleton_iff] at hout
      rw [hout] at hnone
      cases hnone
  | _ + 1, α, computation, Bad, hinv, hbad, budget, s, hs, out, hout, hnone => by
      unfold sequenceDep at hout
      obtain ⟨o1, ho1, h1⟩ := interp_bind_mem tg initial model _ _ budget s out hout
      rcases h1 with ⟨_, hn, _⟩ | ⟨v, hv, o2, ho2, hres2, _, _⟩
      · rw [hnone] at hn; cases hn
      rcases v with _ | head
      · exact ⟨0, hbad 0 budget s hs o1 ho1 hv⟩
      obtain ⟨o3, ho3, h3⟩ := interp_bind_mem tg initial model _ _ _ _ o2 ho2
      rcases h3 with ⟨_, hn, _⟩ | ⟨w, hw, o4, ho4, hres4, _, _⟩
      · rw [hres2, hn] at hnone; cases hnone
      rcases w with _ | tail
      · obtain ⟨i, hi⟩ := interp_sequenceDep_none Inv (α := fun i => α i.succ) (fun i => computation i.succ)
          (fun i => Bad i.succ) (fun i => hinv i.succ) (fun i => hbad i.succ) _ o1.2
          (hinv 0 budget s hs o1 ho1) o3 ho3 hw
        exact ⟨i.succ, hi⟩
      · change o4 ∈ support (interp tg initial model (pure _) _ _) at ho4
        rw [interp_pure, support_pure, Set.mem_singleton_iff] at ho4
        rw [hres2, hres4, ho4] at hnone
        cases hnone

end Dep

/-- **A failed layer search is a failed prepared search.** -/
theorem layerCostSearch_fail (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (steps : Message → Randomness)
    (prepared : (OtsKey → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (tg : Targeting HashInput HashOutput Coordinate) (index : Index) (lay : Layer)
    (budget : ℕ) (s1 : State) (hprep : Prepared prepared.2 s1)
    (out : Run HashInput Coordinate (Option (Counter × Encoding)) × State)
    (hout : out ∈ support (interp tg prepared.2 (sampleModel parameterOutput highs)
      (layerCostSearch (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps)
        index lay) budget s1))
    (hnone : out.1.1 = some none) : prepared.1 (keyAt index lay) = none := by
  set model := sampleModel parameterOutput highs
  unfold layerCostSearch at hout
  obtain ⟨o1, ho1, h1⟩ := interp_bind_mem tg prepared.2 model _ _ budget s1 out hout
  rcases h1 with ⟨_, hn, _⟩ | ⟨_, _, o2, ho2, hres2, _, _⟩
  · rw [hnone] at hn; cases hn
  have hext1 := interp_extends tg prepared.2 model _ budget s1 o1 ho1
  obtain ⟨o3, ho3, h3⟩ := interp_bind_mem tg prepared.2 model _ _ _ _ o2 ho2
  rcases h3 with ⟨_, hn, _⟩ | ⟨found, hfound, o4, ho4, hres4, _, _⟩
  · rw [hres2, hn] at hnone; cases hnone
  rcases found with _ | pair
  · obtain ⟨c0, r, hr, hr1, hr2⟩ := preparation_parts parameterOutput fixed highs remaining prepared hprepared
      (keyAt index lay)
    have ho3' : o3 ∈ support (interp tg prepared.2 model
        (liftM (ReferenceChoice.search (truncateHash parameterOutput) lay (treeIndexAt index lay)
          (leafIndexAt index lay) (keyMessages (sampleData parameterOutput fixed highs remaining) (keyAt index lay))
          encodingAttemptLimit 0) : OracleComp CostSpec _) (budget - traceCost o1.1.2.2.1) o1.2) := ho3
    have hrow := noQ_search (bad := fun x => model.parse x ≠ none)
      (truncateHash parameterOutput) lay (treeIndexAt index lay) (leafIndexAt index lay)
      (keyMessages (sampleData parameterOutput fixed highs remaining) (keyAt index lay))
      (fun payload h => h (not_row_encoding parameterOutput highs _ _ _ _ payload)) encodingAttemptLimit 0
    have hstep := interp_liftHash_replay (D := HashInput) (R := HashOutput) tg prepared.2 model
      (ReferenceChoice.search (truncateHash parameterOutput) lay (treeIndexAt index lay) (leafIndexAt index lay)
        (keyMessages (sampleData parameterOutput fixed highs remaining) (keyAt index lay)) encodingAttemptLimit 0 :
          OracleComp HashSpec (Option (Counter × Encoding)))
    have hreplay := hstep hrow c0 r hr _ o1.2 (fun x v hx => hext1.1 x v (hprep x v (hr2 x v hx))) o3 ho3'
      none hfound
    rw [← hr1, ← hreplay]
  · exfalso
    have hmem := interp_result_mem tg prepared.2 model _ _ _ o4 ho4 none (by rw [← hres4, ← hres2, hnone])
    revert hmem
    dsimp only
    intro hmem
    refine post_bind (fun v => v ≠ none) _ (fun _ => ?_) none hmem rfl
    intro v hv
    rw [support_pure, Set.mem_singleton_iff] at hv
    rw [hv]
    exact fun h => by cases h

/-- **A failed final assembly is at a failing index.** -/
theorem finishRest_fail (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (steps : Message → Randomness)
    (prepared : (OtsKey → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (tg : Targeting HashInput HashOutput Coordinate) (m : Message) (ρ : Randomness) (digest : MessageDigest)
    (budget : ℕ) (s1 : State) (hprep : Prepared prepared.2 s1)
    (out : Run HashInput Coordinate (Option Signature) × State)
    (hout : out ∈ support (interp tg prepared.2 (sampleModel parameterOutput highs)
      (finishRest (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps) m ρ digest) budget s1))
    (hnone : out.1.1 = some none) :
    (Lifetime.localDigestView digest).1 ∈ failSet prepared.1 := by
  set model := sampleModel parameterOutput highs
  rw [localDigestView_fst]
  unfold failSet
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, digestIndex digest, rfl, ?_⟩
  unfold finishRest at hout
  obtain ⟨o1, ho1, h1⟩ := interp_bind_mem tg prepared.2 model _ _ budget s1 out hout
  rcases h1 with ⟨_, hn, _⟩ | ⟨_, _, o2, ho2, hres2, _, _⟩
  · rw [hnone] at hn; cases hn
  have hext1 := interp_extends tg prepared.2 model _ budget s1 o1 ho1
  obtain ⟨o3, ho3, h3⟩ := interp_bind_mem tg prepared.2 model _ _ _ _ o2 ho2
  rcases h3 with ⟨_, hn, _⟩ | ⟨found, hfound, o4, ho4, hres4, _, _⟩
  · rw [hres2, hn] at hnone; cases hnone
  rcases found with _ | found
  · exact interp_sequenceDep_none tg prepared.2 model (Prepared prepared.2)
      (layerCostSearch (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps)
        (digestIndex digest))
      (fun lay => prepared.1 (keyAt (digestIndex digest) lay) = none)
      (fun lay budget s hs out hout x v hx =>
        (interp_extends tg prepared.2 model _ budget s out hout).1 x v (hs x v hx))
      (fun lay budget s hs out hout hnone => layerCostSearch_fail parameterOutput fixed highs remaining steps
        prepared hprepared tg (digestIndex digest) lay budget s hs out hout hnone)
      _ o1.2 (fun x v hx => hext1.1 x v (hprep x v hx)) o3 ho3 hfound
  · exfalso
    have hmem := interp_result_mem tg prepared.2 model _ _ _ o4 ho4 none (by rw [← hres4, ← hres2, hnone])
    revert hmem
    dsimp only
    intro hmem
    refine post_bind (fun v => v ≠ none) _ (fun _ => post_bind _ _ fun _ => ?_) none hmem rfl
    intro v hv
    rw [support_pure, Set.mem_singleton_iff] at hv
    rw [hv]
    exact fun h => by cases h

end FailSet

/-! ### All samples -/

section Total

open HiddenBridge Completeness SeedModel Graph Assembly Reduce Internalize

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

/-- A bound per sample, averaged. -/
theorem tsum_bound_le {α : Type} (mx : ProbComp α) (g : α → ℝ≥0∞) (A C : ℝ≥0∞) (φ : α → ℝ≥0∞)
    (h : ∀ x ∈ support mx, g x ≤ A + C * φ x) :
    ∑' x, Pr[= x | mx] * g x ≤ A + C * ∑' x, Pr[= x | mx] * φ x := by
  calc ∑' x, Pr[= x | mx] * g x ≤ ∑' x, Pr[= x | mx] * (A + C * φ x) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support mx
        · exact mul_le_mul_right (h x hx) _
        · rw [probOutput_eq_zero_of_not_mem_support hx, zero_mul, zero_mul]
    _ = (∑' x, Pr[= x | mx]) * A + C * ∑' x, Pr[= x | mx] * φ x := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, mul_left_comm _ C, ENNReal.tsum_mul_left]
    _ ≤ A + C * ∑' x, Pr[= x | mx] * φ x := add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) le_rfl

/-- Expected share of failing indices over the samples and their preparations. -/
noncomputable def expectedFail : ℝ≥0∞ :=
  ∑' parameterOutput, Pr[= parameterOutput | ($ᵗ HashOutput : ProbComp HashOutput)] *
  ∑' fixed, Pr[= fixed | ($ᵗ HiddenGraph.Table : ProbComp HiddenGraph.Table)] *
  ∑' highs, Pr[= highs | ($ᵗ CoordinateHighs : ProbComp CoordinateHighs)] *
  ∑' remaining, Pr[= remaining | ($ᵗ RemainingOutputs : ProbComp RemainingOutputs)] *
  ∑' prepared, Pr[= prepared | preparation parameterOutput fixed highs remaining] *
    failMass (failSet prepared.1)

end Total

/-! ### The prepared cache holds no message-digest input -/

section Clean

open HiddenBridge Completeness SeedModel Graph Assembly Reduce Internalize

theorem noQ_sequenceFin {bad : HashInput → Prop} [DecidablePred bad] {α : Type} :
    ∀ {n : ℕ} (f : Fin n → OracleComp HashSpec α), (∀ i, (f i).IsQueryBoundP bad 0) →
      (Concrete.sequenceFin f).IsQueryBoundP bad 0
  | 0, _, _ => trivial
  | n + 1, f, h => by
      unfold Concrete.sequenceFin
      exact noQ_bind (h 0) fun _ => noQ_bind (noQ_sequenceFin (fun i : Fin n => f i.succ) fun i => h i.succ)
        fun _ => trivial

theorem msg_not_graph (parameter : PublicParameter) (position : Position) (payload x : HashInput)
    (hx : IsMsgInput x) : x ≠ tweakableHashInput parameter position.domain payload := by
  obtain ⟨p', call', payload', rfl⟩ := hx
  intro heq
  have htag := congrArg TweakFields.tag (tweakableInput_injective heq).1
  cases position <;> simp [Position.domain, hashDomainFields, tweakFields, treeFields] at htag

/-- **The prepared cache holds no message-digest input.** -/
theorem prepared_clean (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (prepared : (OtsKey → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining)) :
    ∀ x, IsMsgInput x → prepared.2 x = none := by
  intro x hx
  have hrun : prepared ∈ support ((simulateQ (randomOracle (spec := HashSpec))
      (searchAll (truncateHash parameterOutput) (keyMessages (sampleData parameterOutput fixed highs remaining)))).run
      (structCache (splitMaterial parameterOutput highs remaining fixed) (splitAnswers highs remaining fixed))) :=
    hprepared
  have hnoQ : (searchAll (truncateHash parameterOutput)
      (keyMessages (sampleData parameterOutput fixed highs remaining))).IsQueryBoundP IsMsgInput 0 := by
    unfold searchAll
    exact noQ_bind (noQ_sequenceFin _ fun lay => noQ_sequenceFin _ fun tree => noQ_sequenceFin _ fun leaf =>
      noQ_search (bad := IsMsgInput) _ _ _ _ _
        (fun payload => not_msg_tweakable _ _ payload (by simp [hashDomainFields, treeFields])) _ _)
      fun _ => trivial
  rw [randomOracle_run_avoid (P := IsMsgInput) _ hnoQ _ prepared hrun x hx]
  unfold structCache
  exact programGraphCache_empty_none _ _ _ _ _ x fun position _ => msg_not_graph _ position _ x hx

end Clean

/-! ### Few prepared searches fail -/

section FailBound

open HiddenBridge Completeness SeedModel Graph Assembly Reduce Internalize

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

theorem search_eq_searchLoop (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : HashInput) : ∀ (n t : ℕ),
    (ReferenceChoice.search parameter lay tree leaf message n t : OracleComp HashSpec (Option (Counter × Encoding))) =
      searchLoop (fun c => tweakableHashInput parameter (.encoding lay tree leaf)
          (message ++ bytesLE 4 (BitVec.ofNat counterBits c)))
        (fun out => TargetSum.decodeDigest (truncateHash out))
        (fun c encoding => pure (BitVec.ofNat counterBits c, encoding)) n t := by
  intro n
  induction n with
  | zero => intro t; rfl
  | succ n ih =>
      intro t
      rw [ReferenceChoice.search, searchLoop]
      simp only [encode, tweakableHash, oracleHash, bind_assoc, pure_bind, map_eq_bind_pure_comp,
        Function.comp_def, ih]
      refine bind_congr fun answer => ?_
      cases TargetSum.decodeDigest (truncateHash answer) <;> rfl

/-- One search over fresh counters fails with at most the rejection share to the trial budget. -/
theorem search_fail_le (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : HashInput) (cache : QueryCache HashSpec)
    (hfresh : ∀ s, s < encodingAttemptLimit → cache (encodeInput parameter lay tree leaf message s) = none) :
    Pr[fun r => r.1 = none | (simulateQ (randomOracle (spec := HashSpec))
        (ReferenceChoice.search parameter lay tree leaf message encodingAttemptLimit 0)).run cache] ≤
      Completeness.failMass (fun out => TargetSum.decodeDigest (truncateHash out)) ^ encodingAttemptLimit := by
  rw [search_eq_searchLoop]
  exact probEvent_searchLoop _ _ _ encodingAttemptLimit
    (fun s s' hs hs' heq => encodeInput_inj parameter lay tree leaf message hs hs' heq)
    encodingAttemptLimit 0 (by simp) cache (fun s _ hsb => hfresh s hsb)

theorem encoding_not_graph (parameter parameter' : PublicParameter) (position : Position) (payload payload' : HashInput)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    tweakableHashInput parameter' (.encoding lay tree leaf) payload' ≠
      tweakableHashInput parameter position.domain payload := by
  intro heq
  have htag := congrArg TweakFields.tag (tweakableInput_injective heq).1
  cases position <;> simp [Position.domain, hashDomainFields, tweakFields, treeFields] at htag

/-- **One prepared search fails rarely.** -/
theorem prep_fail_le (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (key : OtsKey) :
    Pr[fun prepared => prepared.1 key = none | preparation parameterOutput fixed highs remaining] ≤
      Completeness.failMass (fun out => TargetSum.decodeDigest (truncateHash out)) ^ encodingAttemptLimit := by
  have hrw : preparation parameterOutput fixed highs remaining =
      (fun r => ((fun key : OtsKey => r.1 key.1 key.2.1 key.2.2), r.2)) <$>
        (simulateQ (randomOracle (spec := HashSpec)) (Concrete.sequenceFin fun lay : Layer =>
          Concrete.sequenceFin fun tree : TreeIndex => Concrete.sequenceFin fun leaf : LeafIndex =>
            ReferenceChoice.search (truncateHash parameterOutput) lay tree leaf
              (keyMessages (sampleData parameterOutput fixed highs remaining) (lay, tree, leaf))
              encodingAttemptLimit 0)).run
          (structCache (splitMaterial parameterOutput highs remaining fixed) (splitAnswers highs remaining fixed)) := by
    unfold preparation searchAll
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure]
    rw [map_eq_bind_pure_comp]
    rfl
  rw [hrw, probEvent_map]
  let Bad : HashInput → Prop := fun x => ∃ t, x = encodeInput (truncateHash parameterOutput) key.1 key.2.1 key.2.2
    (keyMessages (sampleData parameterOutput fixed highs remaining) key) t
  let Inv : QueryCache HashSpec → Prop := fun c => ∀ s, s < encodingAttemptLimit →
    c (encodeInput (truncateHash parameterOutput) key.1 key.2.1 key.2.2
      (keyMessages (sampleData parameterOutput fixed highs remaining) key) s) = none
  have hnoQ : ∀ lay tree leaf, (lay, tree, leaf) ≠ key →
      (ReferenceChoice.search (truncateHash parameterOutput) lay tree leaf
        (keyMessages (sampleData parameterOutput fixed highs remaining) (lay, tree, leaf)) encodingAttemptLimit 0 :
          OracleComp HashSpec _).IsQueryBoundP Bad 0 :=
    fun lay tree leaf hne => noQ_search _ _ _ _ _
      (fun payload ⟨t, ht⟩ => hne (encoding_fields_injective (key := (lay, tree, leaf)) (key' := key)
        (tweakableInput_injective ht).1)) _ _
  have hkeep : ∀ {α : Type} (c : OracleComp HashSpec α), c.IsQueryBoundP Bad 0 →
      ∀ cache, Inv cache → ∀ r ∈ support ((simulateQ (randomOracle (spec := HashSpec)) c).run cache), Inv r.2 := by
    intro α c hc cache hcache r hr s hs
    rw [randomOracle_run_avoid (P := Bad) c hc cache r hr _ ⟨s, rfl⟩]
    exact hcache s hs
  refine sequenceFin_prob (D := HashInput) (R := HashOutput) Inv
    (fun found : TreeIndex → LeafIndex → Option (Counter × Encoding) => found key.2.1 key.2.2 = none) _ _ key.1 ?_ ?_ _ ?_
  · intro j hj c hc r hr
    exact hkeep _ (noQ_sequenceFin _ fun tree => noQ_sequenceFin _ fun leaf =>
      hnoQ j tree leaf fun h => hj (congrArg Prod.fst h)) c hc r hr
  · intro c hc
    refine sequenceFin_prob (D := HashInput) (R := HashOutput) Inv
      (fun found : LeafIndex → Option (Counter × Encoding) => found key.2.2 = none) _ _ key.2.1 ?_ ?_ c hc
    · intro j hj c hc r hr
      exact hkeep _ (noQ_sequenceFin _ fun leaf =>
        hnoQ key.1 j leaf fun h => hj (congrArg (fun k : OtsKey => k.2.1) h)) c hc r hr
    · intro c hc
      refine sequenceFin_prob (D := HashInput) (R := HashOutput) Inv
        (fun found : Option (Counter × Encoding) => found = none) _ _ key.2.2 ?_ ?_ c hc
      · intro j hj c hc r hr
        exact hkeep _ (hnoQ key.1 key.2.1 j fun h => hj (congrArg (fun k : OtsKey => k.2.2) h)) c hc r hr
      · intro c hc
        exact search_fail_le _ key.1 key.2.1 key.2.2 _ c hc
  · intro s _
    unfold structCache
    exact programGraphCache_empty_none _ _ _ _ _ _ fun position _ => encoding_not_graph _ _ position _ _ _ _ _

/-- Bernoulli: `(1 - 2⁻¹⁴) ^ 2¹⁴ ≤ 1/2`. -/
theorem one_sub_pow_le_half : (1 - (2 : ℝ)⁻¹ ^ 14) ^ (2 ^ 14) ≤ 1 / 2 := by
  set a : ℝ := (2 : ℝ)⁻¹ ^ 14 with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by rw [ha]; norm_num
  have hbern : 1 + ((2 ^ 14 : ℕ) : ℝ) * a ≤ (1 + a) ^ (2 ^ 14) := one_add_mul_le_pow (by linarith) _
  have hna : ((2 ^ 14 : ℕ) : ℝ) * a = 1 := by rw [ha]; norm_num
  rw [hna] at hbern
  have hprod : (1 - a) ^ (2 ^ 14) * (1 + a) ^ (2 ^ 14) ≤ 1 := by
    rw [← mul_pow]
    have h0 : 0 ≤ (1 - a) * (1 + a) := mul_nonneg (by linarith) (by linarith)
    have h1 : (1 - a) * (1 + a) ≤ 1 := by nlinarith
    exact pow_le_one₀ h0 h1
  have hpos : 0 < (1 + a) ^ (2 ^ 14) := by positivity
  rw [div_eq_mul_inv, one_mul]
  calc (1 - a) ^ (2 ^ 14) = (1 - a) ^ (2 ^ 14) * (1 + a) ^ (2 ^ 14) / (1 + a) ^ (2 ^ 14) := by
        field_simp
    _ ≤ 1 / (1 + a) ^ (2 ^ 14) := by gcongr
    _ ≤ 1 / 2 := by gcongr; exact (by norm_num : (2 : ℝ) ≤ 1 + 1).trans hbern
    _ = 2⁻¹ := by norm_num

/-- The trial budget makes a prepared search fail with negligible probability. -/
theorem fail_pow_le :
    Completeness.failMass (fun out => TargetSum.decodeDigest (truncateHash out)) ^ encodingAttemptLimit ≤
      (2 : ℝ≥0∞)⁻¹ ^ (2 ^ 18) := by
  set fm := Completeness.failMass (fun out => TargetSum.decodeDigest (truncateHash out)) with hfm
  have hadd := Completeness.failMass_encoding_add_le
  have hle : fm ≤ ENNReal.ofReal (1 - (2 : ℝ)⁻¹ ^ 14) := by
    have htop : ((2 : ℝ≥0∞) ^ 14)⁻¹ ≠ ⊤ := by simp
    have h1 : fm ≤ 1 - ((2 : ℝ≥0∞) ^ 14)⁻¹ := ENNReal.le_sub_of_add_le_right htop hadd
    refine h1.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]
    congr 1
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.inv_pow]
  calc fm ^ encodingAttemptLimit ≤ ENNReal.ofReal (1 - (2 : ℝ)⁻¹ ^ 14) ^ (2 ^ 14 * 2 ^ 18) := by
        rw [show encodingAttemptLimit = 2 ^ 14 * 2 ^ 18 from rfl]
        exact pow_le_pow_left' hle _
    _ = (ENNReal.ofReal ((1 - (2 : ℝ)⁻¹ ^ 14) ^ (2 ^ 14))) ^ (2 ^ 18) := by
        rw [pow_mul, ENNReal.ofReal_pow (by norm_num)]
    _ ≤ (ENNReal.ofReal (1 / 2)) ^ (2 ^ 18) := pow_le_pow_left' (ENNReal.ofReal_le_ofReal one_sub_pow_le_half) _
    _ = (2 : ℝ≥0∞)⁻¹ ^ (2 ^ 18) := by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]

theorem failMass_le_count (R : OtsKey → Option (Counter × Encoding)) :
    failMass (failSet R) ≤ ∑ i : OtsKey, (R i).elim (1 : ℝ≥0∞) fun _ => 0 := by
  by_cases h : ∃ i, R i = none
  · obtain ⟨i, hi⟩ := h
    calc failMass (failSet R) ≤ 1 := by
          unfold failMass
          calc _ ≤ freshAvg Finset.univ (fun _ : View => (1 : ℝ≥0∞)) :=
                freshAvg_mono _ fun v _ => by split_ifs <;> simp
            _ = 1 := freshAvg_const _ Finset.univ_nonempty 1
      _ = (R i).elim (1 : ℝ≥0∞) fun _ => 0 := by rw [hi]; rfl
      _ ≤ _ := Finset.single_le_sum (f := fun i : OtsKey => (R i).elim (1 : ℝ≥0∞) fun _ => 0)
          (fun _ _ => bot_le) (Finset.mem_univ i)
  · push Not at h
    have hempty : failSet R = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun l hl => ?_
      obtain ⟨i, _, lay, hi⟩ := (Finset.mem_filter.1 hl).2
      exact h _ hi
    rw [hempty]
    unfold failMass freshAvg
    simp only [Finset.notMem_empty, if_false, Finset.sum_const_zero, mul_zero]
    exact bot_le

theorem tsum_elim_le {β : Type} (mx : ProbComp ((OtsKey → Option β) × QueryCache HashSpec)) (i : OtsKey) :
    ∑' x, Pr[= x | mx] * (x.1 i).elim (1 : ℝ≥0∞) (fun _ => 0) ≤ Pr[fun x => x.1 i = none | mx] := by
  rw [probEvent_eq_tsum_indicator]
  refine ENNReal.tsum_le_tsum fun x => ?_
  cases hx : x.1 i with
  | none =>
      rw [Set.indicator_of_mem (show x ∈ {x | x.1 i = none} from hx)]
      simp
  | some v => simp

/-- **Expected share of failing indices.** -/
theorem expectedFail_le : expectedFail ≤ (2 : ℝ≥0∞)⁻¹ ^ 201 := by
  have hinner : ∀ parameterOutput fixed highs remaining,
      ∑' prepared, Pr[= prepared | preparation parameterOutput fixed highs remaining] *
        failMass (failSet prepared.1) ≤ (2 : ℝ≥0∞)⁻¹ ^ 201 := by
    intro parameterOutput fixed highs remaining
    calc _ ≤ ∑' prepared, Pr[= prepared | preparation parameterOutput fixed highs remaining] *
          ∑ i : OtsKey, (prepared.1 i).elim (1 : ℝ≥0∞) (fun _ => 0) :=
          ENNReal.tsum_le_tsum fun prepared => mul_le_mul_right (failMass_le_count prepared.1) _
      _ = ∑ i : OtsKey, ∑' prepared, Pr[= prepared | preparation parameterOutput fixed highs remaining] *
          (prepared.1 i).elim (1 : ℝ≥0∞) (fun _ => 0) := by
          simp only [Finset.mul_sum]
          rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      _ ≤ ∑ i : OtsKey, Pr[fun prepared => prepared.1 i = none | preparation parameterOutput fixed highs remaining] :=
          Finset.sum_le_sum fun i _ => tsum_elim_le _ i
      _ ≤ ∑ _i : OtsKey, (2 : ℝ≥0∞)⁻¹ ^ (2 ^ 18) :=
          Finset.sum_le_sum fun i _ => (prep_fail_le parameterOutput fixed highs remaining i).trans fail_pow_le
      _ = (Fintype.card OtsKey : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (2 ^ 18) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (2 ^ 58 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ (2 ^ 18) := by
          refine mul_le_mul_left (Nat.cast_le (α := ℝ≥0∞).2 ?_) _
          rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
          calc numLayers * (2 ^ totalHeight * 2 ^ maxLayerHeight) ≤ 4 * (2 ^ 28 * 2 ^ 28) :=
                Nat.mul_le_mul numLayers_le (Nat.mul_le_mul two_pow_totalHeight_le
                  (Nat.pow_le_pow_right (by norm_num) (maxLayerHeight_le.trans totalHeight_le_28)))
            _ = 2 ^ 58 := by norm_num
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 201 := by
          have hsplit : (2 : ℝ≥0∞)⁻¹ ^ (2 ^ 18) = (2 : ℝ≥0∞)⁻¹ ^ 58 * ((2 : ℝ≥0∞)⁻¹ ^ 201 *
              (2 : ℝ≥0∞)⁻¹ ^ (2 ^ 18 - 259)) := by
            rw [← pow_add, ← pow_add]
            congr 1
          rw [hsplit, Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc, ← mul_pow,
            ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow, one_mul]
          exact mul_le_of_le_one_right' (pow_le_one₀ bot_le (by norm_num))
  have hconst : ∀ {α : Type} (mx : ProbComp α) (g : α → ℝ≥0∞) (c : ℝ≥0∞), (∀ x, g x ≤ c) →
      ∑' x, Pr[= x | mx] * g x ≤ c := by
    intro α mx g c hg
    calc _ ≤ ∑' x, Pr[= x | mx] * c := ENNReal.tsum_le_tsum fun x => mul_le_mul_right (hg x) _
      _ ≤ c := by rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' tsum_probOutput_le_one
  unfold expectedFail
  exact hconst _ _ _ fun parameterOutput => hconst _ _ _ fun fixed => hconst _ _ _ fun highs =>
    hconst _ _ _ fun remaining => hinner parameterOutput fixed highs remaining

end FailBound

/-! ### Targeting facts of a sample -/

section Close

open HiddenBridge Completeness SeedModel Graph Assembly Reduce Internalize

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

/-- The targeting facts of one prepared sample. -/
def TargetingFor (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (prepared : (OtsKey → Option (Counter × Encoding)) × QueryCache HashSpec) : Prop :=
  ∃ tg : Targeting HashInput HashOutput Coordinate,
    Compatible tg (sampleModel parameterOutput highs) ∧ UniformTruncation (R := HashOutput) tg ∧
    (∀ x, IsMsgInput x → tg.kind x = .none ∧ tg.digest x) ∧
    ∀ table, tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table →
      ∀ s : State, Prepared prepared.2 s → Agrees s.known table →
        (CorrectGuess table s ∨ CacheMatch.Bad (TargetAssignment.targets (truncateHash parameterOutput)
          (compTable parameterOutput fixed highs remaining table prepared.1)) s.cache) →
        Hit tg prepared.2 table s

theorem two_mul_inv_pow_succ (n : ℕ) : (2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + 1) = (2 : ℝ≥0∞)⁻¹ ^ n := by
  rw [pow_succ, mul_comm, mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]

theorem div_two_pow (x : ℝ≥0∞) (n : ℕ) : x / 2 ^ n = x * (2 : ℝ≥0∞)⁻¹ ^ n := by
  rw [div_eq_mul_inv, ENNReal.inv_pow]

end Close

end FORS.Security.ForsPotential
