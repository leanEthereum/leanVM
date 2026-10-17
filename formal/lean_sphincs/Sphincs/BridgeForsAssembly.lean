import Sphincs.BridgeForsGame
import Sphincs.BridgeReplay

/-! Shared pieces of the routes that run saturation and the FORS potential on the same lazy run:
the start state, from the stopped experiment to the interpreted run, failing indices of the
prepared encoding searches and their expected share (at most `2^-201`), the prepared cache holding
no message-digest input, and the targeting facts of one prepared sample. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForestPrice ForestSigner HiddenReveal SphincsFors.Security.Domination

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

variable [Params]

section Rest

variable (parameter : PublicParameter) (data : PublicData) (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- A FORS cover of a completed run. -/
def CoverOf (out : Run HashInput Coordinate HiddenBridge.Outcome × State) : Prop :=
  ∃ outcome, out.1.1 = some outcome ∧
    HiddenBridge.ForestCover parameter data.root outcome out.1.2.1 out.2.cache

theorem start_pinv (hclean : ∀ p, initial (pblk parameter data p) = none) (known : Knowledge Coordinate) :
    PInv parameter data (DebtState.start initial known) [] := by
  refine ⟨List.nodup_nil, fun p => ?_⟩
  constructor
  · intro h; cases h
  · rintro ⟨u, hu, _⟩
    change initial (pblk parameter data p) = some u at hu
    rw [hclean p] at hu; cases hu

omit [Params] in
theorem start_count (hclean : ∀ p, initial (pblk parameter data p) = none) (known : Knowledge Coordinate)
    (budget : ℕ) : CountInv parameter data budget (DebtState.start initial known) budget := by
  intro m
  have : cachedCount parameter data m (DebtState.start initial known) = 0 := by
    unfold cachedCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro ρ _ h
    exact h (hclean (m, ρ))
  rw [this, zero_add]

omit [Params] in
theorem start_prepared (known : Knowledge Coordinate) : Prepared initial (DebtState.start initial known) :=
  fun _ _ h => h

end Rest

section Tick

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)

omit [Params] in
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

omit [Params] in
theorem interp_tick_bind_abort {β : Type} (amount : ℕ) (next : Unit → OracleComp CostSpec β) (budget : ℕ) (s : State)
    (h : ¬amount ≤ budget) :
    interp tg initial model (HiddenCost.tick amount >>= next) budget s = pure ((none, [], [], []), s) := by
  unfold HiddenCost.tick
  rw [interp_query_bind]
  split_ifs with hc
  · exact absurd hc h
  · rfl

omit [Params] in
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

omit [Params] in
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
    (remaining : RemainingOutputs) (results : Index → Option (Counter × Encoding)) (table : Coordinate → Digest)
    (v : ((Option HiddenBridge.Outcome × List Coordinate) × List (Entry HashInput)) × QueryCache HashSpec) : Prop :=
  CacheMatch.Bad (TargetAssignment.targets (truncateHash parameterOutput)
      (compTable parameterOutput fixed highs remaining table results)) v.2 ∨
    ∃ outcome, v.1.1.1 = some outcome ∧
      ForestCover (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining).root outcome v.1.1.2 v.2

/-- One table: the stopped run against the comparison run. -/
theorem stopped_table_le (hb : 0 < subtreeHeight) (adversary : Adversary) (q : ℕ) (hq : q < 2 ^ 256)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs)
    (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (table : Coordinate → Digest) (hagree : Agrees (knownOf (truncateHash parameterOutput) fixed) table) :
    Pr[HiddenReveal.StopOr RichWin | HiddenOutside.stopped (sampleModel parameterOutput highs) table
        (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
          (sampleData parameterOutput fixed highs remaining))))
        (knownOf (truncateHash parameterOutput) fixed) prepared.2] ≤
      Pr[fun r => CorrectGuess table r.2 ∨
          badFor parameterOutput fixed highs remaining prepared.1 table (r.1, r.2.cache) |
        fixedRun (sampleModel parameterOutput highs) table
          (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
            (sampleData parameterOutput fixed highs remaining))))
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
    rcases win_implies_bad hb adversary q hq parameterOutput fixed highs remaining prepared hprepared table htable
      outcome reveals entries cacheF hr hw with h | h
    · exact Or.inl h
    · exact Or.inr ⟨outcome, rfl, h⟩

set_option maxRecDepth 100000 in
/-- **From the stopped experiment to the interpreted run.** -/
theorem stopped_le_interp (hb : 0 < subtreeHeight) (adversary : Adversary) (q : ℕ) (hq : q < 2 ^ 256)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs)
    (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (tg : Targeting HashInput HashOutput Coordinate) :
    Pr[HiddenReveal.StopOr RichWin | HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
        (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
          (sampleData parameterOutput fixed highs remaining))))
        (knownOf (truncateHash parameterOutput) fixed) prepared.2] ≤
      Pr[fun x => CorrectGuess x.1 x.2.2 ∨
          badFor parameterOutput fixed highs remaining prepared.1 x.1 (((x.2.1.1, x.2.1.2.1), x.2.1.2.2.1), x.2.2.cache) |
        interp tg prepared.2 (sampleModel parameterOutput highs)
          (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
            (internalize adversary)) q (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed)) >>=
          fun result => (fun table => (table, result)) <$> completion result.2.known] := by
  unfold HiddenOutside.stoppedExperiment
  rw [probEvent_bind_eq_tsum]
  calc _ ≤ ∑' table, Pr[= table | completion (knownOf (truncateHash parameterOutput) fixed)] *
        Pr[fun r => CorrectGuess table r.2 ∨
            badFor parameterOutput fixed highs remaining prepared.1 table (r.1, r.2.cache) |
          fixedRun (sampleModel parameterOutput highs) table
            (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
              (sampleData parameterOutput fixed highs remaining))))
            (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed))] := by
        refine ENNReal.tsum_le_tsum fun table => ?_
        by_cases htab : table ∈ support (completion (knownOf (truncateHash parameterOutput) fixed))
        · have hag : Agrees (knownOf (truncateHash parameterOutput) fixed) table := by
            unfold completion at htab
            rw [support_map] at htab
            obtain ⟨t, _, rfl⟩ := htab
            exact fun c v hc => completion_known _ c v hc t
          have := stopped_table_le hb adversary q hq parameterOutput fixed highs remaining prepared
            hprepared table hag
          exact mul_le_mul_right this _
        · rw [probOutput_eq_zero_of_not_mem_support htab, zero_mul, zero_mul]
    _ = Pr[fun x => CorrectGuess x.1 x.2.2 ∨
            badFor parameterOutput fixed highs remaining prepared.1 x.1 (x.2.1, x.2.2.cache) |
          withTable (fun table => fixedRun (sampleModel parameterOutput highs) table
            (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
              (sampleData parameterOutput fixed highs remaining))))
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
              (sampleData parameterOutput fixed highs remaining))))
            (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed)) >>= fun result =>
              (fun table => (table, result)) <$> completion result.2.known] :=
        probEvent_congr' (fun _ _ => Iff.rfl) (withTable_fixedRun _ _ _)
    _ = _ := by
        unfold richProgram
        rw [lazyRun_wrapped tg prepared.2]
        have hcomp : ((fun out : Run HashInput Coordinate HiddenBridge.Outcome × State =>
              (((out.1.1, out.1.2.1), out.1.2.2.1), out.2)) <$>
            interp tg prepared.2 (sampleModel parameterOutput highs)
              (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
                (internalize adversary)) q (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed))) >>=
              (fun result => (fun table => (table, result)) <$> completion result.2.known) =
            (fun x : (Coordinate → Digest) × (Run HashInput Coordinate HiddenBridge.Outcome × State) =>
              (x.1, (((x.2.1.1, x.2.1.2.1), x.2.1.2.2.1), x.2.2))) <$>
            (interp tg prepared.2 (sampleModel parameterOutput highs)
              (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
                (internalize adversary)) q (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed)) >>=
              fun result => (fun table => (table, result)) <$> completion result.2.known) := by
          rw [bind_map_left, map_bind]
          refine bind_congr fun out => ?_
          rw [Functor.map_map]
        rw [hcomp, probEvent_map]
        rfl

/-- Keygen cost credited before the adversary runs. -/
abbrev keygenCost : ℕ := 226 * 2 ^ subtreeHeight + 2 * (totalHeight - subtreeHeight)

end Chain

/-! ### Failing indices of the prepared searches -/

section FailSet

open HiddenBridge Completeness SeedModel Graph Assembly Reduce Internalize

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

omit [Params] in
theorem noQ_bind {bad : HashInput → Prop} [DecidablePred bad] {α β : Type} {oa : OracleComp HashSpec α}
    {next : α → OracleComp HashSpec β} (h : oa.IsQueryBoundP bad 0)
    (hnext : ∀ value, (next value).IsQueryBoundP bad 0) : (oa >>= next).IsQueryBoundP bad 0 := by
  have := isQueryBoundP_bind (n := 0) (m := 0) h (fun value _ => hnext value)
  simpa using this

omit [Params] in
/-- The encoding search queries only encoding inputs. -/
theorem noQ_search {bad : HashInput → Prop} [DecidablePred bad]
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest)
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
      cases address <;> simp [Address.position, Position.domain, hashDomainFields, tweakFields] at htag

/-- Every prepared search result was recorded inside the prepared cache. -/
theorem preparation_parts (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining)) (i : Index) :
    ∃ c0, ∃ r ∈ support ((simulateQ (randomOracle (spec := HashSpec))
        (ReferenceChoice.search (truncateHash parameterOutput) topLayer rootTree i
          ((sampleData parameterOutput fixed highs remaining).forestKey i) encodingAttemptLimit 0)).run c0),
      r.1 = prepared.1 i ∧ ∀ x v, r.2 x = some v → prepared.2 x = some v :=
  sequenceFin_parts (D := HashInput) (R := HashOutput)
    (fun leaf => ReferenceChoice.search (truncateHash parameterOutput) topLayer rootTree leaf
      ((sampleData parameterOutput fixed highs remaining).forestKey leaf) encodingAttemptLimit 0)
    (structCache (splitMaterial parameterOutput highs remaining fixed) (splitAnswers highs remaining fixed))
    prepared hprepared i

/-- Local indices of some index whose prepared search failed. -/
noncomputable def failSet (results : Index → Option (Counter × Encoding)) : Finset (Fin (2 ^ subtreeHeight)) :=
  Finset.univ.filter fun l => ∃ i : Index, ForsPotential.localIdx i = l ∧ results i = none

/-- **A failed final assembly is at a failing index.** -/
theorem finishRest_fail (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs)
    (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (tg : Targeting HashInput HashOutput Coordinate) (m : Message) (ρ : Randomness) (digest : MessageDigest)
    (budget : ℕ) (s1 : State) (hprep : Prepared prepared.2 s1)
    (out : Run HashInput Coordinate (Option Signature) × State)
    (hout : out ∈ support (interp tg prepared.2 (sampleModel parameterOutput highs)
      (finishRest (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining) m ρ digest) budget s1))
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
  -- the search returned nothing
  have hfnone : found = none := by
    rcases found with _ | ⟨counter, word⟩
    · rfl
    · exfalso
      have hmem := interp_result_mem tg prepared.2 model _ _ _ o4 ho4 none (by rw [← hres4, ← hres2, hnone])
      revert hmem
      dsimp only
      intro hmem
      refine post_bind (fun v => v ≠ none) _ (fun _ => post_bind _ _ fun _ => post_bind _ _ fun _ => ?_) none hmem rfl
      intro v hv
      rw [support_pure, Set.mem_singleton_iff] at hv
      rw [hv]
      exact fun h => by cases h
  subst hfnone
  -- the recorded search of the same index
  obtain ⟨c0, r, hr, hr1, hr2⟩ := preparation_parts parameterOutput fixed highs remaining prepared hprepared
    (digestIndex digest)
  have ho3' : o3 ∈ support (interp tg prepared.2 model
      (liftM (ReferenceChoice.search (truncateHash parameterOutput) topLayer rootTree (digestIndex digest)
        ((sampleData parameterOutput fixed highs remaining).forestKey (digestIndex digest)) encodingAttemptLimit 0) :
        OracleComp CostSpec _) (budget - traceCost o1.1.2.2.1) o1.2) := ho3
  have hrow := noQ_search (bad := fun x => model.parse x ≠ none)
    (truncateHash parameterOutput) topLayer rootTree (digestIndex digest)
    ((sampleData parameterOutput fixed highs remaining).forestKey (digestIndex digest))
    (fun payload h => h (not_row_encoding parameterOutput highs _ _ _ _ payload)) encodingAttemptLimit 0
  have hstep := interp_liftHash_replay (D := HashInput) (R := HashOutput) tg prepared.2 model
    (ReferenceChoice.search (truncateHash parameterOutput) topLayer rootTree (digestIndex digest)
      ((sampleData parameterOutput fixed highs remaining).forestKey (digestIndex digest)) encodingAttemptLimit 0 :
        OracleComp HashSpec (Option (Counter × Encoding)))
  have hreplay := hstep hrow c0 r hr _ o1.2 (fun x v hx => hext1.1 x v (hprep x v (hr2 x v hx))) o3 ho3' none hfound
  rw [← hr1, ← hreplay]

end FailSet

/-! ### All samples -/

section Total

open HiddenBridge Completeness SeedModel Graph Assembly Reduce Internalize

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

omit [Params] in
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

omit [Params] in
theorem noQ_sequenceFin {bad : HashInput → Prop} [DecidablePred bad] {α : Type} :
    ∀ {n : ℕ} (f : Fin n → OracleComp HashSpec α), (∀ i, (f i).IsQueryBoundP bad 0) →
      (Concrete.sequenceFin f).IsQueryBoundP bad 0
  | 0, _, _ => trivial
  | n + 1, f, h => by
      unfold Concrete.sequenceFin
      exact noQ_bind (h 0) fun _ => noQ_bind (noQ_sequenceFin (fun i : Fin n => f i.succ) fun i => h i.succ)
        fun _ => trivial

omit [Params] in
theorem msg_not_graph (parameter : PublicParameter) (position : Position) (payload x : HashInput)
    (hx : IsMsgInput x) : x ≠ tweakableHashInput parameter position.domain payload := by
  obtain ⟨p', payload', rfl⟩ := hx
  intro heq
  have htag := congrArg TweakFields.tag (tweakableInput_injective heq).1
  cases position <;> simp [Position.domain, hashDomainFields, tweakFields] at htag

/-- **The prepared cache holds no message-digest input.** -/
theorem prepared_clean (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining)) :
    ∀ x, IsMsgInput x → prepared.2 x = none := by
  intro x hx
  have hrun : prepared ∈ support ((simulateQ (randomOracle (spec := HashSpec))
      (Concrete.sequenceFin fun leaf => ReferenceChoice.search (truncateHash parameterOutput) topLayer rootTree leaf
        ((sampleData parameterOutput fixed highs remaining).forestKey leaf) encodingAttemptLimit 0)).run
      (structCache (splitMaterial parameterOutput highs remaining fixed) (splitAnswers highs remaining fixed))) :=
    hprepared
  rw [randomOracle_run_avoid (P := IsMsgInput) _
    (noQ_sequenceFin _ fun leaf => noQ_search (bad := IsMsgInput) _ _ _ _ _
      (fun payload => not_msg_tweakable _ _ payload (by simp [hashDomainFields, tweakFields])) _ _) _ prepared hrun x hx]
  unfold structCache
  exact programGraphCache_empty_none _ _ _ _ _ x fun position _ => msg_not_graph _ position _ x hx

end Clean

/-! ### Few prepared searches fail -/

section FailBound

open HiddenBridge Completeness SeedModel Graph Assembly Reduce Internalize

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

omit [Params] in
theorem search_eq_searchLoop (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) : ∀ (n t : ℕ),
    (ReferenceChoice.search parameter lay tree leaf message n t : OracleComp HashSpec (Option (Counter × Encoding))) =
      searchLoop (fun c => tweakableHashInput parameter (.encoding lay tree leaf)
          (bytesLE 16 message ++ bytesLE 4 (BitVec.ofNat counterBits c)))
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

omit [Params] in
/-- One search over fresh counters fails with at most the rejection share to the trial budget. -/
theorem search_fail_le (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (cache : QueryCache HashSpec)
    (hfresh : ∀ s, s < encodingAttemptLimit → cache (encodeInput parameter lay tree leaf message s) = none) :
    Pr[fun r => r.1 = none | (simulateQ (randomOracle (spec := HashSpec))
        (ReferenceChoice.search parameter lay tree leaf message encodingAttemptLimit 0)).run cache] ≤
      Completeness.failMass (fun out => TargetSum.decodeDigest (truncateHash out)) ^ encodingAttemptLimit := by
  rw [search_eq_searchLoop]
  exact probEvent_searchLoop _ _ _ encodingAttemptLimit
    (fun s s' hs hs' heq => encodeInput_inj parameter lay tree leaf message hs hs' heq)
    encodingAttemptLimit 0 (by simp) cache (fun s _ hsb => hfresh s hsb)

omit [Params] in
theorem encoding_not_graph (parameter parameter' : PublicParameter) (position : Position) (payload payload' : HashInput)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    tweakableHashInput parameter' (.encoding lay tree leaf) payload' ≠
      tweakableHashInput parameter position.domain payload := by
  intro heq
  have htag := congrArg TweakFields.tag (tweakableInput_injective heq).1
  cases position <;> simp [Position.domain, hashDomainFields, tweakFields] at htag

/-- **One prepared search fails rarely.** -/
theorem prep_fail_le (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (i : Index) :
    Pr[fun prepared => prepared.1 i = none | preparation parameterOutput fixed highs remaining] ≤
      Completeness.failMass (fun out => TargetSum.decodeDigest (truncateHash out)) ^ encodingAttemptLimit := by
  set key := (sampleData parameterOutput fixed highs remaining).forestKey with hkey
  set param := truncateHash parameterOutput with hparam
  change Pr[fun prepared => prepared.1 i = none | (simulateQ (randomOracle (spec := HashSpec))
      (Concrete.sequenceFin fun leaf => ReferenceChoice.search param topLayer rootTree leaf (key leaf)
        encodingAttemptLimit 0)).run
      (structCache (splitMaterial parameterOutput highs remaining fixed) (splitAnswers highs remaining fixed))] ≤ _
  refine sequenceFin_prob (D := HashInput) (R := HashOutput)
    (fun c => ∀ s, s < encodingAttemptLimit → c (encodeInput param topLayer rootTree i (key i) s) = none)
    (fun r => r = none) _ _ i ?_ ?_ _ ?_
  · -- other searches never touch this leaf's counters
    intro j hj c hc r hr s hs
    have hkeep := randomOracle_run_avoid (P := fun x => ∃ t, x = encodeInput param topLayer rootTree i (key i) t) _
      (noQ_search (bad := fun x => ∃ t, x = encodeInput param topLayer rootTree i (key i) t) _ _ _ j (key j)
        (fun payload ⟨t, ht⟩ => hj (encoding_fields_injective (tweakableInput_injective ht).1)) _ _)
      c r hr _ ⟨s, rfl⟩
    rw [hkeep]
    exact hc s hs
  · intro c hc
    exact search_fail_le param topLayer rootTree i (key i) c hc
  · intro s _
    unfold structCache
    exact programGraphCache_empty_none _ _ _ _ _ _ fun position _ => encoding_not_graph _ _ position _ _ _ _ _

omit [Params] in
/-- Bernoulli: `(1 - 2⁻¹⁰) ^ 2¹⁰ ≤ 1/2`. -/
theorem one_sub_pow_le_half : (1 - (2 : ℝ)⁻¹ ^ 10) ^ (2 ^ 10) ≤ 1 / 2 := by
  set a : ℝ := (2 : ℝ)⁻¹ ^ 10 with ha
  have ha0 : 0 ≤ a := by positivity
  have ha1 : a ≤ 1 := by rw [ha]; norm_num
  have hbern : 1 + ((2 ^ 10 : ℕ) : ℝ) * a ≤ (1 + a) ^ (2 ^ 10) := one_add_mul_le_pow (by linarith) _
  have hna : ((2 ^ 10 : ℕ) : ℝ) * a = 1 := by rw [ha]; norm_num
  rw [hna] at hbern
  have hprod : (1 - a) ^ (2 ^ 10) * (1 + a) ^ (2 ^ 10) ≤ 1 := by
    rw [← mul_pow]
    have h0 : 0 ≤ (1 - a) * (1 + a) := mul_nonneg (by linarith) (by linarith)
    have h1 : (1 - a) * (1 + a) ≤ 1 := by nlinarith
    exact pow_le_one₀ h0 h1
  have hpos : 0 < (1 + a) ^ (2 ^ 10) := by positivity
  rw [div_eq_mul_inv, one_mul]
  calc (1 - a) ^ (2 ^ 10) = (1 - a) ^ (2 ^ 10) * (1 + a) ^ (2 ^ 10) / (1 + a) ^ (2 ^ 10) := by
        field_simp
    _ ≤ 1 / (1 + a) ^ (2 ^ 10) := by gcongr
    _ ≤ 1 / 2 := by gcongr; exact (by norm_num : (2 : ℝ) ≤ 1 + 1).trans hbern
    _ = 2⁻¹ := by norm_num

omit [Params] in
/-- The trial budget makes a prepared search fail with negligible probability. -/
theorem fail_pow_le :
    Completeness.failMass (fun out => TargetSum.decodeDigest (truncateHash out)) ^ encodingAttemptLimit ≤
      (2 : ℝ≥0∞)⁻¹ ^ (2 ^ 22) := by
  set fm := Completeness.failMass (fun out => TargetSum.decodeDigest (truncateHash out)) with hfm
  have hadd := Completeness.failMass_encoding_add_le
  have hle : fm ≤ ENNReal.ofReal (1 - (2 : ℝ)⁻¹ ^ 10) := by
    have htop : ((2 : ℝ≥0∞) ^ 10)⁻¹ ≠ ⊤ := by simp
    have h1 : fm ≤ 1 - ((2 : ℝ≥0∞) ^ 10)⁻¹ := ENNReal.le_sub_of_add_le_right htop hadd
    refine h1.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]
    congr 1
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.inv_pow]
  calc fm ^ encodingAttemptLimit ≤ ENNReal.ofReal (1 - (2 : ℝ)⁻¹ ^ 10) ^ (2 ^ 10 * 2 ^ 22) := by
        rw [show encodingAttemptLimit = 2 ^ 10 * 2 ^ 22 from rfl]
        exact pow_le_pow_left' hle _
    _ = (ENNReal.ofReal ((1 - (2 : ℝ)⁻¹ ^ 10) ^ (2 ^ 10))) ^ (2 ^ 22) := by
        rw [pow_mul, ENNReal.ofReal_pow (by norm_num)]
    _ ≤ (ENNReal.ofReal (1 / 2)) ^ (2 ^ 22) := pow_le_pow_left' (ENNReal.ofReal_le_ofReal one_sub_pow_le_half) _
    _ = (2 : ℝ≥0∞)⁻¹ ^ (2 ^ 22) := by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]

theorem failMass_le_count (R : Index → Option (Counter × Encoding)) :
    failMass (failSet R) ≤ ∑ i : Index, (R i).elim (1 : ℝ≥0∞) fun _ => 0 := by
  by_cases h : ∃ i, R i = none
  · obtain ⟨i, hi⟩ := h
    calc failMass (failSet R) ≤ 1 := by
          unfold failMass
          calc _ ≤ freshAvg Finset.univ (fun _ : View => (1 : ℝ≥0∞)) :=
                freshAvg_mono _ fun v _ => by split_ifs <;> simp
            _ = 1 := freshAvg_const _ Finset.univ_nonempty 1
      _ = (R i).elim (1 : ℝ≥0∞) fun _ => 0 := by rw [hi]; rfl
      _ ≤ _ := Finset.single_le_sum (f := fun i : Index => (R i).elim (1 : ℝ≥0∞) fun _ => 0)
          (fun _ _ => bot_le) (Finset.mem_univ i)
  · push Not at h
    have hempty : failSet R = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun l hl => ?_
      obtain ⟨i, _, hi⟩ := (Finset.mem_filter.1 hl).2
      exact h i hi
    rw [hempty]
    unfold failMass freshAvg
    simp only [Finset.notMem_empty, if_false, Finset.sum_const_zero, mul_zero]
    exact bot_le

omit [Params] in
theorem tsum_elim_le {β : Type} (mx : ProbComp ((Index → Option β) × QueryCache HashSpec)) (i : Index) :
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
          ∑ i : Index, (prepared.1 i).elim (1 : ℝ≥0∞) (fun _ => 0) :=
          ENNReal.tsum_le_tsum fun prepared => mul_le_mul_right (failMass_le_count prepared.1) _
      _ = ∑ i : Index, ∑' prepared, Pr[= prepared | preparation parameterOutput fixed highs remaining] *
          (prepared.1 i).elim (1 : ℝ≥0∞) (fun _ => 0) := by
          simp only [Finset.mul_sum]
          rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      _ ≤ ∑ i : Index, Pr[fun prepared => prepared.1 i = none | preparation parameterOutput fixed highs remaining] :=
          Finset.sum_le_sum fun i _ => tsum_elim_le _ i
      _ ≤ ∑ _i : Index, (2 : ℝ≥0∞)⁻¹ ^ (2 ^ 22) :=
          Finset.sum_le_sum fun i _ => (prep_fail_le parameterOutput fixed highs remaining i).trans fail_pow_le
      _ = (2 ^ 26 : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ (2 ^ 22) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rfl
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 201 := by
          have hsplit : (2 : ℝ≥0∞)⁻¹ ^ (2 ^ 22) = (2 : ℝ≥0∞)⁻¹ ^ 26 * ((2 : ℝ≥0∞)⁻¹ ^ 201 *
              (2 : ℝ≥0∞)⁻¹ ^ (2 ^ 22 - 227)) := by
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
    (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec) : Prop :=
  ∃ tg : Targeting HashInput HashOutput Coordinate,
    Compatible tg (sampleModel parameterOutput highs) ∧ UniformTruncation (R := HashOutput) tg ∧
    (∀ x, IsMsgInput x → tg.kind x = .none ∧ tg.digest x) ∧
    ∀ table, tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table →
      ∀ s : State, Prepared prepared.2 s → Agrees s.known table →
        (CorrectGuess table s ∨ CacheMatch.Bad (TargetAssignment.targets (truncateHash parameterOutput)
          (compTable parameterOutput fixed highs remaining table prepared.1)) s.cache) →
        Hit tg prepared.2 table s

omit [Params] in
theorem two_mul_inv_pow_succ (n : ℕ) : (2 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ (n + 1) = (2 : ℝ≥0∞)⁻¹ ^ n := by
  rw [pow_succ, mul_comm, mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]

omit [Params] in
theorem div_two_pow (x : ℝ≥0∞) (n : ℕ) : x / 2 ^ n = x * (2 : ℝ≥0∞)⁻¹ ^ n := by
  rw [div_eq_mul_inv, ENNReal.inv_pow]

end Close

end Sphincs.Security.ForsPotential
