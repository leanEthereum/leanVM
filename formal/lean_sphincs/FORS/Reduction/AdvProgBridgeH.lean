module

public import FORS.Classification.Win
public import FORS.CoverPotential.GameH
public import FORS.LargeBudget.HonestCoupling
public import FORS.Reduction.UntilSeedH

@[expose] public section

/-! The honest-reading game against the charged one, in the stopped world. The honest program
(`costGameXH`: the signer's reads honest, everything else charged) and the charged program
(`costGameX`) issue the same erased queries, the signer's honest reads being the charged reads of
the same inputs; the charged program has extra ticks and records more. So every finished stopped
run of the honest rich program at a budget `Q` is a finished stopped run of the charged rich program
at a budget the charged program cannot exhaust, with the same outcome, reveals and final cache, and
with at most `Q` recorded inputs of a seed's length (44 or 80 bytes): the signer reads none. The
charged win implication, whose only use of its budget is to avoid the seed in those inputs, then
holds of the honest program (`win_implies_bad`). -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.HiddenBridge

variable [Params]

open Concrete Completeness _root_.FORS.Security.Graph GraphCorrectness HiddenGraph Assembly SeedModel Reduce Eager
  HiddenCost GraphView

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-! ### Support transfer in the stopped world -/

/-- The erased (stopped-world) query interface. -/
abbrev SrcSpec := HiddenRows.SourceSpec HashInput HashOutput Coordinate

section Sim

variable {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate) (table : HiddenGraph.Table)

/-- `y` asks the queries `x` asks, until `x` can no longer produce a good result; finished good
results are related. -/
inductive Sim {α β : Type} (G : α → Prop) (R : α → β → Prop) : OracleComp SrcSpec α → OracleComp SrcSpec β → Prop
  | pure (a : α) (b : β) (h : G a → R a b) : Sim G R (pure a) (pure b)
  | query (input : SrcSpec.Domain) (left : SrcSpec.Range input → OracleComp SrcSpec α) (right : SrcSpec.Range input → OracleComp SrcSpec β)
      (h : ∀ value, Sim G R (left value) (right value)) :
      Sim G R (liftM (SrcSpec.query input) >>= left) (liftM (SrcSpec.query input) >>= right)
  | escape (left : OracleComp SrcSpec α) (right : OracleComp SrcSpec β) (h : ∀ a ∈ support left, ¬G a) : Sim G R left right

theorem Sim.map {α β α' β' : Type} {G : α → Prop} {R : α → β → Prop} {G' : α' → Prop} {R' : α' → β' → Prop}
    (f : α → α') (g : β → β') (hG : ∀ a, G' (f a) → G a) (hR : ∀ a b, G' (f a) → R a b → R' (f a) (g b))
    {x : OracleComp SrcSpec α} {y : OracleComp SrcSpec β} (h : Sim G R x y) : Sim G' R' (f <$> x) (g <$> y) := by
  induction h with
  | pure a b h => exact Sim.pure (f a) (g b) fun hg => hR a b hg (h (hG a hg))
  | query input left right _ ih =>
      rw [map_bind, map_bind]
      exact Sim.query input _ _ ih
  | escape left right h =>
      refine Sim.escape _ _ fun a ha hg => ?_
      rw [support_map] at ha
      obtain ⟨a0, ha0, rfl⟩ := ha
      exact h a0 ha0 (hG a0 hg)

/-- A step of the stopped world finishes only through its continuation. -/
theorem stoppedStep_some {α β : Type} (input : SrcSpec.Domain)
    (left : SrcSpec.Range input → HiddenReveal.Knowledge Coordinate → QueryCache HashSpec →
      ProbComp (Option (α × QueryCache HashSpec)))
    (right : SrcSpec.Range input → HiddenReveal.Knowledge Coordinate → QueryCache HashSpec →
      ProbComp (Option (β × QueryCache HashSpec)))
    (P : α × QueryCache HashSpec → Prop) (Q : α × QueryCache HashSpec → β × QueryCache HashSpec → Prop)
    (h : ∀ value known cache r, some r ∈ support (left value known cache) → P r →
      ∃ r', Q r r' ∧ some r' ∈ support (right value known cache))
    (known : HiddenReveal.Knowledge Coordinate) (cache : QueryCache HashSpec) (r : α × QueryCache HashSpec)
    (hr : some r ∈ support (HiddenOutside.stoppedStep model table input left known cache)) (hP : P r) :
    ∃ r', Q r r' ∧ some r' ∈ support (HiddenOutside.stoppedStep model table input right known cache) := by
  rcases input with draw | (bytes | coordinate)
  · simp only [HiddenOutside.stoppedStep, mem_support_bind_iff] at hr ⊢
    obtain ⟨value, hv, hr⟩ := hr
    obtain ⟨r', hq, hr'⟩ := h value known cache r hr hP
    exact ⟨r', hq, value, hv, hr'⟩
  · have hord : ∀ (hr : some r ∈ support (HiddenOutside.outsideRead bytes cache >>= fun result =>
        left result.1 known result.2)), ∃ r', Q r r' ∧ some r' ∈ support (HiddenOutside.outsideRead bytes cache >>=
          fun result => right result.1 known result.2) := by
      intro hr
      simp only [mem_support_bind_iff] at hr ⊢
      obtain ⟨result, hres, hr⟩ := hr
      obtain ⟨r', hq, hr'⟩ := h result.1 known result.2 r hr hP
      exact ⟨r', hq, result, hres, hr'⟩
    simp only [HiddenOutside.stoppedStep] at hr ⊢
    cases hp : model.parse bytes with
    | none => rw [hp] at hr; exact hord hr
    | some query =>
        rw [hp] at hr
        dsimp only at hr ⊢
        split_ifs at hr ⊢ with h1 h2
        · simp at hr
        · exact h _ _ _ r hr hP
        · exact hord hr
  · simp only [HiddenOutside.stoppedStep] at hr ⊢
    exact h _ _ _ r hr hP

/-- A finished stopped run's result is a result of the program. -/
theorem stopped_some_mem {α : Type} (x : OracleComp SrcSpec α) :
    ∀ known cache (r : α × QueryCache HashSpec),
      some r ∈ support (HiddenOutside.stopped model table x known cache) → r.1 ∈ support x := by
  induction x using OracleComp.inductionOn with
  | pure a =>
      intro known cache r hr
      change some r ∈ support (pure (some (a, cache)) : ProbComp _) at hr
      rw [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hr
      subst hr
      exact Set.mem_singleton _
  | query_bind input next ih =>
      intro known cache r hr
      rw [HiddenDebt.stopped_query_bind] at hr
      obtain ⟨r', ⟨rfl, value, hv⟩, -⟩ := stoppedStep_some model table input
        (fun value => HiddenOutside.stopped model table (next value))
        (fun value => HiddenOutside.stopped model table (next value))
        (fun _ => True) (fun r r' => r' = r ∧ ∃ value, r.1 ∈ support (next value))
        (fun value known cache r0 hr0 _ => ⟨r0, ⟨rfl, value, ih value known cache r0 hr0⟩, hr0⟩)
        known cache r hr trivial
      rw [support_bind]
      exact Set.mem_iUnion₂.2 ⟨value, by simp, hv⟩

/-- **Support transfer.** A good finished stopped run of `x` has a related finished stopped run of
`y` with the same final cache. -/
theorem Sim.stopped {α β : Type} {G : α → Prop} {R : α → β → Prop} {x : OracleComp SrcSpec α} {y : OracleComp SrcSpec β}
    (h : Sim G R x y) :
    ∀ known cache (a : α) (cacheF : QueryCache HashSpec),
      some (a, cacheF) ∈ support (HiddenOutside.stopped model table x known cache) → G a →
      ∃ b, R a b ∧ some (b, cacheF) ∈ support (HiddenOutside.stopped model table y known cache) := by
  induction h with
  | pure a b h =>
      intro known cache a' cacheF ha hg
      change some (a', cacheF) ∈ support (Pure.pure (some (a, cache)) : ProbComp _) at ha
      rw [support_pure, Set.mem_singleton_iff, Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl⟩ := ha
      exact ⟨b, h hg, Set.mem_singleton _⟩
  | query input left right _ ih =>
      intro known cache a cacheF ha hg
      rw [HiddenDebt.stopped_query_bind] at ha ⊢
      obtain ⟨r', ⟨b, hb, rfl⟩, hr'⟩ := stoppedStep_some model table input
        (fun value => HiddenOutside.stopped model table (left value))
        (fun value => HiddenOutside.stopped model table (right value))
        (fun r => G r.1) (fun r r' => ∃ b, R r.1 b ∧ r' = (b, r.2))
        (fun value known cache r hr hg => by
          obtain ⟨b, hb, hb'⟩ := ih value known cache r.1 r.2 hr hg
          exact ⟨(b, r.2), ⟨b, hb, rfl⟩, hb'⟩)
        known cache (a, cacheF) ha hg
      exact ⟨b, hb, hr'⟩
  | escape left right h =>
      intro known cache a cacheF ha hg
      exact absurd hg (h a (stopped_some_mem model table left known cache (a, cacheF) ha))

end Sim

/-! ### The coupling of the honest and the charged programs -/

/-- An input of a seed's length (`Stop.seedHit_length`). -/
def SeedLength (input : HashInput) : Prop := input.length = 44 ∨ input.length = 80

/-- The recorded inputs of a seed's length. -/
noncomputable def seedMarks (entries : List (Entry HashInput)) : ℕ :=
  ((entries.filterMap fun entry => match entry with | .inl input => some input | .inr _ => none).filter
    fun input => decide (SeedLength input)).length

theorem seedMarks_append (left right : List (Entry HashInput)) :
    seedMarks (left ++ right) = seedMarks left + seedMarks right := by
  simp only [seedMarks, List.filterMap_append, List.filter_append, List.length_append]

theorem seedMarks_recorded_le {H : Type} (input : (SourceCostSpec HashInput HashOutput Coordinate H).Domain) :
    seedMarks (recorded input) ≤ sourceCost input := by
  rcases input with (draw | bytes | coordinate) | (amount | honest)
  · exact Nat.zero_le _
  · simp only [recorded, sourceCost, seedMarks, List.filterMap_cons, List.filterMap_nil]
    exact List.length_filter_le _ _
  · exact Nat.zero_le _
  · simp [recorded, seedMarks]
  · exact Nat.zero_le _

/-- The stopped-world form of a capped program: erased, traced, with its reveals. -/
noncomputable def erun {H : Type} [HonestInputs H HashInput] {α : Type}
    (computation : OracleComp (SourceCostSpec HashInput HashOutput Coordinate H) α) (budget : ℕ) :
    OracleComp SrcSpec ((Option α × List Coordinate) × List (Entry HashInput)) :=
  erase (trace (withReveals (cap computation budget)))

theorem erun_pure {H : Type} [HonestInputs H HashInput] {α : Type} (value : α) (budget : ℕ) :
    erun (pure value : OracleComp (SourceCostSpec HashInput HashOutput Coordinate H) α) budget =
      pure ((some value, []), []) := by
  simp [erun, cap, withReveals_pure, trace_pure, erase]

theorem erun_query_bind {H : Type} [HonestInputs H HashInput] {α : Type}
    (input : (SourceCostSpec HashInput HashOutput Coordinate H).Domain)
    (next : (SourceCostSpec HashInput HashOutput Coordinate H).Range input →
      OracleComp (SourceCostSpec HashInput HashOutput Coordinate H) α) (budget : ℕ) :
    erun (liftM ((SourceCostSpec HashInput HashOutput Coordinate H).query input) >>= next) budget =
      if sourceCost input ≤ budget then
        eraseQuery input >>= fun value =>
          (fun result => ((result.1.1, revealed input ++ result.1.2), recorded input ++ result.2)) <$>
            erun (next value) (budget - sourceCost input)
      else pure ((none, []), []) := by
  unfold erun
  rw [cap_query_bind_gen]
  split_ifs
  · rw [withReveals_query_bind, trace_query_bind, erase, simulateQ_bind, simulateQ_spec_query]
    refine bind_congr fun value => ?_
    simp only [trace_map, simulateQ_map, Functor.map_map, erase]
  · simp [withReveals_pure, trace_pure, erase]

/-- A finished result. -/
def Finished {α : Type} (result : (Option α × List Coordinate) × List (Entry HashInput)) : Prop :=
  result.1.1.isSome

/-- Same result and reveals; at most `budget` recorded seed-length inputs on the right. -/
def Related {α : Type} (budget : ℕ) (left right : (Option α × List Coordinate) × List (Entry HashInput)) : Prop :=
  left.1 = right.1 ∧ seedMarks right.2 ≤ budget

/-- The honest program (left) against the charged program (right): the same source queries and
ticks, an honest read against a charged read of the same input (never of a seed's length), and
extra ticks on the right. -/
inductive Corr {α : Type} : OracleComp CostSpecH α → OracleComp CostSpec α → Prop
  | pure (a : α) : Corr (pure a) (pure a)
  | source (input : SrcSpec.Domain) (left : SrcSpec.Range input → OracleComp CostSpecH α)
      (right : SrcSpec.Range input → OracleComp CostSpec α) (h : ∀ value, Corr (left value) (right value)) :
      Corr (liftM (CostSpecH.query (.inl input)) >>= left) (liftM (CostSpec.query (.inl input)) >>= right)
  | tick (amount : ℕ) (left : Unit → OracleComp CostSpecH α) (right : Unit → OracleComp CostSpec α)
      (h : Corr (left ()) (right ())) :
      Corr (liftM (CostSpecH.query (.inr (.inl amount))) >>= left) (liftM (CostSpec.query (.inr (.inl amount))) >>= right)
  | honest (input : HashInput) (hinput : ¬SeedLength input) (left : HashOutput → OracleComp CostSpecH α)
      (right : HashOutput → OracleComp CostSpec α) (h : ∀ value, Corr (left value) (right value)) :
      Corr (liftM (CostSpecH.query (.inr (.inr input))) >>= left)
        (liftM (CostSpec.query (.inl (.inr (.inl input)))) >>= right)
  | extra (amount : ℕ) (left : OracleComp CostSpecH α) (right : Unit → OracleComp CostSpec α)
      (h : Corr left (right ())) : Corr left (liftM (CostSpec.query (.inr (.inl amount))) >>= right)

theorem revealed_source {H : Type} (input : SrcSpec.Domain) :
    @revealed HashInput HashOutput Coordinate H (Sum.inl input) =
      @revealed HashInput HashOutput Coordinate Empty (Sum.inl input) := by
  rcases input with _ | _ | _ <;> rfl

theorem recorded_source {H : Type} (input : SrcSpec.Domain) :
    @recorded HashInput HashOutput Coordinate H (Sum.inl input) =
      @recorded HashInput HashOutput Coordinate Empty (Sum.inl input) := by
  rcases input with _ | _ | _ <;> rfl

theorem sourceCost_source {H : Type} (input : SrcSpec.Domain) :
    @sourceCost HashInput HashOutput Coordinate H (Sum.inl input) =
      @sourceCost HashInput HashOutput Coordinate Empty (Sum.inl input) := by
  rcases input with _ | _ | _ <;> rfl

/-- **The coupling in the stopped world.** At any budget the charged program cannot exhaust, the
charged program's stopped form follows the honest program's at budget `budget`. -/
theorem Corr.sim {α : Type} {left : OracleComp CostSpecH α} {right : OracleComp CostSpec α} (h : Corr left right) :
    ∀ budget budget', CostAtMost right budget' →
      Sim Finished (Related budget) (erun left budget) (erun right budget') := by
  induction h with
  | pure a =>
      intro budget budget' _
      rw [erun_pure, erun_pure]
      exact Sim.pure _ _ fun _ => ⟨rfl, Nat.zero_le _⟩
  | source input left right _ ih =>
      intro budget budget' hc
      rw [costAtMost_query_bind] at hc
      rw [erun_query_bind, erun_query_bind]
      by_cases hb : @sourceCost HashInput HashOutput Coordinate HashInput (Sum.inl input) ≤ budget
      · rw [ite_eq_left hb, ite_eq_left hc.1]
        refine Sim.query input _ _ fun value => Sim.map _ _ (fun _ hg => hg) (fun rH rC _ hr => ⟨?_, ?_⟩)
          (ih value _ _ (hc.2 value))
        · rw [revealed_source, hr.1]
        · rw [recorded_source, seedMarks_append]
          have h1 := seedMarks_recorded_le (Sum.inl input : CostSpec.Domain)
          have h2 := hr.2
          have h3 := sourceCost_source (H := HashInput) input
          omega
      · rw [ite_eq_right hb]
        exact Sim.escape _ _ fun a ha hg => by
          rw [support_pure, Set.mem_singleton_iff] at ha
          subst ha
          exact absurd hg (by simp [Finished])
  | tick amount left right _ ih =>
      intro budget budget' hc
      rw [costAtMost_query_bind] at hc
      rw [erun_query_bind, erun_query_bind]
      by_cases hb : @sourceCost HashInput HashOutput Coordinate HashInput (Sum.inr (Sum.inl amount)) ≤ budget
      · rw [ite_eq_left hb, ite_eq_left hc.1]
        change Sim _ _ (Pure.pure () >>= _) (Pure.pure () >>= _)
        rw [pure_bind, pure_bind]
        refine Sim.map _ _ (fun _ hg => hg) (fun rH rC _ hr => ⟨?_, ?_⟩) (ih _ _ (hc.2 ()))
        · simp only [revealed, List.nil_append]
          exact hr.1
        · simp only [recorded, seedMarks_append]
          have h2 := hr.2
          have h3 : seedMarks [Sum.inr amount] = 0 := by simp [seedMarks]
          change amount ≤ budget at hb
          change seedMarks rC.2 ≤ budget - amount at h2
          omega
      · rw [ite_eq_right hb]
        exact Sim.escape _ _ fun a ha hg => by
          rw [support_pure, Set.mem_singleton_iff] at ha
          subst ha
          exact absurd hg (by simp [Finished])
  | honest input hinput left right _ ih =>
      intro budget budget' hc
      rw [costAtMost_query_bind] at hc
      rw [erun_query_bind, erun_query_bind]
      rw [ite_eq_left (show @sourceCost HashInput HashOutput Coordinate HashInput (Sum.inr (Sum.inr input)) ≤ budget
        from Nat.zero_le _), ite_eq_left hc.1]
      refine Sim.query (Sum.inr (Sum.inl input)) _ _ fun value =>
        Sim.map _ _ (fun _ hg => hg) (fun rH rC _ hr => ⟨?_, ?_⟩) (ih value _ _ (hc.2 value))
      · exact hr.1
      · have h2 := hr.2
        have h3 : seedMarks [Sum.inl input] = 0 := by simp [seedMarks, hinput]
        change seedMarks ([Sum.inl input] ++ rC.2) ≤ budget
        change seedMarks rC.2 ≤ budget - 0 at h2
        rw [seedMarks_append]
        omega
  | extra amount left right _ ih =>
      intro budget budget' hc
      rw [costAtMost_query_bind] at hc
      rw [erun_query_bind (H := Empty), ite_eq_left hc.1]
      change Sim _ _ _ (Pure.pure () >>= _)
      rw [pure_bind, ← id_map (erun left budget)]
      refine Sim.map id _ (fun _ hg => hg) (fun rH rC _ hr => ⟨?_, ?_⟩) (ih budget _ (hc.2 ()))
      · simp only [revealed, List.nil_append]
        exact hr.1
      · have h3 : seedMarks [Sum.inr amount] = 0 := by simp [seedMarks]
        simp only [recorded, seedMarks_append, h3, Nat.zero_add]
        exact hr.2

attribute [local irreducible] ReferenceChoice.selection encodingAttemptLimit

theorem win_implies_badM (hb : 0 < keptHeight topLayer) (adversary : Adversary) (q : Nat)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (steps : Message → Randomness)
    (prepared : (OtsKey → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (table : HiddenGraph.Table)
    (htable : tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table)
    (outcome : Outcome) (reveals : List Coordinate) (entries : List (HiddenCost.Entry HashInput))
    (cacheF : QueryCache HashSpec)
    (hstop : some (((some outcome, reveals), entries), cacheF) ∈ support
      (HiddenOutside.stopped (sampleModel parameterOutput highs) table
        (HiddenCost.erase (HiddenCost.trace (richProgram (Internalize.internalize adversary) q
          (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps))))
        (knownOf (truncateHash parameterOutput) fixed) prepared.2))
    (hwin : outcomeWins outcome = true) (hmarks : seedMarks entries < 2 ^ 256) :
    CacheMatch.Bad (digestFreeTargets parameterOutput fixed highs remaining table prepared.1) cacheF ∨
      ForsCover (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining).root
        outcome reveals cacheF := by
  obtain ⟨hgrow, hrun, hguess⟩ := lazy_support (sampleModel parameterOutput highs) table _
    (knownOf (truncateHash parameterOutput) fixed) prepared.2 cacheF _ entries hstop
  obtain ⟨-, hcached⟩ := lazy_cached (sampleModel parameterOutput highs) table _
    (knownOf (truncateHash parameterOutput) fixed) prepared.2 cacheF _ entries hstop
  have hOnly : OnlyC (richProgram (Internalize.internalize adversary) q (truncateHash parameterOutput)
      (sampleData parameterOutput fixed highs remaining steps)) :=
    OnlyC.withReveals (OnlyC.cap (OnlyC.costGameX _ _ adversary) q)
  have hshortE := costRun_entries_short _ table _ hOnly _ hrun
  obtain ⟨seed, hseed⟩ := exists_seed_avoiding _ hmarks
  have hseed' : ∀ input, Sum.inl input ∈ entries → ¬SeedGuess.SeedHit input seed := fun input hinput hhit =>
    hseed input (List.mem_filter.2 ⟨List.mem_filterMap.mpr ⟨_, hinput, rfl⟩,
      decide_eq_true ((Stop.seedHit_length hhit).symm.imp id id)⟩) hhit
  have hstructPrep := (preparation_support _ _ _ prepared hprepared
    (preferCache prepared.2 (sampleFn (materialT parameterOutput fixed highs remaining table) seed
      (answersT parameterOutput fixed highs remaining table) (finalTable parameterOutput highs table cacheF)))
    (preferCache_agrees _ _))
  have hstruct : ∀ input answer, structCache (splitMaterial parameterOutput highs remaining fixed)
      (splitAnswers highs remaining fixed) input = some answer → cacheF input = some answer :=
    fun input answer h => hgrow input answer (hstructPrep.1 h)
  have hagreeAll := sampleFn_final parameterOutput fixed highs remaining table htable cacheF seed hstruct
  have hagree : ∀ input, Sum.inl input ∈ entries →
      sampleFn (materialT parameterOutput fixed highs remaining table) seed
        (answersT parameterOutput fixed highs remaining table) (finalTable parameterOutput highs table cacheF) input =
      finalFn (sampleModel parameterOutput highs) table cacheF input :=
    fun input hinput => hagreeAll input (hshortE input hinput) (hseed' input hinput)
  set f' := sampleFn (materialT parameterOutput fixed highs remaining table) seed
    (answersT parameterOutput fixed highs remaining table) (finalTable parameterOutput highs table cacheF) with hf'
  have hrun' := costRun_support_congr _ f' table _ _ hrun (fun input hinput => (hagree input hinput).symm)
  have hagreement := sample_agreement (materialT parameterOutput fixed highs remaining table) seed
    (answersT parameterOutput fixed highs remaining table) (finalTable parameterOutput highs table cacheF)
  have hcons := sample_consistent (materialT parameterOutput fixed highs remaining table) seed
    (answersT parameterOutput fixed highs remaining table) (finalTable parameterOutput highs table cacheF)
  have hbound := sample_boundary (materialT parameterOutput fixed highs remaining table) seed
    (answersT parameterOutput fixed highs remaining table) (finalTable parameterOutput highs table cacheF)
  have hdata : GraphView.DataCorrect f' (truncateHash parameterOutput) seed
      (sampleData parameterOutput fixed highs remaining steps) := by
    have h := GraphView.publicData_correct f' _ seed _ hcons hbound steps
    rwa [publicData_T] at h
  have hcoord : GraphView.CoordinatesCorrect f' (truncateHash parameterOutput) seed table := by
    have h := GraphView.coordinates_correct f' _ seed _ hcons
    have heq := (Reduce.sampleCoordinates_eq (materialT parameterOutput fixed highs remaining table) seed
      (answersT parameterOutput fixed highs remaining table) (finalTable parameterOutput highs table cacheF)).trans
      (graphCoordinates_T parameterOutput fixed highs remaining table htable)
    unfold Assembly.sampleCoordinates at heq
    rwa [heq] at h
  obtain ⟨hverified, htrace, hgood⟩ := rich_support f' table (Internalize.internalize adversary) q
    (truncateHash parameterOutput) seed (sampleData parameterOutput fixed highs remaining steps) hdata hcoord
    outcome reveals entries hrun'
  have hencAgree : ∀ (key : OtsKey) (counter : Counter),
      f' (Wots.encodingInput (truncateHash parameterOutput) key.1 key.2.1 key.2.2
        (keyMessages (sampleData parameterOutput fixed highs remaining) key) counter) =
      preferCache prepared.2 f' (Wots.encodingInput (truncateHash parameterOutput) key.1 key.2.1 key.2.2
        (keyMessages (sampleData parameterOutput fixed highs remaining) key) counter) :=
    fun key counter => encoding_preferCache parameterOutput highs table cacheF prepared.2 f' seed
      (fun input hshort hnot => hagreeAll input hshort hnot) hgrow _ _ _ _
      (shortMessage_keyMessage _ _ _ _) counter
  have hselection := selection_of_agree (truncateHash parameterOutput)
    (keyMessages (sampleData parameterOutput fixed highs remaining)) prepared.1 f' (preferCache prepared.2 f')
    hstructPrep.2 hencAgree
  have hfull := fullTable_eq parameterOutput fixed highs remaining table prepared.1 f' seed hagreement
    hselection
  obtain ⟨forgery, log, verified⟩ := outcome
  simp only [outcomeWins, Bool.and_eq_true, decide_eq_true_eq] at hwin
  obtain ⟨⟨hvalid, hnotContains⟩, rfl⟩ := hwin
  exact bad_of_accepted hb parameterOutput fixed highs remaining steps table htable prepared.1 cacheF reveals entries
    f' seed hcons hbound hdata hcoord hfull hagree hcached hguess forgery log htrace hgood
    hverified.symm hvalid hnotContains

/-! ### The honest and the charged games are coupled -/

/-- A charged program against its honest form, followed by coupled continuations. -/
theorem corr_toHonest_bind {α β : Type} (computation : OracleComp CostSpec β)
    (left : β → OracleComp CostSpecH α) (right : β → OracleComp CostSpec α) (h : ∀ r, Corr (left r) (right r)) :
    Stop.HonestUnmarked SeedLength (simulateQ toHonest computation) →
      Corr (simulateQ toHonest computation >>= left) (computation >>= right) := by
  induction computation using OracleComp.inductionOn with
  | pure r =>
      intro _
      rw [simulateQ_pure, pure_bind, pure_bind]
      exact h r
  | query_bind input next ih =>
      intro hu
      rw [simulateQ_bind, simulateQ_spec_query] at hu ⊢
      rw [bind_assoc, bind_assoc]
      rcases input with (draw | bytes | coordinate) | (amount | honest)
      · change Stop.HonestUnmarked _ (liftM (CostSpecH.query (.inl (.inl draw))) >>= _) at hu
        rw [Stop.honestUnmarked_query_bind] at hu
        exact Corr.source (.inl draw) _ _ fun value => ih value (hu.2 value)
      · change Stop.HonestUnmarked _ (liftM (CostSpecH.query (.inr (.inr bytes))) >>= _) at hu
        rw [Stop.honestUnmarked_query_bind] at hu
        exact Corr.honest bytes (hu.1 bytes rfl) _ _ fun value => ih value (hu.2 value)
      · change Stop.HonestUnmarked _ (liftM (CostSpecH.query (.inl (.inr (.inr coordinate)))) >>= _) at hu
        rw [Stop.honestUnmarked_query_bind] at hu
        exact Corr.source (.inr (.inr coordinate)) _ _ fun value => ih value (hu.2 value)
      · change Stop.HonestUnmarked _ (Pure.pure () >>= _) at hu
        change Corr (Pure.pure () >>= _) _
        rw [pure_bind] at hu ⊢
        exact Corr.extra amount _ _ (ih () hu)
      · exact Empty.elim honest

/-- A hash computation read raw on both sides, followed by coupled continuations. -/
theorem corr_raw_bind {α β : Type} (computation : OracleComp HashSpec β)
    (left : β → OracleComp CostSpecH α) (right : β → OracleComp CostSpec α) (h : ∀ r, Corr (left r) (right r)) :
    Corr (simulateQ (fun q => liftM (CostSpecH.query (.inl (.inr (.inl q)))) :
        QueryImpl HashSpec (OracleComp CostSpecH)) computation >>= left)
      ((liftM computation : OracleComp CostSpec β) >>= right) := by
  induction computation using OracleComp.inductionOn with
  | pure r =>
      rw [simulateQ_pure, liftM_pure, pure_bind, pure_bind]
      exact h r
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, liftM_bind, bind_assoc, bind_assoc]
      exact Corr.source (.inr (.inl input)) _ _ fun value => ih value

open ForsPotential in
/-- The rest of the game, honest against charged. -/
theorem corr_advProg (parameter : PublicParameter) (data : PublicData)
    (M : OracleComp (OracleWorld + SigningSpec) Forgery) :
    ∀ L, Corr (advProgH parameter data M L) (advProg parameter data M L) := by
  induction M using OracleComp.inductionOn with
  | pure forgery =>
      intro L
      rw [advProgH_pure, advProg_pure]
      exact corr_raw_bind _ _ _ fun _ => Corr.pure _
  | query_bind input next ih =>
      intro L
      rcases input with (draw | bytes) | message
      · rw [advProgH_draw, advProg_draw]
        exact Corr.source (.inl draw) _ _ fun value => ih value L
      · rw [advProgH_hash, advProg_hash]
        exact Corr.source (.inr (.inl bytes)) _ _ fun value => ih value L
      · rw [advProgH_sign, advProg_sign, signCostSourceH_eq]
        refine corr_toHonest_bind _ _ _ (fun r => ih r _) ?_
        rw [← signCostSourceH_eq]
        exact Stop.honestUnmarked_signCostSourceH_of_length SeedLength
          (fun _ hx => hx.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h))) parameter data message

/-- The honest-reading rest of the game, with its whole outcome. -/
noncomputable def costRestXH (parameter : PublicParameter) (data : PublicData) (adversary : Adversary) :
    OracleComp CostSpecH Outcome := do
  let pk : PublicKey := ⟨data.root, parameter⟩
  let (forgery, log) ← (simulateQ (costInteractionH parameter data) (adversary.main pk)).run
  let verified ← liftRawH (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return (forgery, log, verified)

theorem costRestXH_eq (parameter : PublicParameter) (data : PublicData) (adversary : Adversary) :
    costRestXH parameter data adversary =
      ForsPotential.advProgH parameter data (adversary.main ⟨data.root, parameter⟩) [] := by
  unfold costRestXH ForsPotential.advProgH ForsPotential.finishGameH
  refine bind_congr fun r => ?_
  rcases r with ⟨forgery, log⟩
  simp only [List.nil_append]
  rfl

theorem costGameH_eq_map (parameter : PublicParameter) (data : PublicData) (adversary : Adversary) :
    costGame parameter data adversary = outcomeWins <$> ForsPotential.costGameXH parameter data adversary := by
  unfold ForsPotential.costGameXH
  rw [← costRestXH_eq]
  simp only [costGame, costRest, costRestXH, map_bind, map_pure, outcomeWins]

/-- The honest rich program: the honest-reading game capped at `q`, with its reveals. -/
noncomputable def richProgramH (adversary : Adversary) (q : Nat) (parameter : PublicParameter)
    (data : PublicData) : OracleComp CostSpecH (Option Outcome × List HiddenGraph.Coordinate) :=
  withReveals (cap (ForsPotential.costGameXH parameter data adversary) q)

theorem cap_costGameH_eq (adversary : Adversary) (q : Nat) (parameter : PublicParameter) (data : PublicData) :
    cap (costGame parameter data adversary) q =
      (fun result => Option.map outcomeWins result.1) <$> richProgramH adversary q parameter data := by
  rw [richProgramH, ← Functor.map_map, fst_withReveals, costGameH_eq_map, cap_map]

theorem corr_costGameX (parameter : PublicParameter) (data : PublicData) (adversary : Adversary) :
    Corr (ForsPotential.costGameXH parameter data adversary) (costGameX parameter data adversary) := by
  unfold ForsPotential.costGameXH costGameX
  refine Corr.tick _ _ _ ?_
  rw [ForsPotential.costRestX_eq]
  exact corr_advProg parameter data _ []

/-- **Honest stopped runs are charged stopped runs.** A finished stopped run of the honest rich
program at budget `q` is a finished stopped run of the charged rich program at a budget the charged
game cannot exhaust, with the same outcome, reveals and final cache, recording at most `q` inputs of
a seed's length. -/
theorem stopped_richH {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate)
    (table : HiddenGraph.Table) (adversary : Adversary) (q : Nat) (parameter : PublicParameter) (data : PublicData)
    (known : HiddenReveal.Knowledge Coordinate) (cache : QueryCache HashSpec)
    (value : Outcome) (reveals : List Coordinate) (entries : List (Entry HashInput)) (cacheF : QueryCache HashSpec)
    (hstop : some (((some value, reveals), entries), cacheF) ∈ support
      (HiddenOutside.stopped model table (erase (trace (richProgramH adversary q parameter data))) known cache)) :
    ∃ budget entries', seedMarks entries' ≤ q ∧ some (((some value, reveals), entries'), cacheF) ∈ support
      (HiddenOutside.stopped model table (erase (trace (richProgram adversary budget parameter data))) known cache) := by
  obtain ⟨budget, hbudget⟩ := exists_costAtMost (costGameX parameter data adversary)
  obtain ⟨⟨⟨o, rv⟩, entries'⟩, ⟨heq, hmarks⟩, hstop'⟩ :=
    ((corr_costGameX parameter data adversary).sim q budget hbudget).stopped model table known cache _ cacheF hstop
      (by simp [Finished])
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  exact ⟨budget, entries', hmarks, hstop'⟩

/-- **Win implication for the honest program.** -/
theorem win_implies_bad (hb : 0 < keptHeight topLayer) (adversary : Adversary) (q : Nat) (hq : q < 2 ^ 256)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (steps : Message → Randomness)
    (prepared : (OtsKey → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (table : HiddenGraph.Table)
    (htable : tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table)
    (outcome : Outcome) (reveals : List Coordinate) (entries : List (HiddenCost.Entry HashInput))
    (cacheF : QueryCache HashSpec)
    (hstop : some (((some outcome, reveals), entries), cacheF) ∈ support
      (HiddenOutside.stopped (sampleModel parameterOutput highs) table
        (HiddenCost.erase (HiddenCost.trace (richProgramH (Internalize.internalize adversary) q
          (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps))))
        (knownOf (truncateHash parameterOutput) fixed) prepared.2))
    (hwin : outcomeWins outcome = true) :
    CacheMatch.Bad (digestFreeTargets parameterOutput fixed highs remaining table prepared.1) cacheF ∨
      ForsCover (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining).root
        outcome reveals cacheF := by
  obtain ⟨budget, entries', hmarks, hstop'⟩ := stopped_richH _ table _ q _ _ _ _ outcome reveals entries cacheF hstop
  exact win_implies_badM hb adversary budget parameterOutput fixed highs remaining steps prepared hprepared table htable
    outcome reveals entries' cacheF hstop' hwin (lt_of_le_of_lt hmarks hq)

end FORS.Security.HiddenBridge
