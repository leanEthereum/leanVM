module

public import FORS.Reduction.UntilSeed
public import FORS.GraphView.PreparedSearch

@[expose] public section

section

/-! The "identical until a marked input" comparison (`UntilSeed`) for the cost interface with
honest reads (`GraphView.CostSpecH`). An honest read reads the answer function but is not recorded
in the trace, so the comparison holds for computations whose honest reads are all unmarked
(`HonestUnmarked`): an unmarked read reads the same answer under both functions. The honest
signer reads message-digest inputs and counter-search trials only (`honestUnmarked_signCostSourceH`),
none of which carries the seed. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.Stop

variable [Params]

open Completeness HiddenCost GraphView Concrete

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] encodingAttemptLimit digestAttemptLimit

/-- `fixedCostP` with honest reads: an honest read reads the fixed function at its raw input. -/
noncomputable def fixedCostPH (f : HashInput → HashOutput) (table : HiddenGraph.Table) :
    QueryImpl CostSpecH ProbComp
  | .inl (.inl draw) => liftM (unifSpec.query draw)
  | .inl (.inr (.inl input)) => pure (f input)
  | .inl (.inr (.inr coordinate)) => pure (table coordinate)
  | .inr (.inl _) => pure ()
  | .inr (.inr honest) => pure (f honest)

noncomputable def costRunH {α : Type} (f : HashInput → HashOutput) (table : HiddenGraph.Table)
    (computation : OracleComp CostSpecH α) : ProbComp (α × List (Entry HashInput)) :=
  simulateQ (fixedCostPH f table) (trace computation)

theorem costRunH_pure {α : Type} (f : HashInput → HashOutput) (table : HiddenGraph.Table) (value : α) :
    costRunH f table (pure value) = pure (value, []) := by
  simp [costRunH, trace_pure]

theorem costRunH_query_bind {α : Type} (f : HashInput → HashOutput) (table : HiddenGraph.Table)
    (input : CostSpecH.Domain) (next : CostSpecH.Range input → OracleComp CostSpecH α) :
    costRunH f table (liftM (CostSpecH.query input) >>= next) =
      fixedCostPH f table input >>= fun answer =>
        (fun result => (result.1, recorded input ++ result.2)) <$> costRunH f table (next answer) := by
  rw [costRunH, trace_query_bind, simulateQ_bind, simulateQ_spec_query]
  simp only [simulateQ_map, costRunH]

/-- The writer cost of `fixedCostSource` is the cost of the recorded trace. -/
theorem run_withAddCost_trace {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (impl : QueryImpl CostSpecH m) (computation : OracleComp CostSpecH α) :
    (simulateQ (impl.withAddCost sourceCost) computation).run =
      (fun result => (result.1, Multiplicative.ofAdd (traceCost result.2))) <$>
        simulateQ impl (trace computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp [trace_pure, traceCost]
  | query_bind input next ih =>
      rw [trace_query_bind, simulateQ_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_spec_query,
        WriterT.run_bind, QueryImpl.withAddCost_apply]
      simp only [WriterT.run_bind, map_bind, simulateQ_map, ih]
      simp [map_eq_bind_pure_comp, bind_assoc, traceCost_append,
        recorded_cost, ← ofAdd_add]

/-- `fixedCostSource`'s run is the cost run's, its cost the recorded trace's. -/
theorem evalDist_fixedCostSource {α : Type} (f : QueryImpl HashSpec Id) (table : HiddenGraph.Table)
    (computation : OracleComp CostSpecH α) :
    ((simulateQ (fixedCostSource f table) computation).run) =ᵈ ((fun result =>
        (result.1, Multiplicative.ofAdd (traceCost result.2))) <$> costRunH f table computation) := by
  rw [fixedCostSource, run_withAddCost_trace, costRunH]
  refine EvalDistEq.map ?_ _
  refine Assembly.evalDist_simulateQ_congr _ _ (fun input => ?_) _
  rcases input with (draw | (bytes | coordinate)) | (amount | honest)
  · exact (Assembly.evalDistEq_unifQuery_pmf draw).symm
  · exact evalDist_liftM_id (f bytes)
  · exact evalDist_liftM_id (table coordinate)
  · exact Assembly.evalDistEq_pure ()
  · exact evalDist_liftM_id (f honest)

theorem hits_append_recorded (marked : HashInput → Prop) (input : CostSpecH.Domain)
    (entries : List (Entry HashInput))
    (hinput : ∀ bytes, input = .inl (.inr (.inl bytes)) → ¬marked bytes) :
    Hits marked (recorded input ++ entries) ↔ Hits marked entries := by
  constructor
  · rintro ⟨bytes, hmem, hmarked⟩
    rw [List.mem_append] at hmem
    rcases hmem with hrec | htail
    · rcases input with (draw | (other | coordinate)) | (amount | honest) <;> simp [recorded] at hrec
      subst other
      exact absurd hmarked (hinput bytes rfl)
    · exact ⟨bytes, htail, hmarked⟩
  · rintro ⟨bytes, hmem, hmarked⟩
    exact ⟨bytes, List.mem_append_right _ hmem, hmarked⟩

/-! ### Honest reads off the marked inputs -/

/-- No honest read of the computation reads a marked input. -/
def HonestUnmarked (marked : HashInput → Prop) {α : Type} (computation : OracleComp CostSpecH α) : Prop :=
  OracleComp.construct (fun _ => True)
    (fun input _ next => (∀ honest, input = .inr (.inr honest) → ¬marked honest) ∧ ∀ value, next value)
    computation

theorem honestUnmarked_query_bind (marked : HashInput → Prop) {α : Type} (input : CostSpecH.Domain)
    (next : CostSpecH.Range input → OracleComp CostSpecH α) :
    HonestUnmarked marked (liftM (CostSpecH.query input) >>= next) ↔
      (∀ honest, input = .inr (.inr honest) → ¬marked honest) ∧ ∀ value, HonestUnmarked marked (next value) :=
  Iff.rfl

/-- **Identical until a marked input, with honest reads.** Changing the answer function on
marked inputs costs at most the probability that the trace records a marked raw input, when no
honest read is marked. -/
theorem probEvent_costRunH_le {α : Type} (f f₀ : HashInput → HashOutput) (table : HiddenGraph.Table)
    (marked : HashInput → Prop) (hagree : ∀ input, ¬marked input → f input = f₀ input)
    (computation : OracleComp CostSpecH α) (hhonest : HonestUnmarked marked computation)
    (event : α × List (Entry HashInput) → Prop) :
    Pr{let x ← costRunH f table computation}[event x] ≤
      Pr{let x ← costRunH f₀ table computation}[event x] +
        Pr{let result ← costRunH f₀ table computation}[Hits marked result.2] := by
  induction computation using OracleComp.inductionOn generalizing event with
  | pure value => simp [costRunH_pure]
  | query_bind input next ih =>
      obtain ⟨hhere, hrest⟩ := (honestUnmarked_query_bind marked input next).1 hhonest
      by_cases hmarked : ∃ bytes, input = .inl (.inr (.inl bytes)) ∧ marked bytes
      · obtain ⟨bytes, rfl, hbytes⟩ := hmarked
        have hone : Pr{let result ← costRunH f₀ table (liftM (CostSpecH.query (.inl (.inr (.inl bytes)))) >>= next)}[Hits marked result.2] = 1 := by
          refine OracleComp.prEvent_eq_one_of_forall_mem_support _ _ fun result hresult => ?_
          rw [costRunH_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨answer, _, hmap⟩ := hresult
          rw [support_map] at hmap
          obtain ⟨tail, _, rfl⟩ := hmap
          exact ⟨bytes, by simp [recorded], hbytes⟩
        rw [hone]
        exact (prEvent_le_one _).trans (le_add_self)
      · have hsame : fixedCostPH f table input = fixedCostPH f₀ table input := by
          rcases input with (draw | (bytes | coordinate)) | (amount | honest)
          · rfl
          · simp only [fixedCostPH]
            rw [hagree bytes (fun h => hmarked ⟨bytes, rfl, h⟩)]
          · rfl
          · rfl
          · simp only [fixedCostPH]
            rw [hagree honest (hhere honest rfl)]
        have hnot : ∀ bytes, input = .inl (.inr (.inl bytes)) → ¬marked bytes :=
          fun bytes heq h => hmarked ⟨bytes, heq, h⟩
        rw [costRunH_query_bind, costRunH_query_bind, hsame]
        simp only [OracleComp.prEvent_bind_eq_tsum, prEvent_map]
        rw [← ENNReal.tsum_add]
        refine ENNReal.tsum_le_tsum (fun answer => ?_)
        rw [← mul_add]
        refine mul_le_mul' le_rfl ?_
        have h := ih answer (hrest answer) (event ∘ fun result : α × List (Entry HashInput) =>
          (result.1, recorded input ++ result.2))
        simp only [hits_append_recorded marked input _ hnot]
        simpa only [Function.comp_def] using h

/-! ### Capping the original budget, with honest reads -/

theorem capH_pure {α : Type} (value : α) (budget : Nat) :
    cap (pure value : OracleComp CostSpecH α) budget = pure (some value) := rfl

theorem capH_query_bind {α : Type} (input : CostSpecH.Domain)
    (next : CostSpecH.Range input → OracleComp CostSpecH α) (budget : Nat) :
    cap (liftM (CostSpecH.query input) >>= next) budget =
      if sourceCost input ≤ budget then
        liftM (CostSpecH.query input) >>= fun value => cap (next value) (budget - sourceCost input)
      else pure none := rfl

/-- Runs within the budget are runs of the capped program, with honest reads. -/
theorem probEvent_costRunH_le_cap {α : Type} (f : HashInput → HashOutput) (table : HiddenGraph.Table)
    (computation : OracleComp CostSpecH α) (budget : Nat) (event : α → Prop) :
    Pr{let result ← costRunH f table computation}[event result.1 ∧ traceCost result.2 ≤ budget] ≤
      Pr{let result ← costRunH f table (cap computation budget)}[∃ value, result.1 = some value ∧ event value] := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value =>
      rw [capH_pure, costRunH_pure, costRunH_pure]
      simp [traceCost]
  | query_bind input next ih =>
      rw [capH_query_bind]
      split
      · rename_i hcost
        rw [costRunH_query_bind, costRunH_query_bind]
        simp only [OracleComp.prEvent_bind_eq_tsum, prEvent_map]
        refine ENNReal.tsum_le_tsum (fun answer => mul_le_mul' le_rfl ?_)
        refine le_trans (prEvent_mono_of_support _ _ _ ?_) (ih answer (budget - sourceCost input))
        intro result _ hresult
        refine ⟨hresult.1, ?_⟩
        have h : traceCost (recorded input ++ result.2) ≤ budget := hresult.2
        rw [traceCost_append, recorded_cost] at h
        omega
      · rename_i hcost
        rw [costRunH_query_bind]
        simp only [OracleComp.prEvent_bind_eq_tsum, prEvent_map]
        refine le_trans (le_of_eq ?_) bot_le
        refine ENNReal.tsum_eq_zero.2 (fun answer => ?_)
        rw [mul_eq_zero]
        right
        refine prEvent_eq_zero_of_forall_mem_support _ _ fun result _ hresult => ?_
        have h : traceCost (recorded input ++ result.2) ≤ budget := hresult.2
        rw [traceCost_append, recorded_cost] at h
        omega

/-! ### The honest signer reads no marked input -/

theorem honestUnmarked_pure (marked : HashInput → Prop) {α : Type} (value : α) :
    HonestUnmarked marked (pure value : OracleComp CostSpecH α) := trivial

theorem honestUnmarked_bind (marked : HashInput → Prop) {α β : Type} {first : OracleComp CostSpecH α}
    {next : α → OracleComp CostSpecH β} (hfirst : HonestUnmarked marked first)
    (hnext : ∀ value, HonestUnmarked marked (next value)) :
    HonestUnmarked marked (first >>= next) := by
  induction first using OracleComp.inductionOn with
  | pure value => simpa only [pure_bind] using hnext value
  | query_bind input rest ih =>
      rw [bind_assoc]
      obtain ⟨hin, hrest⟩ := (honestUnmarked_query_bind marked input rest).1 hfirst
      exact (honestUnmarked_query_bind marked input _).2 ⟨hin, fun value => ih value (hrest value)⟩

theorem honestUnmarked_query_of_ne (marked : HashInput → Prop) (input : CostSpecH.Domain)
    (hinput : ∀ honest, input ≠ .inr (.inr honest)) :
    HonestUnmarked marked (liftM (CostSpecH.query input) : OracleComp CostSpecH _) := by
  rw [← bind_pure (liftM (CostSpecH.query input))]
  exact (honestUnmarked_query_bind marked input _).2
    ⟨fun honest h => absurd h (hinput honest), fun _ => trivial⟩

theorem honestUnmarked_reveal (marked : HashInput → Prop) (coordinate : HiddenGraph.Coordinate) :
    HonestUnmarked marked (reveal (H := HashInput) (D := HashInput) (R := HashOutput) coordinate) :=
  honestUnmarked_query_of_ne marked _ fun _ h => by cases h

theorem honestUnmarked_sequenceFin (marked : HashInput → Prop) {α : Type} :
    ∀ {n : ℕ} (computation : Fin n → OracleComp CostSpecH α),
      (∀ i, HonestUnmarked marked (computation i)) → HonestUnmarked marked (Concrete.sequenceFin computation)
  | 0, _, _ => honestUnmarked_pure marked _
  | n + 1, computation, h => by
      unfold Concrete.sequenceFin
      exact honestUnmarked_bind marked (h 0) fun _ =>
        honestUnmarked_bind marked (honestUnmarked_sequenceFin marked (fun i : Fin n => computation i.succ)
          fun i => h i.succ) fun _ => honestUnmarked_pure marked _

theorem honestUnmarked_sequenceDep (marked : HashInput → Prop) :
    ∀ {n : ℕ} {α : Fin n → Type} (computation : (i : Fin n) → OracleComp CostSpecH (Option (α i))),
      (∀ i, HonestUnmarked marked (computation i)) → HonestUnmarked marked (sequenceDep computation)
  | 0, _, _, _ => honestUnmarked_pure marked _
  | n + 1, α, computation, h => by
      rw [sequenceDep]
      refine honestUnmarked_bind marked (h (Fin.last n)) fun last => ?_
      cases last with
      | none => exact honestUnmarked_pure marked _
      | some last =>
          refine honestUnmarked_bind marked
            (honestUnmarked_sequenceDep marked (α := fun i => α i.castSucc) (fun i => computation i.castSucc)
              fun i => h i.castSucc) fun init => ?_
          cases init with
          | none => exact honestUnmarked_pure marked _
          | some init => exact honestUnmarked_pure marked _

theorem honestUnmarked_liftCoins (marked : HashInput → Prop) {α : Type} (computation : ProbComp α) :
    HonestUnmarked marked (liftM computation : OracleComp CostSpecH α) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact honestUnmarked_pure marked value
  | query_bind draw rest ih =>
      rw [liftM_bind]
      exact (honestUnmarked_query_bind marked (.inl (.inl draw)) _).2 ⟨fun _ h => (by cases h), ih⟩

/-- A hash computation all of whose queries are unmarked, run through honest reads, reads no
marked input. -/
theorem honestUnmarked_liftHonest (marked : HashInput → Prop) {α : Type} (computation : OracleComp HashSpec α)
    (h : computation.IsQueryBoundP marked 0) : HonestUnmarked marked (liftHonest computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact honestUnmarked_pure marked value
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      have hin : ¬marked input := by
        rcases h.1 with hnot | hzero
        · exact hnot
        · omega
      have hnext : ∀ value, (next value).IsQueryBoundP marked 0 := fun value => by
        have := h.2 value
        split at this <;> simpa using this
      have hlift : liftHonest (liftM (HashSpec.query input) >>= next) =
          HiddenCost.honestRead (D := HashInput) (R := HashOutput) (ι := HiddenGraph.Coordinate) input >>=
            fun value => liftHonest (next value) := by
        simp only [liftHonest, simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
          OracleQuery.input_query, id_map, honestHash]
      rw [hlift]
      exact (honestUnmarked_query_bind marked (.inr (.inr input)) _).2
        ⟨fun honest h => by cases h; exact hin, fun value => ih value (hnext value)⟩

/-- A message-digest call queries one message-digest input. -/
theorem noMarked_messageDigestCall (marked : HashInput → Prop)
    (hmsg : ∀ parameter root message randomness call, ¬marked (messageDigestInput parameter root message randomness call))
    (parameter : PublicParameter) (root : Digest) (message : Message) (randomness : Randomness)
    (call : DigestCall) :
    (messageDigestCall parameter root message randomness call : OracleComp HashSpec HashOutput).IsQueryBoundP
      marked 0 := by
  have hq : (oracleHash (messageDigestInput parameter root message randomness call) :
      OracleComp HashSpec HashOutput) = liftM (HashSpec.query (messageDigestInput parameter root message randomness call)) :=
    rfl
  rw [messageDigestCall, hq, ← bind_pure (liftM (HashSpec.query _)), isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl (hmsg _ _ _ _ _), fun _ => trivial⟩

theorem noMarked_sequenceFin (marked : HashInput → Prop) {α : Type} :
    ∀ {n : ℕ} (computation : Fin n → OracleComp HashSpec α),
      (∀ i, (computation i).IsQueryBoundP marked 0) → (Concrete.sequenceFin computation).IsQueryBoundP marked 0
  | 0, _, _ => trivial
  | n + 1, computation, h => by
      unfold Concrete.sequenceFin
      exact isQueryBoundP_bind_zero _ _ (h 0) fun _ =>
        isQueryBoundP_bind_zero _ _ (noMarked_sequenceFin marked (fun i : Fin n => computation i.succ)
          fun i => h i.succ) fun _ => trivial

theorem noMarked_messageDigest (marked : HashInput → Prop)
    (hmsg : ∀ parameter root message randomness call, ¬marked (messageDigestInput parameter root message randomness call))
    (parameter : PublicParameter) (root : Digest) (message : Message) (randomness : Randomness) :
    (messageDigest parameter root message randomness : OracleComp HashSpec MessageDigest).IsQueryBoundP marked 0 := by
  rw [messageDigest]
  exact isQueryBoundP_bind_zero _ _ (noMarked_sequenceFin marked _ fun call =>
    noMarked_messageDigestCall marked hmsg parameter root message randomness call) fun _ => trivial

theorem noMarked_search (marked : HashInput → Prop) (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (message : HashInput)
    (htrial : ∀ start, ¬marked (trialInput parameter lay tree leaf message start)) :
    ∀ attempts start, (ReferenceChoice.search parameter lay tree leaf message attempts start).IsQueryBoundP marked 0
  | 0, _ => by
      rw [ReferenceChoice.search]
      trivial
  | attempts + 1, start => by
      rw [search_step, isQueryBoundP_query_bind_iff]
      refine ⟨Or.inl (htrial start), fun output => ?_⟩
      rw [ite_eq_right (htrial start)]
      cases TargetSum.decodeDigest (truncateHash output) with
      | none => exact noMarked_search marked parameter lay tree leaf message htrial attempts (start + 1)
      | some _ => trivial

/-- **The honest signer reads no marked input** when message-digest inputs and counter-search
trials are unmarked. -/
theorem honestUnmarked_signCostSourceH (marked : HashInput → Prop)
    (hmsg : ∀ parameter root message randomness call, ¬marked (messageDigestInput parameter root message randomness call))
    (parameter : PublicParameter) (data : PublicData)
    (htrial : ∀ lay tree leaf start, ¬marked (trialInput parameter lay tree leaf (data.keyMessage lay tree leaf) start))
    (message : Message) :
    HonestUnmarked marked (signCostSourceH parameter data message) := by
  have hfinish : ∀ randomness, HonestUnmarked marked (finishCostSourceH parameter data message randomness) := by
    intro randomness
    rw [finishCostSourceH]
    refine honestUnmarked_bind marked (honestUnmarked_liftHonest marked _
      (noMarked_messageDigest marked hmsg parameter data.root message randomness)) fun digest => ?_
    refine honestUnmarked_bind marked (honestUnmarked_sequenceDep marked _ fun lay =>
      honestUnmarked_liftHonest marked _ (noMarked_search marked parameter lay _ _ _
        (htrial lay _ _) _ _)) fun found => ?_
    cases found with
    | none => exact honestUnmarked_pure marked _
    | some found =>
        refine honestUnmarked_bind marked (honestUnmarked_sequenceFin marked _ fun lay =>
          honestUnmarked_sequenceFin marked _ fun chain => honestUnmarked_reveal marked _) fun values => ?_
        refine honestUnmarked_bind marked (honestUnmarked_sequenceFin marked _ fun κ => ?_)
          fun _ => honestUnmarked_pure marked _
        rw [treeCostSourceH]
        exact honestUnmarked_bind marked (honestUnmarked_sequenceFin marked _ fun _ =>
          honestUnmarked_reveal marked _) fun _ => honestUnmarked_pure marked _
  have hloop : ∀ step attempts randomness,
      HonestUnmarked marked (signCostSourceLoopH parameter data message step attempts randomness) := by
    intro step attempts
    induction attempts with
    | zero => intro randomness; rw [signCostSourceLoopH]; exact honestUnmarked_pure marked _
    | succ attempts ih =>
        intro randomness
        rw [signCostSourceLoopH]
        refine honestUnmarked_bind marked (honestUnmarked_liftHonest marked _
          (noMarked_messageDigestCall marked hmsg parameter data.root message randomness firstCall))
          fun first => ?_
        split
        · exact hfinish randomness
        · exact ih (randomness + step)
  rw [signCostSourceH]
  exact honestUnmarked_bind marked (honestUnmarked_liftCoins marked _) fun start => hloop _ _ start

/-! ### The marked inputs and the signer's: lengths -/

theorem keyMessage_length (data : PublicData) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    (data.keyMessage lay tree leaf).length = 16 := by
  unfold PublicData.keyMessage
  split <;> exact bytesLE_length _ _

/-- A counter-search trial of a key's message: 68 bytes. -/
theorem trialInput_keyMessage_length (parameter : PublicParameter) (data : PublicData) (lay : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (start : ℕ) :
    (trialInput parameter lay tree leaf (data.keyMessage lay tree leaf) start).length = 68 := by
  rw [trialInput, tweakableHashInput_length, List.length_append, keyMessage_length, bytesBE_length]

theorem messageDigestInput_length (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) (call : DigestCall) :
    (messageDigestInput parameter root message randomness call).length = 84 := by
  simp only [messageDigestInput, List.length_append, bytesLE_length, bytesBE_length]

/-- An input naming the seed: 80 bytes (`PK.seed || ADRS || SK.seed`) or 44 (`leanSPHINCS || SK.seed || d`). -/
theorem seedHit_length {input : HashInput} {seed : MasterSeed} (h : SeedGuess.SeedHit input seed) :
    input.length = 80 ∨ input.length = 44 := by
  rcases h with ⟨parameter, domain, rfl⟩ | ⟨domain, rfl⟩
  · left
    simp only [keygenHashInput, fieldBytes, List.length_append, bytesLE_length, bytesBE_length]
  · right
    simp only [keySeedInput, seedTag, List.length_append, bytesLE_length, List.length_cons, List.length_nil]

/-- **The honest signer reads no input of a marked length**: a marker that holds only at 44, 80 or
93 bytes (the seed's inputs, `SeedGuess.SeedHit`, and the randomizer's, `randomizerHashInput`)
marks no honest read of the signer. -/
theorem honestUnmarked_signCostSourceH_of_length (marked : HashInput → Prop)
    (hlength : ∀ input, marked input → input.length = 44 ∨ input.length = 80 ∨ input.length = 93)
    (parameter : PublicParameter) (data : PublicData) (message : Message) :
    HonestUnmarked marked (signCostSourceH parameter data message) :=
  honestUnmarked_signCostSourceH marked
    (fun parameter root message randomness call h => by
      have := hlength _ h
      rw [messageDigestInput_length] at this
      omega)
    parameter data
    (fun lay tree leaf start h => by
      have := hlength _ h
      rw [trialInput_keyMessage_length] at this
      omega)
    message

end FORS.Security.Stop

end
