import FORS.Classification.Accepted

/-! Deterministic core: a winning non-stopped run of the rich program yields a cached hit of
a fixed target or a covered FORS digest. -/

open OracleComp OracleSpec

namespace FORS.Security.HiddenBridge

variable [Params]

open Concrete Completeness Graph GraphCorrectness TargetAssignment HiddenGraph Assembly SeedModel Reduce Eager

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable


/-! ### The honest counter is the canonical one -/

theorem otsSignFrom_firstEncoding (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (seed : MasterSeed) (message : HashInput) :
    ∀ (attempts start : Nat) {counter : Counter} {values : ChainIndex → Digest},
      evalWithAnswerFn f (Seeded.otsSignFrom parameter lay tree leaf seed message attempts start
          : OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) = some (counter, values) →
      ∃ word, Prefix.firstEncoding f parameter lay tree leaf message attempts start = some (counter, word) := by
  intro attempts
  induction attempts with
  | zero => intro start counter values h; simp [Seeded.otsSignFrom] at h
  | succ attempts ih =>
      intro start counter values h
      rw [Seeded.otsSignFrom, evalWithAnswerFn_bind] at h
      cases hencode : evalWithAnswerFn f (encode parameter lay tree leaf message
          (BitVec.ofNat counterBits start) : OracleComp HashSpec (Option Encoding)) with
      | none =>
          rw [hencode] at h
          obtain ⟨word, hword⟩ := ih (start + 1) h
          exact ⟨word, by simp only [Prefix.firstEncoding, hencode, hword]⟩
      | some encoding =>
          rw [hencode] at h
          simp only [eval_sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
            Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact ⟨encoding, by simp only [Prefix.firstEncoding, hencode]⟩

theorem honest_counter (f : QueryImpl HashSpec Id) (sk : Seeded.SecretKey) (message : Message)
    (randomness : Randomness) (signature : Signature)
    (hland : Landed sk.parameter (digestIndex (Completeness.digestValue f sk message randomness)))
    (hsign : evalWithAnswerFn f (Seeded.finishSign sk message randomness) = some signature)
    (lay : Layer) :
    SignatureWitness.chosenCounter f sk.parameter sk.seed
      (SignatureWitness.index f ⟨sk.root, sk.parameter⟩ message signature) lay =
        some (signature.layers lay).counter := by
  obtain ⟨-, -, hlayers⟩ := Completeness.finishSign_spec f sk message randomness hland hsign
  obtain ⟨hots, -⟩ := Completeness.signLayer_spec f sk _ lay (hlayers lay)
  obtain ⟨word, hword⟩ := otsSignFrom_firstEncoding f sk.parameter lay _ _ sk.seed _
    encodingAttemptLimit 0 hots
  have hindex : SignatureWitness.index f ⟨sk.root, sk.parameter⟩ message signature =
      digestIndex (Completeness.digestValue f sk message signature.randomness) := rfl
  rw [hindex]
  simp only [SignatureWitness.chosenCounter, ReferenceChoice.selection]
  rw [SignatureWitness.canonicalMessage_eq, hword]
  rfl

/-! ### The fixed comparison-world events -/

section Events

variable (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
  (remaining : RemainingOutputs)

/-- Material of the sample whose hidden coordinates are the table's. -/
noncomputable def materialT (table : HiddenGraph.Table) : SeedModel.Material :=
  splitMaterial parameterOutput highs remaining (mix (truncateHash parameterOutput) fixed table)

noncomputable def answersT (table : HiddenGraph.Table) : CanonicalGraphLabels :=
  splitAnswers highs remaining (mix (truncateHash parameterOutput) fixed table)

/-- Encoding targets fixed by the preparation's search results. -/
noncomputable def encTable (parameter : PublicParameter) (message : OtsKey → HashInput)
    (results : OtsKey → Option (Counter × Encoding)) : TargetAssignment.Table := fun fields =>
  (encodingAt fields).map fun key =>
    ⟨(results key).map (fun pair => Wots.encodingInput parameter key.1 key.2.1 key.2.2 (message key) pair.1),
      Completeness.pack (((results key).map Prod.snd).getD ReferenceChoice.dummyWord)⟩

/-- All fixed targets of one sample, hidden table and preparation. -/
noncomputable def compTable (table : HiddenGraph.Table) (results : OtsKey → Option (Counter × Encoding)) :
    TargetAssignment.Table := fun fields =>
  match positionAt fields with
  | some _ => referenceTable (truncateHash parameterOutput)
      (materialOts (materialT parameterOutput fixed highs remaining table))
      (materialFts (materialT parameterOutput fixed highs remaining table))
      (PrunedGraph.active (truncateHash parameterOutput))
      (PrunedGraph.boundary (truncateHash parameterOutput)
        (materialSurrogates (materialT parameterOutput fixed highs remaining table)))
      (labelsOf (materialT parameterOutput fixed highs remaining table)
        (answersT parameterOutput fixed highs remaining table)) fields
  | none => encTable (truncateHash parameterOutput)
      (keyMessages (sampleData parameterOutput fixed highs remaining)) results fields

end Events

/-- The verifier's message digest of a forgery, read from a cache. -/
def cachedDigest (cache : QueryCache HashSpec) (parameter : PublicParameter) (root : Digest)
    (message : Message) (randomness : Randomness) : Option MessageDigest :=
  (Completeness.allSome (α := fun _ => HashOutput) fun call : DigestCall =>
    cache (tweakableHashInput parameter (.message call) (messageDigestPayload root message randomness))).map
    truncateMessageDigest

/-- FORS leaves whose secret the run revealed. -/
noncomputable def revealedSet (reveals : List HiddenGraph.Coordinate) : Disclosures := fun index κ =>
  Finset.univ.filter fun leaf => HiddenGraph.Coordinate.fors index κ leaf 0 ∈ reveals

/-- A cached, landed digest of an unsigned message-randomizer pair whose FORS secrets were all
revealed by the run. -/
def ForsCover (parameter : PublicParameter) (root : Digest) (outcome : Outcome)
    (reveals : List HiddenGraph.Coordinate) (cache : QueryCache HashSpec) : Prop :=
  SigningTranscript.Valid outcome.2.1 ∧
  ∃ digest, cachedDigest cache parameter root outcome.1.message outcome.1.signature.randomness = some digest ∧
    Landed parameter (digestIndex digest) ∧
    (∀ entry ∈ outcome.2.1, ∀ signature, entry.2 = some signature →
      ¬(entry.1 = outcome.1.message ∧ signature.randomness = outcome.1.signature.randomness)) ∧
    Covered (revealedSet reveals) (fullDigestView digest)

/-! ### Auxiliary facts for one sample -/

section Aux

variable (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
  (remaining : RemainingOutputs)

theorem mix_agree_fixed (table : HiddenGraph.Table) :
    ∀ coordinate, KnownCoordinate (truncateHash parameterOutput) coordinate →
      mix (truncateHash parameterOutput) fixed table coordinate = fixed coordinate :=
  fun coordinate h => mix_known _ fixed table coordinate h

theorem graphCoordinates_T (table : HiddenGraph.Table)
    (htable : tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table) :
    graphCoordinates (materialT parameterOutput fixed highs remaining table)
      (answersT parameterOutput fixed highs remaining table) = table := by
  unfold materialT answersT
  rw [graphCoordinates_split, masked_mix, htable]

theorem publicData_T (table : HiddenGraph.Table) (steps : Message → Randomness) :
    GraphView.publicData (labelsOf (materialT parameterOutput fixed highs remaining table)
      (answersT parameterOutput fixed highs remaining table)) steps =
      sampleData parameterOutput fixed highs remaining steps :=
  publicData_agree parameterOutput highs remaining _ fixed steps (mix_agree_fixed parameterOutput fixed table)

/-- Away from the chosen seed's derivations, the consistent preparation is the hidden-row oracle. -/
theorem sampleFn_answer (table : HiddenGraph.Table)
    (htable : tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table)
    (seed : MasterSeed) (outside : Eager.Table) (input : HashInput)
    (hnot : ¬SeedGuess.SeedHit input seed) :
    sampleFn (materialT parameterOutput fixed highs remaining table) seed
        (answersT parameterOutput fixed highs remaining table) outside input =
      HiddenRows.answer (sampleModel parameterOutput highs) table
        (outsideFn (splitMaterial parameterOutput highs remaining fixed)
          (splitAnswers highs remaining fixed) outside) input := by
  rw [Reduce.sampleFn_agree _ _ _ _ _ hnot, graphFn_eq_answer,
    graphCoordinates_T parameterOutput fixed highs remaining table htable]
  unfold sampleModel
  rw [rowModel_answer]
  have hparameter : parameter (materialT parameterOutput fixed highs remaining table) =
      truncateHash parameterOutput := rfl
  rw [hparameter]
  unfold materialT answersT
  rw [answer_congr_high _ _ _ _ (fun address => highs address.outputCoordinate) _
    (fun address hactive => highHalves_split parameterOutput highs remaining _ address hactive)]
  unfold outsideFn
  rw [structCache_agree parameterOutput highs remaining _ fixed (mix_agree_fixed parameterOutput fixed table)]

end Aux

/-- The hidden-row oracle over the structural cache and a table read off a final cache is the
final-cache oracle, on every short input. -/
theorem answer_extend_final {A : Type} (model : HiddenRows.Model HashInput HashOutput A HiddenGraph.Coordinate)
    (table : HiddenGraph.Table) (base cacheF : QueryCache HashSpec)
    (hbase : ∀ input answer, base input = some answer → cacheF input = some answer)
    (input : HashInput) (hshort : Short.IsShort input) :
    HiddenRows.answer model table (extend base (fun short => finalFn model table cacheF short.val)) input =
      finalFn model table cacheF input := by
  have houtside : extend base (fun short => finalFn model table cacheF short.val) input =
      (cacheF input).getD 0 ∨ ∃ query, model.parse input = some query ∧
        query.2 = table (model.incoming query.1) := by
    unfold extend
    cases hb : base input with
    | some answer => left; rw [hbase _ _ hb]; rfl
    | none =>
        simp only [Option.getD_none, hshort, ↓reduceDIte]
        unfold finalFn HiddenRows.answer
        cases hp : model.parse input with
        | none => left; rfl
        | some query =>
            by_cases hmatch : query.2 = table (model.incoming query.1)
            · right; exact ⟨query, rfl, hmatch⟩
            · left; simp [hmatch]
  unfold finalFn HiddenRows.answer
  cases hp : model.parse input with
  | none =>
      rcases houtside with h | ⟨query, hq, _⟩
      · exact h
      · rw [hp] at hq; cases hq
  | some query =>
      simp only [Option.elim_some]
      split_ifs with hmatch
      · rfl
      · rcases houtside with h | ⟨query', hq, hmatch'⟩
        · exact h
        · rw [hp] at hq
          cases hq
          exact absurd hmatch' hmatch

/-- Preparation facts: the structural cache persists, and every key's encoding search result is
the one recorded, for any function agreeing with the prepared cache. -/
theorem preparation_support (parameter : PublicParameter) (message : OtsKey → HashInput)
    (base : QueryCache HashSpec) (prepared : (OtsKey → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support ((simulateQ randomOracle (searchAll parameter message)).run base))
    (f : QueryImpl HashSpec Id) (hf : prepared.2.AgreesWithFn f) :
    base ≤ prepared.2 ∧ ∀ key : OtsKey, Prefix.firstEncoding f parameter key.1 key.2.1 key.2.2 (message key)
      encodingAttemptLimit 0 = prepared.1 key := by
  obtain ⟨hle, heval⟩ := replay_hash_support _ base prepared.1 prepared.2 hprepared f hf
  refine ⟨hle, fun key => ?_⟩
  rw [← heval, searchAll]
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_sequenceFin]
  rw [← ReferenceChoice.eval_search]

/-! ### Runs: short entries, cost, seed choice and support transfer -/

theorem OnlyC.withReveals {α : Type} {computation : OracleComp GraphView.CostSpec α}
    (h : OnlyC computation) : OnlyC (withReveals computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact OnlyC.pure' _
  | query_bind input next ih =>
      obtain ⟨hinput, hnext⟩ := onlyC_query_bind h
      rw [withReveals_query_bind']
      exact OnlyC.bind (OnlyC.query hinput) (fun value => OnlyC.map _ (ih value (hnext value)))

theorem costRun_entries_short {α : Type} (f : HashInput → HashOutput) (table : HiddenGraph.Table)
    (computation : OracleComp GraphView.CostSpec α) (h : OnlyC computation)
    (result : α × List (HiddenCost.Entry HashInput)) (hresult : result ∈ support (Stop.costRun f table computation)) :
    ∀ input, Sum.inl input ∈ result.2 → Short.IsShort input := by
  induction computation using OracleComp.inductionOn generalizing result with
  | pure value =>
      rw [Stop.costRun_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      intro input hinput
      simp at hinput
  | query_bind input next ih =>
      obtain ⟨hinput, hnext⟩ := onlyC_query_bind h
      rw [Stop.costRun_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨answer, _, hresult⟩ := hresult
      rw [support_map] at hresult
      obtain ⟨tail, htail, rfl⟩ := hresult
      intro bytes hbytes
      rcases List.mem_append.mp hbytes with hrec | hrest
      · rcases input with (draw | (other | coordinate)) | amount <;> simp [HiddenCost.recorded] at hrec
        subst hrec
        by_contra hlong
        exact hinput hlong
      · exact ih answer (hnext answer) tail htail bytes hrest

theorem costRun_withReveals_cap_cost {α : Type} (f : HashInput → HashOutput) (table : HiddenGraph.Table)
    (computation : OracleComp GraphView.CostSpec α) (budget : Nat)
    (result : (Option α × List HiddenGraph.Coordinate) × List (HiddenCost.Entry HashInput))
    (hresult : result ∈ support (Stop.costRun f table (withReveals (HiddenCost.cap computation budget)))) :
    HiddenCost.traceCost result.2 ≤ budget := by
  induction computation using OracleComp.inductionOn generalizing budget result with
  | pure value =>
      change result ∈ support (Stop.costRun f table (withReveals
        (pure (some value) : OracleComp GraphView.CostSpec _))) at hresult
      rw [costRun_withReveals_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      simp [HiddenCost.traceCost]
  | query_bind input next ih =>
      rw [cap_query_bind_gen] at hresult
      split at hresult
      · rename_i hcost
        rw [costRun_withReveals_query_bind, mem_support_bind_iff] at hresult
        obtain ⟨answer, _, hresult⟩ := hresult
        rw [support_map] at hresult
        obtain ⟨tail, htail, rfl⟩ := hresult
        have h := ih answer _ tail htail
        rw [HiddenCost.traceCost_append, HiddenCost.recorded_cost]
        omega
      · rw [costRun_withReveals_pure, support_pure, Set.mem_singleton_iff] at hresult
        subst result
        simp [HiddenCost.traceCost]

theorem ordinary_length_le_cost (entries : List (HiddenCost.Entry HashInput)) :
    (entries.filterMap fun entry => match entry with
      | .inl input => some input
      | .inr _ => none).length ≤ HiddenCost.traceCost entries := by
  induction entries with
  | nil => simp
  | cons entry entries ih =>
      cases entry with
      | inl input =>
          simp only [List.filterMap_cons, List.length_cons, HiddenCost.traceCost, List.map_cons,
            List.sum_cons, HiddenCost.entryCost] at ih ⊢
          omega
      | inr amount =>
          simp only [List.filterMap_cons, HiddenCost.traceCost, List.map_cons, List.sum_cons] at ih ⊢
          omega

/-- A seed named by none of fewer than 2^256 inputs. -/
theorem exists_seed_avoiding (inputs : List HashInput) (hlength : inputs.length < 2 ^ 256) :
    ∃ seed : MasterSeed, ∀ input ∈ inputs, ¬SeedGuess.SeedHit input seed := by
  let named : Finset MasterSeed := (inputs.filterMap SeedGuess.parseSeed).toFinset
  have hcard : named.card < (Finset.univ : Finset MasterSeed).card := by
    rw [Finset.card_univ]
    calc named.card ≤ (inputs.filterMap SeedGuess.parseSeed).length := List.toFinset_card_le _
      _ ≤ inputs.length := List.length_filterMap_le _ _
      _ < 2 ^ 256 := hlength
      _ = Fintype.card MasterSeed := by simp
  obtain ⟨seed, -, hseed⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨seed, fun input hinput hhit => hseed ?_⟩
  have hparse := (SeedGuess.parseSeed_eq_some_iff input seed).mpr hhit
  simp only [named, List.mem_toFinset, List.mem_filterMap]
  exact ⟨input, hinput, hparse⟩

/-- A fixed-function run depends only on the function at its recorded ordinary inputs. -/
theorem costRun_support_congr {α : Type} (f g : HashInput → HashOutput) (table : HiddenGraph.Table)
    (computation : OracleComp GraphView.CostSpec α) (result : α × List (HiddenCost.Entry HashInput))
    (hresult : result ∈ support (Stop.costRun f table computation))
    (hagree : ∀ input, Sum.inl input ∈ result.2 → f input = g input) :
    result ∈ support (Stop.costRun g table computation) := by
  induction computation using OracleComp.inductionOn generalizing result with
  | pure value => simpa [Stop.costRun_pure] using hresult
  | query_bind input next ih =>
      rw [Stop.costRun_query_bind, mem_support_bind_iff] at hresult ⊢
      obtain ⟨answer, hanswer, hresult⟩ := hresult
      rw [support_map] at hresult
      obtain ⟨tail, htail, rfl⟩ := hresult
      have htailAgree : ∀ x, Sum.inl x ∈ tail.2 → f x = g x :=
        fun x hx => hagree x (List.mem_append_right _ hx)
      refine ⟨answer, ?_, by rw [support_map]; exact ⟨tail, ih answer tail htail htailAgree, rfl⟩⟩
      rcases input with (draw | (bytes | coordinate)) | amount
      · exact hanswer
      · have hb := hagree bytes (by simp [HiddenCost.recorded])
        simpa [Stop.fixedCostP, hb] using hanswer
      · exact hanswer
      · exact hanswer

/-! ### Reachable coordinates of the sample model -/

theorem knownOf_known (parameter : PublicParameter) (fixed : HiddenGraph.Table) (coordinate : Coordinate)
    (value : Digest) (h : knownOf parameter fixed coordinate = some value) :
    KnownCoordinate parameter coordinate := by
  unfold knownOf at h
  split at h
  · assumption
  · cases h

/-- A reachable FORS secret was revealed: it is neither known nor a row output. -/
theorem reach_fors (parameterOutput : HashOutput) (highs : CoordinateHighs) (fixed : HiddenGraph.Table)
    (reveals : List Coordinate) (coordinate : Coordinate)
    (h : Reach (sampleModel parameterOutput highs) (knownOf (truncateHash parameterOutput) fixed)
      reveals coordinate) :
    ∀ index κ leaf, coordinate = .fors index κ leaf 0 → Coordinate.fors index κ leaf 0 ∈ reveals := by
  induction h with
  | known coordinate value hvalue =>
      intro index κ leaf heq
      subst heq
      have := knownOf_known _ fixed _ value hvalue
      simp [KnownCoordinate] at this
  | reveal coordinate hmem =>
      intro index κ leaf heq
      subst heq
      exact hmem
  | succ address _ _ =>
      intro index κ leaf heq
      cases address <;> simp [sampleModel, rowModel, Address.outputCoordinate] at heq

theorem reach_chain (parameterOutput : HashOutput) (highs : CoordinateHighs) (fixed : HiddenGraph.Table)
    (reveals : List Coordinate) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (hactive : PrunedGraph.KeyActive (truncateHash parameterOutput) lay tree leaf) (word : Encoding)
    (hreveals : ∀ (chain : ChainIndex) (position : Digit),
      Coordinate.chain lay tree leaf chain position ∈ reveals → (word chain).val ≤ position.val)
    (coordinate : Coordinate)
    (h : Reach (sampleModel parameterOutput highs) (knownOf (truncateHash parameterOutput) fixed)
      reveals coordinate) :
    ∀ (chain : ChainIndex) (position : Digit),
      coordinate = .chain lay tree leaf chain position → (word chain).val ≤ position.val := by
  induction h with
  | known coordinate value hvalue =>
      intro chain position heq
      subst heq
      rcases knownOf_known _ fixed _ value hvalue with htop | hout
      · have := (word chain).isLt
        simp only [chainLength, winternitzBits] at this htop ⊢
        omega
      · exact (hout hactive).elim
  | reveal coordinate hmem =>
      intro chain position heq
      subst heq
      exact hreveals chain position hmem
  | succ address _ ih =>
      intro chain position heq
      cases address with
      | chain lay' tree' leaf' chainIdx step =>
          simp only [sampleModel, rowModel, Address.outputCoordinate, Coordinate.chain.injEq] at heq
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq
          have hprev := ih chainIdx ⟨step.val, by have := step.isLt; omega⟩ rfl
          simp only at hprev ⊢
          omega
      | fleaf index κ leaf =>
          simp [sampleModel, rowModel, Address.outputCoordinate] at heq

/-! ### Small helpers -/

theorem firstEncoding_congr (f g : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (message : HashInput)
    (h : ∀ counter : Counter, f (Wots.encodingInput parameter lay tree leaf message counter) =
      g (Wots.encodingInput parameter lay tree leaf message counter)) :
    ∀ attempts start, Prefix.firstEncoding f parameter lay tree leaf message attempts start =
      Prefix.firstEncoding g parameter lay tree leaf message attempts start := by
  have hencode : ∀ counter : Counter,
      evalWithAnswerFn f (encode parameter lay tree leaf message counter : OracleComp HashSpec (Option Encoding)) =
        evalWithAnswerFn g (encode parameter lay tree leaf message counter : OracleComp HashSpec (Option Encoding)) := by
    intro counter
    simp only [encode, evalWithAnswerFn_bind, eval_tweakableHash, evalWithAnswerFn_pure]
    rw [show f (tweakableHashInput parameter (.encoding lay tree leaf) (message ++ bytesLE 4 counter)) =
      g (tweakableHashInput parameter (.encoding lay tree leaf) (message ++ bytesLE 4 counter)) from
      h counter]
  intro attempts
  induction attempts with
  | zero => intro start; rfl
  | succ attempts ih =>
      intro start
      simp only [Prefix.firstEncoding, hencode, ih]

theorem digestInputs_mem (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) (call : DigestCall) :
    tweakableHashInput pk.parameter (.message call)
        (messageDigestPayload pk.root message signature.randomness) ∈
      SignatureWitness.trace f pk message signature := by
  unfold SignatureWitness.trace
  rw [Concrete.verify]
  apply queriedInputs_mono_bind_left
  unfold messageDigest
  apply queriedInputs_mono_bind_left
  apply queriedInputs_sequenceFin_component f _ call
  unfold messageDigestCall
  simp only [oracleHash, HasQuery.query]
  rw [← bind_pure (liftM _), queriedInputs_query_bind]
  exact List.mem_cons_self

theorem OnlyC.costGameX (parameter : PublicParameter) (data : GraphView.PublicData) (adversary : Adversary) :
    OnlyC (HiddenBridge.costGameX parameter data (Internalize.internalize adversary)) := by
  unfold HiddenBridge.costGameX HiddenBridge.costRestX
  refine OnlyC.bind (OnlyC.tick _) (fun _ => ?_)
  refine OnlyC.bind ?_ (fun output => ?_)
  · exact OnlyC.costInteraction _ _ _ (Internalize.OnlyAdv.map _ (Internalize.OnlyAdv.internal _ _))
  · exact OnlyC.bind (OnlyC.liftHash (Short.Only.verify _ _ _)) (fun _ => OnlyC.pure' _)

theorem sampleModel_parse (parameterOutput : HashOutput) (highs : CoordinateHighs) :
    (sampleModel parameterOutput highs).parse =
      HiddenGraph.parse (truncateHash parameterOutput) (candidateActive (truncateHash parameterOutput)) := by
  simp only [sampleModel, rowModel]

theorem sampleModel_incoming (parameterOutput : HashOutput) (highs : CoordinateHighs) :
    (sampleModel parameterOutput highs).incoming = Address.inputCoordinate := by
  simp only [sampleModel, rowModel]

theorem sampleModel_outgoing (parameterOutput : HashOutput) (highs : CoordinateHighs) :
    (sampleModel parameterOutput highs).outgoing = Address.outputCoordinate := by
  simp only [sampleModel, rowModel]

section Sample

variable (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
  (remaining : RemainingOutputs) (table : HiddenGraph.Table)
  (htable : tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table)

include htable in
/-- A canonical row input is the prepared graph's canonical input. -/
theorem canonicalRow_input (address : Address) :
    HiddenGraph.input (truncateHash parameterOutput) (address, table address.inputCoordinate) =
      canonicalGraphInput (truncateHash parameterOutput)
        (materialOts (materialT parameterOutput fixed highs remaining table))
        (materialFts (materialT parameterOutput fixed highs remaining table)) address.position
        (labelsOf (materialT parameterOutput fixed highs remaining table)
          (answersT parameterOutput fixed highs remaining table)) := by
  have h := HiddenGraph.coordinates_input (truncateHash parameterOutput)
    (materialOts (materialT parameterOutput fixed highs remaining table))
    (materialFts (materialT parameterOutput fixed highs remaining table))
    (labelsOf (materialT parameterOutput fixed highs remaining table)
      (answersT parameterOutput fixed highs remaining table)) address
  have hcoord := graphCoordinates_T parameterOutput fixed highs remaining table htable
  unfold graphCoordinates at hcoord
  rw [hcoord] at h
  exact h

include htable in
/-- A queried input with a nonempty target set is not a canonical row input. -/
theorem not_canonicalRow_of_target (results : OtsKey → Option (Counter × Encoding)) (input : HashInput)
    (hhit : (targets (truncateHash parameterOutput)
      (compTable parameterOutput fixed highs remaining table results) input).Nonempty) :
    ∀ query, (sampleModel parameterOutput highs).parse input = some query →
      ¬query.2 = table ((sampleModel parameterOutput highs).incoming query.1) := by
  intro query hparse hmatch
  rw [sampleModel_parse] at hparse
  rw [sampleModel_incoming] at hmatch
  obtain ⟨rfl, hactive⟩ := (parse_some_iff _ _ input query).mp hparse
  obtain ⟨address, value⟩ := query
  simp only at hmatch
  subst hmatch
  have hcanonical := canonicalRow_input parameterOutput fixed highs remaining table htable address
  apply Finset.not_nonempty_empty
  convert hhit
  symm
  refine canonical_input_excluded _ _ _ (hashDomainFields address.position.domain)
    ⟨some (canonicalGraphInput (truncateHash parameterOutput)
        (materialOts (materialT parameterOutput fixed highs remaining table))
        (materialFts (materialT parameterOutput fixed highs remaining table)) address.position
        (labelsOf (materialT parameterOutput fixed highs remaining table)
          (answersT parameterOutput fixed highs remaining table))),
      truncateHash (labelsOf (materialT parameterOutput fixed highs remaining table)
        (answersT parameterOutput fixed highs remaining table) address.position)⟩ ⟨_, rfl⟩ ?_ ?_
  · simp only [compTable, (positionAt_some_iff _ address.position).2 rfl]
    exact referenceTable_active _ _ _ _ _ _ address.position hactive
  · exact congrArg some hcanonical.symm

end Sample

/-! ### Unparsed and noncanonical inputs read the final cache -/

theorem parse_tweakable_none (parameter : PublicParameter) (active : Address → Prop) (domain : HashDomain)
    (payload : HashInput) (hdomain : ∀ address : Address, address.position.domain ≠ domain)
    (hrange : domain.InRange) :
    HiddenGraph.parse parameter active (tweakableHashInput parameter domain payload) = none := by
  cases hparse : HiddenGraph.parse parameter active (tweakableHashInput parameter domain payload) with
  | none => rfl
  | some query =>
      obtain ⟨heq, -⟩ := (parse_some_iff parameter active _ query).mp hparse
      have h := tweakableInput_injective heq
      exact (hdomain query.1 (hashFields_injective hrange (Position.domain_inRange _) h.1).symm).elim

theorem finalFn_unparsed (parameterOutput : HashOutput) (highs : CoordinateHighs) (table : HiddenGraph.Table)
    (cacheF : QueryCache HashSpec) (input : HashInput)
    (hnot : ∀ query, (sampleModel parameterOutput highs).parse input = some query →
      ¬query.2 = table ((sampleModel parameterOutput highs).incoming query.1)) :
    finalFn (sampleModel parameterOutput highs) table cacheF input = (cacheF input).getD 0 := by
  unfold finalFn HiddenRows.answer
  cases hparse : (sampleModel parameterOutput highs).parse input with
  | none => rfl
  | some query =>
      simp only [Option.elim_some]
      rw [if_neg (hnot query hparse)]

theorem encoding_not_row (parameterOutput : HashOutput) (highs : CoordinateHighs) (table : HiddenGraph.Table)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : HashInput) (counter : Counter) :
    ∀ query, (sampleModel parameterOutput highs).parse
      (Wots.encodingInput (truncateHash parameterOutput) lay tree leaf message counter) = some query →
      ¬query.2 = table ((sampleModel parameterOutput highs).incoming query.1) := by
  intro query hparse
  rw [sampleModel_parse, Wots.encodingInput, parse_tweakable_none _ _ _ _
    (fun address => by cases address <;> simp [Address.position, Position.domain]) (by trivial)] at hparse
  cases hparse

theorem message_not_row (parameterOutput : HashOutput) (highs : CoordinateHighs) (table : HiddenGraph.Table)
    (payload : HashInput) (call : DigestCall) :
    ∀ query, (sampleModel parameterOutput highs).parse
      (tweakableHashInput (truncateHash parameterOutput) (.message call) payload) = some query →
      ¬query.2 = table ((sampleModel parameterOutput highs).incoming query.1) := by
  intro query hparse
  rw [sampleModel_parse, parse_tweakable_none _ _ _ _
    (fun address => by cases address <;> simp [Address.position, Position.domain]) (by trivial)] at hparse
  cases hparse

theorem tweakable_not_seedHit (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput)
    (seed : MasterSeed) : ¬SeedGuess.SeedHit (tweakableHashInput parameter domain payload) seed := by
  rintro ⟨parameter', derive, heq⟩
  exact keygenInput_ne_hashInput parameter' parameter derive domain seed payload heq

/-- The consistent preparation's targets are the sample's fixed targets. -/
theorem fullTable_eq (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (table : HiddenGraph.Table)
    (results : OtsKey → Option (Counter × Encoding)) (f : QueryImpl HashSpec Id) (seed : MasterSeed)
    (hagreement : SeedModel.PreparedAgreement f seed (materialT parameterOutput fixed highs remaining table))
    (hselection : ∀ key : OtsKey, ReferenceChoice.selection f (truncateHash parameterOutput) key.1 key.2.1
      key.2.2 (keyMessages (sampleData parameterOutput fixed highs remaining) key) = results key) :
    fullTable f (truncateHash parameterOutput) seed
        (labelsOf (materialT parameterOutput fixed highs remaining table)
          (answersT parameterOutput fixed highs remaining table)) =
      compTable parameterOutput fixed highs remaining table results := by
  funext fields
  unfold fullTable compTable
  cases positionAt fields with
  | some position =>
      dsimp only
      unfold graphTable
      have h1 : materialOts (materialT parameterOutput fixed highs remaining table) =
          otsSecrets f (truncateHash parameterOutput) seed :=
        GraphCorrectness.materialOts_eq f seed _ hagreement
      have h2 : materialFts (materialT parameterOutput fixed highs remaining table) =
          ftsSecrets f (truncateHash parameterOutput) seed :=
        GraphCorrectness.materialFts_eq f seed _ hagreement
      have h3 : materialSurrogates (materialT parameterOutput fixed highs remaining table) =
          surrogates f (truncateHash parameterOutput) seed :=
        GraphCorrectness.materialSurrogates_eq f seed _ hagreement
      rw [← h1, ← h2, ← h3]
  | none =>
      dsimp only
      unfold encodingEntry encTable
      refine congrArg (fun g => Option.map g (encodingAt fields)) (funext fun key => ?_)
      have hmsg : labelMessage (labelsOf (materialT parameterOutput fixed highs remaining table)
          (answersT parameterOutput fixed highs remaining table)) key =
          keyMessages (sampleData parameterOutput fixed highs remaining) key := by
        unfold labelMessage keyMessages
        rw [publicData_T]
      rw [hmsg]
      unfold ReferenceChoice.exemptInput ReferenceChoice.target ReferenceChoice.word
      rw [hselection key]

theorem selection_of_agree (parameter : PublicParameter) (message : OtsKey → HashInput)
    (results : OtsKey → Option (Counter × Encoding)) (f g : QueryImpl HashSpec Id)
    (hsearch : ∀ key : OtsKey, Prefix.firstEncoding g parameter key.1 key.2.1 key.2.2 (message key)
      encodingAttemptLimit 0 = results key)
    (hagree : ∀ (key : OtsKey) (counter : Counter),
      f (Wots.encodingInput parameter key.1 key.2.1 key.2.2 (message key) counter) =
        g (Wots.encodingInput parameter key.1 key.2.1 key.2.2 (message key) counter))
    (key : OtsKey) :
    ReferenceChoice.selection f parameter key.1 key.2.1 key.2.2 (message key) = results key := by
  unfold ReferenceChoice.selection
  rw [firstEncoding_congr f g _ _ _ _ _ (hagree key), hsearch key]

/-- A target hit at a recorded, non-canonical query is a cached hit of a fixed target. -/
theorem cached_hit (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (table : HiddenGraph.Table)
    (htable : tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table)
    (results : OtsKey → Option (Counter × Encoding)) (cacheF : QueryCache HashSpec)
    (f : QueryImpl HashSpec Id) (entries : List (HiddenCost.Entry HashInput))
    (hagree : ∀ input, Sum.inl input ∈ entries →
      f input = finalFn (sampleModel parameterOutput highs) table cacheF input)
    (hcached : CachedQueries (sampleModel parameterOutput highs) table cacheF entries)
    (input : HashInput) (hentry : Sum.inl input ∈ entries)
    (hmem : truncateHash (f input) ∈ targets (truncateHash parameterOutput)
      (compTable parameterOutput fixed highs remaining table results) input) :
    CacheMatch.Bad (targets (truncateHash parameterOutput)
      (compTable parameterOutput fixed highs remaining table results)) cacheF := by
  have hnot := not_canonicalRow_of_target parameterOutput fixed highs remaining table htable
    results input ⟨_, hmem⟩
  obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp (hcached input hentry hnot)
  have hfin := finalFn_unparsed parameterOutput highs table cacheF input hnot
  rw [hanswer] at hfin
  refine ⟨input, answer, hanswer, ?_⟩
  have hvalue : f input = answer := (hagree input hentry).trans hfin
  rw [← hvalue]
  exact hmem

/-- A queried honest FORS secret was revealed. -/
theorem queried_fleaf_revealed (parameterOutput : HashOutput) (highs : CoordinateHighs)
    (fixed table : HiddenGraph.Table) (reveals : List Coordinate) (entries : List (HiddenCost.Entry HashInput))
    (hguess : NoHiddenGuess (sampleModel parameterOutput highs) table
      (knownOf (truncateHash parameterOutput) fixed) reveals entries)
    (index : Index) (κ : FTree) (leaf : FLeaf)
    (hmem : Sum.inl (tweakableHashInput (truncateHash parameterOutput) (.forsLeaf index κ leaf)
      (bytesLE 16 (table (.fors index κ leaf 0)))) ∈ entries) :
    Coordinate.fors index κ leaf 0 ∈ reveals := by
  have hparse : (sampleModel parameterOutput highs).parse
      (tweakableHashInput (truncateHash parameterOutput) (.forsLeaf index κ leaf)
        (bytesLE 16 (table (.fors index κ leaf 0)))) =
      some (.fleaf index κ leaf, table (.fors index κ leaf 0)) := by
    rw [sampleModel_parse]
    exact parse_input _ _ (.fleaf index κ leaf, _) trivial
  have hreach := hguess _ hmem _ hparse (by rw [sampleModel_incoming]; rfl)
  rw [sampleModel_incoming] at hreach
  exact reach_fors parameterOutput highs fixed reveals _ hreach index κ leaf rfl

theorem queried_chain_reach (parameterOutput : HashOutput) (highs : CoordinateHighs)
    (fixed table : HiddenGraph.Table) (reveals : List Coordinate) (entries : List (HiddenCost.Entry HashInput))
    (hguess : NoHiddenGuess (sampleModel parameterOutput highs) table
      (knownOf (truncateHash parameterOutput) fixed) reveals entries)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (hactive : PrunedGraph.KeyActive (truncateHash parameterOutput) lay tree leaf) (word : Encoding)
    (hreveals : ∀ (chain : ChainIndex) (position : Digit),
      Coordinate.chain lay tree leaf chain position ∈ reveals → (word chain).val ≤ position.val)
    (chain : ChainIndex) (step : ChainStep)
    (hmem : Sum.inl (tweakableHashInput (truncateHash parameterOutput) (.chain lay tree leaf chain step)
      (bytesLE 16 (table (.chain lay tree leaf chain ⟨step.val, by have := step.isLt; omega⟩)))) ∈
        entries) :
    (word chain).val ≤ step.val := by
  have hparse : (sampleModel parameterOutput highs).parse
      (tweakableHashInput (truncateHash parameterOutput) (.chain lay tree leaf chain step)
        (bytesLE 16 (table (.chain lay tree leaf chain ⟨step.val, by have := step.isLt; omega⟩)))) =
      some (.chain lay tree leaf chain step,
        table (.chain lay tree leaf chain ⟨step.val, by have := step.isLt; omega⟩)) := by
    rw [sampleModel_parse]
    exact parse_input _ _ (.chain lay tree leaf chain step, _) hactive
  have hreach := hguess _ hmem _ hparse (by rw [sampleModel_incoming]; rfl)
  rw [sampleModel_incoming] at hreach
  exact reach_chain parameterOutput highs fixed reveals lay tree leaf hactive word hreveals _ hreach chain _ rfl

theorem allSome_some {n : Nat} {α : Fin n → Type} {values : (i : Fin n) → Option (α i)}
    {found : (i : Fin n) → α i} (h : allSome values = some found) (i : Fin n) :
    values i = some (found i) := by
  unfold allSome at h
  split at h
  · rename_i hall
    cases h
    exact (Option.some_get (hall i)).symm
  · cases h

/-- Every revealed chain value of a retained key is at that key's canonical word. -/
theorem revealed_chain_word (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (seed : MasterSeed)
    (data : GraphView.PublicData) (log : QueryLog SigningSpec) (reveals : List Coordinate)
    (hgood : LogGood f parameter seed data log reveals)
    (hdata : GraphView.DataCorrect f parameter seed data)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (hactive : PrunedGraph.KeyActive parameter lay tree leaf) (chain : ChainIndex) (position : Digit)
    (hmem : Coordinate.chain lay tree leaf chain position ∈ reveals) :
    (ReferenceChoice.word f parameter lay tree leaf
      (SignatureWitness.keyMessageValue f parameter seed (lay, tree, leaf)) chain).val ≤ position.val := by
  obtain ⟨entry, -, signature, -, hcoordinate⟩ := hgood.2 _ hmem
  unfold revealsOf at hcoordinate
  dsimp only at hcoordinate
  generalize digestIndex (evalWithAnswerFn f (messageDigest parameter data.root entry.1
    signature.randomness : OracleComp HashSpec MessageDigest)) = index at hcoordinate
  cases hfound : GraphView.assembledEncodings f parameter data index with
  | none => rw [hfound] at hcoordinate; cases hcoordinate
  | some found =>
      rw [hfound] at hcoordinate
      rcases List.mem_append.mp hcoordinate with hchain | hfts
      · unfold wotsReveals at hchain
        obtain ⟨l, hl, hchain⟩ := List.mem_flatten.mp hchain
        obtain ⟨lay', rfl⟩ := List.mem_ofFn.mp hl
        obtain ⟨chain', hchain'⟩ := List.mem_ofFn.mp hchain
        simp only [Coordinate.chain.injEq] at hchain'
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hchain'
        have hlay := allSome_some hfound lay'
        have hmsg := hdata.keyMessage lay' _ _ hactive
        rw [hmsg] at hlay
        have hword : ReferenceChoice.word f parameter lay' (treeIndexAt index lay') (leafIndexAt index lay')
            (SignatureWitness.keyMessageValue f parameter seed
              (lay', treeIndexAt index lay', leafIndexAt index lay')) = (found lay').2 := by
          unfold ReferenceChoice.word ReferenceChoice.selection SignatureWitness.keyMessageValue
          rw [hlay]
          rfl
        rw [hword]
      · obtain ⟨l, hl, hfts'⟩ := List.mem_flatten.mp hfts
        obtain ⟨κ, rfl⟩ := List.mem_ofFn.mp hl
        obtain ⟨k, ⟨⟩⟩ := mem_treeReveals hfts'

/-- A canonical opening sharing an honest signature's message and randomizer is that signature. -/
theorem canonical_signed_eq (f : QueryImpl HashSpec Id) (sk : Seeded.SecretKey) (message : Message)
    (randomness : Randomness) (signature honest : Signature)
    (hland : Landed sk.parameter (digestIndex (Completeness.digestValue f sk message randomness)))
    (hfinish : evalWithAnswerFn f (Seeded.finishSign sk message randomness) = some honest)
    (hrandomness : honest.randomness = signature.randomness) (counter : Layer → Counter)
    (hchosen : ∀ lay, SignatureWitness.chosenCounter f sk.parameter sk.seed
      (SignatureWitness.index f ⟨sk.root, sk.parameter⟩ message signature) lay = some (counter lay))
    (hcanonical : SignatureWitness.CanonicalOpening f ⟨sk.root, sk.parameter⟩ sk.seed message signature counter
      (SignatureWitness.chosenWord f sk.parameter sk.seed
        (SignatureWitness.index f ⟨sk.root, sk.parameter⟩ message signature))) :
    signature = honest := by
  have hindex : SignatureWitness.index f ⟨sk.root, sk.parameter⟩ message honest =
      SignatureWitness.index f ⟨sk.root, sk.parameter⟩ message signature := by
    simp only [SignatureWitness.index, verificationDigest, hrandomness]
  have hcounter : ∀ lay, (honest.layers lay).counter = counter lay := by
    intro lay
    have h := honest_counter f sk message randomness honest hland hfinish lay
    rw [hindex, hchosen lay, Option.some.injEq] at h
    exact h.symm
  obtain ⟨word, href, hhonest⟩ := SignatureWitness.canonical_of_finishSign f sk message randomness honest
    hland hfinish
  rw [hindex] at href
  have hcounterFn : (fun lay => (honest.layers lay).counter) = counter := funext hcounter
  rw [hcounterFn] at hhonest
  -- the honest word is the chosen word
  have hword : word = SignatureWitness.chosenWord f sk.parameter sk.seed
      (SignatureWitness.index f ⟨sk.root, sk.parameter⟩ message signature) := by
    funext lay
    have hchosenLay := hchosen lay
    obtain ⟨pair, hpair⟩ : ∃ pair, ReferenceChoice.selection f sk.parameter lay
        (SignatureWitness.keyTree (SignatureWitness.index f ⟨sk.root, sk.parameter⟩ message signature) lay)
        (SignatureWitness.keyLeaf (SignatureWitness.index f ⟨sk.root, sk.parameter⟩ message signature) lay)
        (SignatureWitness.canonicalMessage f sk.parameter sk.seed
          (SignatureWitness.index f ⟨sk.root, sk.parameter⟩ message signature) lay) = some pair := by
      cases h : ReferenceChoice.selection f sk.parameter lay
          (SignatureWitness.keyTree (SignatureWitness.index f ⟨sk.root, sk.parameter⟩ message signature) lay)
          (SignatureWitness.keyLeaf (SignatureWitness.index f ⟨sk.root, sk.parameter⟩ message signature) lay)
          (SignatureWitness.canonicalMessage f sk.parameter sk.seed
            (SignatureWitness.index f ⟨sk.root, sk.parameter⟩ message signature) lay) with
      | none => simp [SignatureWitness.chosenCounter, h] at hchosenLay
      | some pair => exact ⟨pair, rfl⟩
    have hpairCounter : pair.1 = counter lay := by
      simpa [SignatureWitness.chosenCounter, hpair] using hchosenLay
    have hencode := ReferenceChoice.firstEncoding_sound f sk.parameter lay _ _ _
      encodingAttemptLimit 0 pair.1 pair.2 hpair
    have href' := href lay
    unfold SignatureWitness.ReferenceCertificate at href'
    rw [hcounter lay, ← hpairCounter] at href'
    have h := href'.symm.trans hencode
    rw [Option.some.injEq] at h
    rw [h]
    unfold SignatureWitness.chosenWord
    rw [ReferenceChoice.word_of_some _ _ _ _ _ _ pair.1 pair.2 hpair]
  rw [hword] at hhonest
  exact SignatureWitness.canonicalOpening_unique f _ sk.seed message signature honest counter _
    hcanonical hhonest hrandomness.symm

/-- The verifier's digest is read off the final cache. -/
theorem cachedDigest_eq (parameterOutput : HashOutput) (highs : CoordinateHighs) (table : HiddenGraph.Table)
    (cacheF : QueryCache HashSpec) (f : QueryImpl HashSpec Id) (entries : List (HiddenCost.Entry HashInput))
    (hagree : ∀ input, Sum.inl input ∈ entries →
      f input = finalFn (sampleModel parameterOutput highs) table cacheF input)
    (hcached : CachedQueries (sampleModel parameterOutput highs) table cacheF entries)
    (root : Digest) (message : Message) (signature : Signature)
    (htrace : ∀ input ∈ SignatureWitness.trace f ⟨root, truncateHash parameterOutput⟩ message signature,
      Sum.inl input ∈ entries) :
    cachedDigest cacheF (truncateHash parameterOutput) root message signature.randomness =
      some (verificationDigest f ⟨root, truncateHash parameterOutput⟩ message signature) := by
  have hread : ∀ call : DigestCall, cacheF (tweakableHashInput (truncateHash parameterOutput) (.message call)
      (messageDigestPayload root message signature.randomness)) =
      some (f (tweakableHashInput (truncateHash parameterOutput) (.message call)
        (messageDigestPayload root message signature.randomness))) := by
    intro call
    have hentry := htrace _ (digestInputs_mem f ⟨root, truncateHash parameterOutput⟩ message signature call)
    have hnot := message_not_row parameterOutput highs table
      (messageDigestPayload root message signature.randomness) call
    obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp (hcached _ hentry hnot)
    have hfin := finalFn_unparsed parameterOutput highs table cacheF _ hnot
    rw [hanswer] at hfin
    rw [hanswer, (hagree _ hentry).trans hfin]
    rfl
  unfold cachedDigest verificationDigest
  simp only [hread]
  unfold Completeness.allSome
  simp only [Option.isSome_some, implies_true, ↓reduceDIte, Option.map_some, Option.get_some, messageDigest, messageDigestCall, oracleHash,
    HasQuery.query, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Completeness.eval_sequenceFin]
  rfl

/-! ### The win implication -/

attribute [local irreducible] ReferenceChoice.selection encodingAttemptLimit

/-- The label message of a retained key is its canonical message. -/
theorem labelMessage_eq (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (steps : Message → Randomness) (table : HiddenGraph.Table)
    (f : QueryImpl HashSpec Id) (seed : MasterSeed)
    (hdata : GraphView.DataCorrect f (truncateHash parameterOutput) seed
      (sampleData parameterOutput fixed highs remaining steps))
    (key : OtsKey) (hactive : PrunedGraph.KeyActive (truncateHash parameterOutput) key.1 key.2.1 key.2.2) :
    labelMessage (labelsOf (materialT parameterOutput fixed highs remaining table)
        (answersT parameterOutput fixed highs remaining table)) key =
      SignatureWitness.keyMessageValue f (truncateHash parameterOutput) seed key := by
  have h := hdata.keyMessage key.1 key.2.1 key.2.2 hactive
  unfold labelMessage
  rw [publicData_T]
  exact h

/-- **Case analysis.** For any answer function consistent with the sample and agreeing with the
final cache on the run's queries, an accepted fresh forgery yields a cached target hit or FORS
coverage. -/
theorem bad_of_accepted (hb : 0 < keptHeight topLayer) (parameterOutput : HashOutput) (fixed : HiddenGraph.Table)
    (highs : CoordinateHighs) (remaining : RemainingOutputs) (steps : Message → Randomness) (table : HiddenGraph.Table)
    (htable : tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table)
    (results : OtsKey → Option (Counter × Encoding)) (cacheF : QueryCache HashSpec)
    (reveals : List Coordinate) (entries : List (HiddenCost.Entry HashInput))
    (f : QueryImpl HashSpec Id) (seed : MasterSeed)
    (hcons : GraphCorrectness.Consistent f (truncateHash parameterOutput) seed
      (labelsOf (materialT parameterOutput fixed highs remaining table)
        (answersT parameterOutput fixed highs remaining table)))
    (hbound : GraphCorrectness.BoundaryCorrect f (truncateHash parameterOutput) seed
      (labelsOf (materialT parameterOutput fixed highs remaining table)
        (answersT parameterOutput fixed highs remaining table)))
    (hdata : GraphView.DataCorrect f (truncateHash parameterOutput) seed
      (sampleData parameterOutput fixed highs remaining steps))
    (hcoord : GraphView.CoordinatesCorrect f (truncateHash parameterOutput) seed table)
    (hfull : fullTable f (truncateHash parameterOutput) seed
        (labelsOf (materialT parameterOutput fixed highs remaining table)
          (answersT parameterOutput fixed highs remaining table)) =
      compTable parameterOutput fixed highs remaining table results)
    (hagree : ∀ input, Sum.inl input ∈ entries →
      f input = finalFn (sampleModel parameterOutput highs) table cacheF input)
    (hcached : CachedQueries (sampleModel parameterOutput highs) table cacheF entries)
    (hguess : NoHiddenGuess (sampleModel parameterOutput highs) table
      (knownOf (truncateHash parameterOutput) fixed) reveals entries)
    (forgery : Forgery) (log : QueryLog SigningSpec)
    (htrace : ∀ input ∈ SignatureWitness.trace f ⟨(sampleData parameterOutput fixed highs remaining).root,
      truncateHash parameterOutput⟩ forgery.message forgery.signature, Sum.inl input ∈ entries)
    (hgood : LogGood f (truncateHash parameterOutput) seed (sampleData parameterOutput fixed highs remaining steps)
      log reveals)
    (hverify : evalWithAnswerFn f (Concrete.verify ⟨(sampleData parameterOutput fixed highs remaining).root,
      truncateHash parameterOutput⟩ forgery.message forgery.signature : OracleComp HashSpec Bool) = true)
    (hvalid : SigningTranscript.Valid log) (hnotContains : ¬SigningTranscript.Contains log forgery) :
    CacheMatch.Bad (targets (truncateHash parameterOutput)
        (compTable parameterOutput fixed highs remaining table results)) cacheF ∨
      ForsCover (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining).root
        (forgery, log, true) reveals cacheF := by
  have hhit : ∀ input ∈ SignatureWitness.trace f ⟨(sampleData parameterOutput fixed highs remaining).root,
      truncateHash parameterOutput⟩ forgery.message forgery.signature,
      truncateHash (f input) ∈ targets (truncateHash parameterOutput)
        (fullTable f (truncateHash parameterOutput) seed
          (labelsOf (materialT parameterOutput fixed highs remaining table)
            (answersT parameterOutput fixed highs remaining table))) input →
      CacheMatch.Bad (targets (truncateHash parameterOutput)
        (compTable parameterOutput fixed highs remaining table results)) cacheF := by
    intro input hinput hmem
    rw [hfull] at hmem
    exact cached_hit parameterOutput fixed highs remaining table htable results cacheF f entries hagree
      hcached input (htrace input hinput) hmem
  rcases SignatureWitness.accepted_full_classification f ⟨(sampleData parameterOutput fixed highs remaining).root,
      truncateHash parameterOutput⟩ seed forgery.message forgery.signature hb hdata.root hverify with
    ⟨counter, hchosen, hcanon⟩ | ⟨j, -, htree⟩ | ⟨hland, hexc⟩
  · by_cases hsigned : ∃ entry ∈ log, ∃ honest, entry.2 = some honest ∧ entry.1 = forgery.message ∧
        honest.randomness = forgery.signature.randomness
    · exfalso
      obtain ⟨entry, hentry, honest, hhonest, hmessage, hrandomness⟩ := hsigned
      obtain ⟨randomness, hlandR, hfinish⟩ := hgood.1 entry hentry honest hhonest
      rw [hmessage] at hlandR hfinish
      have heq := canonical_signed_eq f ⟨seed, truncateHash parameterOutput,
        (sampleData parameterOutput fixed highs remaining).root⟩ forgery.message randomness
        forgery.signature honest hlandR hfinish hrandomness counter hchosen hcanon
      apply hnotContains
      exact ⟨entry, hentry, hmessage, by rw [hhonest, heq]⟩
    · right
      have hopen := hcanon.2.2
      have hrun := SignatureWitness.verification_fors_run f ⟨(sampleData parameterOutput fixed highs
        remaining).root, truncateHash parameterOutput⟩ forgery.message forgery.signature
      rcases Fors.Opening.covered_or_hidden f (truncateHash parameterOutput) _ seed _
          forgery.signature.fors (revealedSet reveals) _ hopen hrun with
        hcovered | ⟨index, κ, leaf, hnot, hmem⟩
      · refine ⟨hvalid, _, cachedDigest_eq parameterOutput highs table cacheF f entries hagree hcached _
          forgery.message forgery.signature htrace, hcanon.1, ?_, hcovered⟩
        intro entry hentry honest hhonest hpair
        exact hsigned ⟨entry, hentry, honest, hhonest, hpair.1, hpair.2⟩
      · exfalso
        rw [← (hcoord.2 index κ leaf).1] at hmem
        exact hnot (by
          simpa only [revealedSet, Finset.mem_filter, Finset.mem_univ, true_and] using
            queried_fleaf_revealed parameterOutput highs fixed table reveals entries hguess
              index κ leaf (htrace _ hmem))
  · left
    obtain ⟨input, hinput, hmem⟩ := treeHit_hit f (truncateHash parameterOutput) seed _ hcons hbound _ rfl
      forgery.message forgery.signature j htree
    exact hhit input hinput (graph_targets_subset _ _ _ _ _ hmem)
  · have hactive : ∀ lay : Layer, PrunedGraph.KeyActive (truncateHash parameterOutput) lay
        (treeIndexAt (SignatureWitness.index f _ forgery.message forgery.signature) lay)
        (leafIndexAt (SignatureWitness.index f _ forgery.message forgery.signature) lay) :=
      fun lay => ⟨_, hland, rfl, rfl⟩
    rcases hexc with ⟨lay, henc | hleafMatch | hchain⟩ | ⟨hforsExc, -⟩
    · left
      have hmsg := labelMessage_eq parameterOutput fixed highs remaining steps table f seed hdata
        (keyAt (SignatureWitness.index f ⟨(sampleData parameterOutput fixed highs remaining).root,
          truncateHash parameterOutput⟩ forgery.message forgery.signature) lay) (hactive lay)
      obtain ⟨input, hinput, hmem⟩ := encodingMatch_hit f (truncateHash parameterOutput) seed
        (labelsOf (materialT parameterOutput fixed highs remaining table)
          (answersT parameterOutput fixed highs remaining table))
        (keyAt (SignatureWitness.index f ⟨(sampleData parameterOutput fixed highs remaining).root,
          truncateHash parameterOutput⟩ forgery.message forgery.signature) lay) _ (by rw [hmsg]; exact henc)
      exact hhit input hinput hmem
    · left
      obtain ⟨input, hinput, hmem⟩ := leafOutput_hit f (truncateHash parameterOutput) seed _ hcons _ _ _
        (hactive lay) _ hleafMatch
      exact hhit input hinput (graph_targets_subset _ _ _ _ _ hmem)
    · rcases Wots.ChainException.hidden_or_output f _ _ _ _ _ _ hchain with
        ⟨chain, step, hlt, hmem⟩ | houtput
      · exfalso
        have hvalue := hcoord.1 _ _ _ (hactive lay) chain ⟨step.val, by have := step.isLt; omega⟩
        rw [← hvalue] at hmem
        have hle := queried_chain_reach parameterOutput highs fixed table reveals entries hguess _ _ _
          (hactive lay)
          (SignatureWitness.chosenWord f (truncateHash parameterOutput) seed
            (SignatureWitness.index f _ forgery.message forgery.signature) lay)
          (fun chain position h => revealed_chain_word f _ seed _ log reveals hgood hdata _ _ _ (hactive lay)
            chain position h)
          chain step (htrace _ hmem)
        dsimp only at hlt hle
        omega
      · left
        obtain ⟨input, hinput, hmem⟩ := chainOutput_hit f (truncateHash parameterOutput) seed _ hcons _ _ _
          (hactive lay) _ houtput
        exact hhit input hinput (graph_targets_subset _ _ _ _ _ hmem)
    · left
      obtain ⟨input, hinput, hmem⟩ := forsException_hit f (truncateHash parameterOutput) seed _ hcons _ _ _
        hforsExc
      exact hhit input (SignatureWitness.verification_fors_run f _ forgery.message forgery.signature input hinput)
        (graph_targets_subset _ _ _ _ _ hmem)

/-- Prepared answers take priority over a sample function. -/
def preferCache (cache : QueryCache HashSpec) (f : QueryImpl HashSpec Id) : QueryImpl HashSpec Id :=
  fun input => (cache input).getD (f input)

theorem preferCache_agrees (cache : QueryCache HashSpec) (f : QueryImpl HashSpec Id) :
    cache.AgreesWithFn (preferCache cache f) := fun input answer h => by
  simp [preferCache, h]

/-- The outside table read off a final lazy cache. -/
noncomputable def finalTable (parameterOutput : HashOutput) (highs : CoordinateHighs)
    (table : HiddenGraph.Table) (cacheF : QueryCache HashSpec) : Eager.Table :=
  fun short => finalFn (sampleModel parameterOutput highs) table cacheF short.val

theorem encodingInput_short (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : HashInput) (hmessage : Short.ShortMessage message) (counter : Counter) :
    Short.IsShort (Wots.encodingInput parameter lay tree leaf message counter) := by
  unfold Short.ShortMessage at hmessage
  simp only [Wots.encodingInput, Short.IsShort, Short.bound, Short.tweakableHashInput_length,
    List.length_append, bytesLE_length]
  omega

/-- Encoding inputs read the same value through the prepared cache. -/
theorem encoding_preferCache (parameterOutput : HashOutput) (highs : CoordinateHighs)
    (table : HiddenGraph.Table) (cacheF prepCache : QueryCache HashSpec) (f : QueryImpl HashSpec Id)
    (seed : MasterSeed)
    (hagreeAll : ∀ input, Short.IsShort input → ¬SeedGuess.SeedHit input seed →
      f input = finalFn (sampleModel parameterOutput highs) table cacheF input)
    (hgrow : ∀ input answer, prepCache input = some answer → cacheF input = some answer)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : HashInput)
    (hmessage : Short.ShortMessage message) (counter : Counter) :
    f (Wots.encodingInput (truncateHash parameterOutput) lay tree leaf message counter) =
      preferCache prepCache f (Wots.encodingInput (truncateHash parameterOutput) lay tree leaf message counter) := by
  unfold preferCache
  cases hp : prepCache (Wots.encodingInput (truncateHash parameterOutput) lay tree leaf message counter) with
  | none => exact (Option.getD_none).symm
  | some answer =>
      rw [Option.getD_some, hagreeAll _ (encodingInput_short _ _ _ _ _ hmessage _)
          (tweakable_not_seedHit _ _ _ seed),
        finalFn_unparsed parameterOutput highs table cacheF _
          (encoding_not_row parameterOutput highs table lay tree leaf _ counter),
        hgrow _ _ hp]
      exact Option.getD_some

/-- The sample function agrees with the final lazy cache on short, non-seed inputs. -/
theorem sampleFn_final (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (table : HiddenGraph.Table)
    (htable : tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table)
    (cacheF : QueryCache HashSpec) (seed : MasterSeed)
    (hstruct : ∀ input answer, structCache (splitMaterial parameterOutput highs remaining fixed)
      (splitAnswers highs remaining fixed) input = some answer → cacheF input = some answer)
    (input : HashInput) (hshort : Short.IsShort input) (hnot : ¬SeedGuess.SeedHit input seed) :
    sampleFn (materialT parameterOutput fixed highs remaining table) seed
        (answersT parameterOutput fixed highs remaining table) (finalTable parameterOutput highs table cacheF) input =
      finalFn (sampleModel parameterOutput highs) table cacheF input := by
  rw [sampleFn_answer parameterOutput fixed highs remaining table htable seed _ input hnot]
  unfold outsideFn
  exact answer_extend_final _ table _ cacheF hstruct input hshort

/-- **Win implication.** In every non-stopped lazy run of the rich program whose outcome wins
the original game, either a cached answer hits one of the sample's fixed targets, or the run's
reveals cover the FORS openings of a cached, landed, unsigned forgery digest. -/
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
        (HiddenCost.erase (HiddenCost.trace (richProgram (Internalize.internalize adversary) q
          (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps))))
        (knownOf (truncateHash parameterOutput) fixed) prepared.2))
    (hwin : outcomeWins outcome = true) :
    CacheMatch.Bad (targets (truncateHash parameterOutput)
        (compTable parameterOutput fixed highs remaining table prepared.1)) cacheF ∨
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
  have hcost := costRun_withReveals_cap_cost _ table _ q _ hrun
  obtain ⟨seed, hseed⟩ := exists_seed_avoiding
    (entries.filterMap fun entry => match entry with | .inl input => some input | .inr _ => none)
    (lt_of_le_of_lt ((ordinary_length_le_cost entries).trans hcost) hq)
  have hseed' : ∀ input, Sum.inl input ∈ entries → ¬SeedGuess.SeedHit input seed :=
    fun input hinput => hseed input (List.mem_filterMap.mpr ⟨_, hinput, rfl⟩)
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

end FORS.Security.HiddenBridge
