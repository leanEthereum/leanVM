import Sphincs.BridgeClassify
import Sphincs.BridgeSupport

/-! Deterministic core: a winning non-stopped run of the rich program yields a cached hit of
a fixed target or a covered FORS digest. -/

open OracleComp OracleSpec

namespace Sphincs.Security.HiddenBridge

open Concrete Completeness Graph GraphCorrectness TargetAssignment HiddenGraph Assembly SeedModel Reduce Eager

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

/-! ### The honest counter is the canonical one -/

omit [Params] in
theorem otsSignFrom_firstEncoding (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (seed : MasterSeed) (message : Digest) :
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
    (hsign : evalWithAnswerFn f (Randomized.finishSign sk message randomness) = some signature) :
    SignatureWitness.chosenCounter f sk.parameter sk.seed
      (SignatureWitness.index f ⟨sk.root, sk.parameter⟩ message signature) =
        some (signature.layers topLayer).counter := by
  obtain ⟨-, -, hlayers⟩ := Completeness.finishSign_spec f sk message randomness hland hsign
  obtain ⟨hots, -⟩ := Completeness.signLayer_spec f sk _ topLayer (hlayers topLayer)
  simp only [Completeness.treeIndexAt_eq, Completeness.leafIndexAt_eq] at hots
  obtain ⟨word, hword⟩ := otsSignFrom_firstEncoding f sk.parameter topLayer rootTree _ sk.seed _
    encodingAttemptLimit 0 hots
  have hindex : SignatureWitness.index f ⟨sk.root, sk.parameter⟩ message signature =
      digestIndex (Completeness.digestValue f sk message signature.randomness) := rfl
  rw [hindex]
  simp only [SignatureWitness.chosenCounter, ReferenceChoice.selection]
  rw [show SignatureWitness.canonicalForest f sk.parameter sk.seed
      (digestIndex (Completeness.digestValue f sk message signature.randomness)) =
    Completeness.layerMessageValue f sk
      (digestIndex (Completeness.digestValue f sk message signature.randomness)) topLayer from rfl, hword]
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
noncomputable def encTable (parameter : PublicParameter) (forsKey : Index → Digest)
    (results : Index → Option (Counter × Encoding)) : TargetAssignment.Table := fun fields =>
  (encodingAt fields).map fun leaf =>
    ⟨(results leaf).map (fun pair => Wots.encodingInput parameter topLayer rootTree leaf (forsKey leaf) pair.1),
      Completeness.pack (((results leaf).map Prod.snd).getD ReferenceChoice.dummyWord)⟩

/-- All fixed targets of one sample, hidden table and preparation. -/
noncomputable def compTable (table : HiddenGraph.Table) (results : Index → Option (Counter × Encoding)) :
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
      (sampleData parameterOutput fixed highs remaining).forestKey results fields

end Events

/-- The verifier's message digest of a forgery, read from a cache. -/
def cachedDigest (cache : QueryCache HashSpec) (parameter : PublicParameter) (root : Digest)
    (message : Message) (randomness : Randomness) : Option MessageDigest := do
  let first ← cache (tweakableHashInput parameter .message (messageDigestPayload root message randomness))
  return truncateMessageDigest first

/-- Forest chain positions revealed by the run. -/
noncomputable def revealedSet (reveals : List HiddenGraph.Coordinate) : Disclosures := fun index c s j a i =>
  Finset.univ.filter fun p => HiddenGraph.Coordinate.fchain index c s j a i p ∈ reveals

/-- A cached, landed digest of an unsigned message-randomizer pair whose forest openings were all
revealed by the run (at or below the positions it needs). -/
def ForestCover (parameter : PublicParameter) (root : Digest) (outcome : Outcome)
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

theorem publicData_T (table : HiddenGraph.Table) :
    GraphView.publicData (labelsOf (materialT parameterOutput fixed highs remaining table)
      (answersT parameterOutput fixed highs remaining table)) =
      sampleData parameterOutput fixed highs remaining :=
  publicData_agree parameterOutput highs remaining _ fixed (mix_agree_fixed parameterOutput fixed table)

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

omit [Params] in
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

omit [Params] in
/-- Preparation facts: the structural cache persists, and every leaf's encoding search result is
the one recorded, for any function agreeing with the prepared cache. -/
theorem preparation_support (parameter : PublicParameter) (forsKey : Index → Digest)
    (base : QueryCache HashSpec) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support ((simulateQ randomOracle (searchAll parameter forsKey)).run base))
    (f : QueryImpl HashSpec Id) (hf : prepared.2.AgreesWithFn f) :
    base ≤ prepared.2 ∧ ∀ leaf, Prefix.firstEncoding f parameter topLayer rootTree leaf (forsKey leaf)
      encodingAttemptLimit 0 = prepared.1 leaf := by
  obtain ⟨hle, heval⟩ := replay_hash_support _ base prepared.1 prepared.2 hprepared f hf
  refine ⟨hle, fun leaf => ?_⟩
  rw [← heval, searchAll, eval_sequenceFin, ← ReferenceChoice.eval_search]

/-! ### Runs: short entries, cost, seed choice and support transfer -/

omit [Params] in
theorem OnlyC.withReveals {α : Type} {computation : OracleComp GraphView.CostSpec α}
    (h : OnlyC computation) : OnlyC (withReveals computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact OnlyC.pure' _
  | query_bind input next ih =>
      obtain ⟨hinput, hnext⟩ := onlyC_query_bind h
      rw [withReveals_query_bind']
      exact OnlyC.bind (OnlyC.query hinput) (fun value => OnlyC.map _ (ih value (hnext value)))

omit [Params] in
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

omit [Params] in
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

omit [Params] in
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

omit [Params] in
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

omit [Params] in
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
  rw [QueryCache.toFn_ofFn] at h
  split at h
  · assumption
  · cases h

/-- A reachable forest chain value is the public top or lies above a revealed position of its chain. -/
theorem reach_fchain (parameterOutput : HashOutput) (highs : CoordinateHighs) (fixed : HiddenGraph.Table)
    (reveals : List Coordinate) (coordinate : Coordinate)
    (h : Reach (sampleModel parameterOutput highs) (knownOf (truncateHash parameterOutput) fixed)
      reveals coordinate) :
    ∀ index c s j a i (p : FPos), coordinate = .fchain index c s j a i p →
      p.val = chainTop ∨ ∃ q : FPos, q.val ≤ p.val ∧ Coordinate.fchain index c s j a i q ∈ reveals := by
  induction h with
  | known coordinate value hvalue =>
      intro index c s j a i p heq
      subst heq
      exact Or.inl (knownOf_known _ fixed _ value hvalue)
  | reveal coordinate hmem =>
      intro index c s j a i p heq
      subst heq
      exact Or.inr ⟨p, le_rfl, hmem⟩
  | succ address _ ih =>
      intro index c s j a i p heq
      cases address with
      | chain lay tree leaf' chainIdx step =>
          simp [sampleModel, rowModel, Address.outputCoordinate] at heq
      | fchain index' c' s' j' a' i' t =>
          simp only [sampleModel, rowModel, Address.outputCoordinate, Coordinate.fchain.injEq] at heq
          obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := heq
          rcases ih _ _ _ _ _ _ ⟨t.val, by have := t.isLt; omega⟩ rfl with htop | ⟨q, hq, hmem⟩
          · have := t.isLt
            simp only [chainTop] at htop this
            omega
          · exact Or.inr ⟨q, by simp only at hq ⊢; omega, hmem⟩

theorem reach_chain (parameterOutput : HashOutput) (highs : CoordinateHighs) (fixed : HiddenGraph.Table)
    (reveals : List Coordinate) (leaf : LeafIndex) (hland : Landed (truncateHash parameterOutput) leaf)
    (word : Encoding)
    (hreveals : ∀ (chain : ChainIndex) (position : Digit),
      Coordinate.chain topLayer rootTree leaf chain position ∈ reveals → (word chain).val ≤ position.val)
    (coordinate : Coordinate)
    (h : Reach (sampleModel parameterOutput highs) (knownOf (truncateHash parameterOutput) fixed)
      reveals coordinate) :
    ∀ (chain : ChainIndex) (position : Digit),
      coordinate = .chain topLayer rootTree leaf chain position → (word chain).val ≤ position.val := by
  induction h with
  | known coordinate value hvalue =>
      intro chain position heq
      subst heq
      rcases knownOf_known _ fixed _ value hvalue with htop | hout
      · have := (word chain).isLt
        simp only [chainLength, winternitzBits] at this htop ⊢
        omega
      · exact (hout hland).elim
  | reveal coordinate hmem =>
      intro chain position heq
      subst heq
      exact hreveals chain position hmem
  | succ address _ ih =>
      intro chain position heq
      cases address with
      | chain lay tree leaf' chainIdx step =>
          simp only [sampleModel, rowModel, Address.outputCoordinate, Coordinate.chain.injEq] at heq
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq
          have hprev := ih chainIdx ⟨step.val, by have := step.isLt; omega⟩ rfl
          simp only at hprev ⊢
          omega
      | fchain index c s j a i t =>
          simp [sampleModel, rowModel, Address.outputCoordinate] at heq

/-! ### Small helpers -/

omit [Params] in
theorem firstEncoding_congr (f g : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (message : Digest)
    (h : ∀ counter : Counter, f (Wots.encodingInput parameter lay tree leaf message counter) =
      g (Wots.encodingInput parameter lay tree leaf message counter)) :
    ∀ attempts start, Prefix.firstEncoding f parameter lay tree leaf message attempts start =
      Prefix.firstEncoding g parameter lay tree leaf message attempts start := by
  have hencode : ∀ counter : Counter,
      evalWithAnswerFn f (encode parameter lay tree leaf message counter : OracleComp HashSpec (Option Encoding)) =
        evalWithAnswerFn g (encode parameter lay tree leaf message counter : OracleComp HashSpec (Option Encoding)) := by
    intro counter
    simp only [encode, evalWithAnswerFn_bind, eval_tweakableHash, evalWithAnswerFn_pure]
    rw [show f (tweakableHashInput parameter (.encoding lay tree leaf) (bytesLE 16 message ++ bytesLE 4 counter)) =
      g (tweakableHashInput parameter (.encoding lay tree leaf) (bytesLE 16 message ++ bytesLE 4 counter)) from
      h counter]
  intro attempts
  induction attempts with
  | zero => intro start; rfl
  | succ attempts ih =>
      intro start
      simp only [Prefix.firstEncoding, hencode, ih]

omit [Params] in
theorem digestInputs_mem (f : QueryImpl HashSpec Id) (pk : PublicKey) (message : Message)
    (signature : Signature) :
    tweakableHashInput pk.parameter .message
        (messageDigestPayload pk.root message signature.randomness) ∈
      SignatureWitness.trace f pk message signature := by
  unfold SignatureWitness.trace
  rw [Concrete.verify]
  apply queriedInputs_mono_bind_left
  unfold messageDigest messageDigestCall
  simp only [oracleHash, HasQuery.query]
  rw [queriedInputs_query_bind]
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
theorem not_canonicalRow_of_target (results : Index → Option (Counter × Encoding)) (input : HashInput)
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

omit [Params] in
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
      rw [ite_eq_right (hnot query hparse)]

theorem encoding_not_row (parameterOutput : HashOutput) (highs : CoordinateHighs) (table : HiddenGraph.Table)
    (leaf : LeafIndex) (message : Digest) (counter : Counter) :
    ∀ query, (sampleModel parameterOutput highs).parse
      (Wots.encodingInput (truncateHash parameterOutput) topLayer rootTree leaf message counter) = some query →
      ¬query.2 = table ((sampleModel parameterOutput highs).incoming query.1) := by
  intro query hparse
  rw [sampleModel_parse, Wots.encodingInput, parse_tweakable_none _ _ _ _
    (fun address => by cases address <;> simp [Address.position, Position.domain]) (by trivial)] at hparse
  cases hparse

theorem message_not_row (parameterOutput : HashOutput) (highs : CoordinateHighs) (table : HiddenGraph.Table)
    (payload : HashInput) :
    ∀ query, (sampleModel parameterOutput highs).parse
      (tweakableHashInput (truncateHash parameterOutput) .message payload) = some query →
      ¬query.2 = table ((sampleModel parameterOutput highs).incoming query.1) := by
  intro query hparse
  rw [sampleModel_parse, parse_tweakable_none _ _ _ _
    (fun address => by cases address <;> simp [Address.position, Position.domain]) (by trivial)] at hparse
  cases hparse

omit [Params] in
theorem tweakable_not_seedHit (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput)
    (seed : MasterSeed) : ¬SeedGuess.SeedHit (tweakableHashInput parameter domain payload) seed := by
  rintro ⟨parameter', derive, heq⟩
  exact keygenInput_ne_hashInput parameter' parameter derive domain seed payload heq

/-- The consistent preparation's targets are the sample's fixed targets. -/
theorem fullTable_eq (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (table : HiddenGraph.Table)
    (results : Index → Option (Counter × Encoding)) (f : QueryImpl HashSpec Id) (seed : MasterSeed)
    (hagreement : SeedModel.PreparedAgreement f seed (materialT parameterOutput fixed highs remaining table))
    (hfors : ∀ leaf : Index, SignatureWitness.canonicalForest f (truncateHash parameterOutput) seed leaf =
      (sampleData parameterOutput fixed highs remaining).forestKey leaf)
    (hselection : ∀ leaf : Index, ReferenceChoice.selection f (truncateHash parameterOutput) topLayer
      rootTree leaf ((sampleData parameterOutput fixed highs remaining).forestKey leaf) = results leaf) :
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
      refine congrArg (fun g => Option.map g (encodingAt fields)) (funext fun leaf => ?_)
      rw [hfors leaf]
      unfold ReferenceChoice.exemptInput ReferenceChoice.target ReferenceChoice.word
      rw [hselection leaf]

omit [Params] in
theorem selection_of_agree (parameter : PublicParameter) (forsKey : Index → Digest)
    (results : Index → Option (Counter × Encoding)) (f g : QueryImpl HashSpec Id)
    (hsearch : ∀ leaf, Prefix.firstEncoding g parameter topLayer rootTree leaf (forsKey leaf)
      encodingAttemptLimit 0 = results leaf)
    (hagree : ∀ (leaf : Index) (counter : Counter),
      f (Wots.encodingInput parameter topLayer rootTree leaf (forsKey leaf) counter) =
        g (Wots.encodingInput parameter topLayer rootTree leaf (forsKey leaf) counter))
    (leaf : Index) :
    ReferenceChoice.selection f parameter topLayer rootTree leaf (forsKey leaf) = results leaf := by
  unfold ReferenceChoice.selection
  rw [firstEncoding_congr f g _ _ _ _ _ (hagree leaf), hsearch leaf]

/-- A target hit at a recorded, non-canonical query is a cached hit of a fixed target. -/
theorem cached_hit (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (table : HiddenGraph.Table)
    (htable : tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table)
    (results : Index → Option (Counter × Encoding)) (cacheF : QueryCache HashSpec)
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

/-- A queried honest forest chain value lies above a revealed position of its chain. -/
theorem queried_fchain_revealed (parameterOutput : HashOutput) (highs : CoordinateHighs)
    (fixed table : HiddenGraph.Table) (reveals : List Coordinate) (entries : List (HiddenCost.Entry HashInput))
    (hguess : NoHiddenGuess (sampleModel parameterOutput highs) table
      (knownOf (truncateHash parameterOutput) fixed) reveals entries)
    (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain) (t : FStep)
    (hmem : Sum.inl (tweakableHashInput (truncateHash parameterOutput) (.fchain index c s j a i t)
      (bytesLE 16 (table (.fchain index c s j a i ⟨t.val, by have := t.isLt; omega⟩)))) ∈ entries) :
    ∃ q : FPos, q.val ≤ t.val ∧ Coordinate.fchain index c s j a i q ∈ reveals := by
  have hparse : (sampleModel parameterOutput highs).parse
      (tweakableHashInput (truncateHash parameterOutput) (.fchain index c s j a i t)
        (bytesLE 16 (table (.fchain index c s j a i ⟨t.val, by have := t.isLt; omega⟩)))) =
      some (.fchain index c s j a i t, table (.fchain index c s j a i ⟨t.val, by have := t.isLt; omega⟩)) := by
    rw [sampleModel_parse]
    exact parse_input _ _ (.fchain index c s j a i t, _) trivial
  have hreach := hguess _ hmem _ hparse (by rw [sampleModel_incoming]; rfl)
  rw [sampleModel_incoming] at hreach
  rcases reach_fchain parameterOutput highs fixed reveals _ hreach index c s j a i _ rfl with htop | hq
  · have := t.isLt
    simp only [chainTop] at htop this
    omega
  · exact hq

theorem queried_chain_reach (parameterOutput : HashOutput) (highs : CoordinateHighs)
    (fixed table : HiddenGraph.Table) (reveals : List Coordinate) (entries : List (HiddenCost.Entry HashInput))
    (hguess : NoHiddenGuess (sampleModel parameterOutput highs) table
      (knownOf (truncateHash parameterOutput) fixed) reveals entries)
    (leaf : LeafIndex) (hland : Landed (truncateHash parameterOutput) leaf) (word : Encoding)
    (hreveals : ∀ (chain : ChainIndex) (position : Digit),
      Coordinate.chain topLayer rootTree leaf chain position ∈ reveals → (word chain).val ≤ position.val)
    (chain : ChainIndex) (step : ChainStep)
    (hmem : Sum.inl (tweakableHashInput (truncateHash parameterOutput) (.chain topLayer rootTree leaf chain step)
      (bytesLE 16 (table (.chain topLayer rootTree leaf chain ⟨step.val, by have := step.isLt; omega⟩)))) ∈
        entries) :
    (word chain).val ≤ step.val := by
  have hparse : (sampleModel parameterOutput highs).parse
      (tweakableHashInput (truncateHash parameterOutput) (.chain topLayer rootTree leaf chain step)
        (bytesLE 16 (table (.chain topLayer rootTree leaf chain ⟨step.val, by have := step.isLt; omega⟩)))) =
      some (.chain topLayer rootTree leaf chain step,
        table (.chain topLayer rootTree leaf chain ⟨step.val, by have := step.isLt; omega⟩)) := by
    rw [sampleModel_parse]
    exact parse_input _ _ (.chain topLayer rootTree leaf chain step, _) hland
  have hreach := hguess _ hmem _ hparse (by rw [sampleModel_incoming]; rfl)
  rw [sampleModel_incoming] at hreach
  exact reach_chain parameterOutput highs fixed reveals leaf hland word hreveals _ hreach chain _ rfl

/-- Every revealed root-tree chain value of a retained leaf is at that leaf's canonical word. -/
theorem revealed_chain_word (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (seed : MasterSeed)
    (data : GraphView.PublicData) (log : QueryLog SigningSpec) (reveals : List Coordinate)
    (hgood : LogGood f parameter seed data log reveals)
    (hfors : ∀ leaf : Index, SignatureWitness.canonicalForest f parameter seed leaf = data.forestKey leaf)
    (leaf : Index) (chain : ChainIndex) (position : Digit)
    (hmem : Coordinate.chain topLayer rootTree leaf chain position ∈ reveals) :
    (SignatureWitness.chosenWord f parameter seed leaf chain).val ≤ position.val := by
  obtain ⟨entry, -, signature, -, hcoordinate⟩ := hgood.2 _ hmem
  unfold revealsOf at hcoordinate
  dsimp only at hcoordinate
  generalize hindex : digestIndex (evalWithAnswerFn f (messageDigest parameter data.root entry.1
    signature.randomness : OracleComp HashSpec MessageDigest)) = index at hcoordinate
  cases hfound : Prefix.firstEncoding f parameter topLayer rootTree index (data.forestKey index)
      encodingAttemptLimit 0 with
  | none => rw [hfound] at hcoordinate; cases hcoordinate
  | some pair =>
      rw [hfound] at hcoordinate
      rcases List.mem_append.mp hcoordinate with hchain | hfts
      · obtain ⟨chain', hchain'⟩ := List.mem_ofFn.mp hchain
        simp only [Coordinate.chain.injEq] at hchain'
        obtain ⟨-, -, rfl, rfl, rfl⟩ := hchain'
        have hword : SignatureWitness.chosenWord f parameter seed index = pair.2 := by
          unfold SignatureWitness.chosenWord ReferenceChoice.word ReferenceChoice.selection
          rw [hfors, hfound]
          rfl
        rw [hword]
      · obtain ⟨l, hl, hfts'⟩ := List.mem_flatten.mp hfts
        obtain ⟨c, rfl⟩ := List.mem_ofFn.mp hl
        obtain ⟨j, ch, k, -, hk⟩ := mem_treeReveals hfts'
        cases hk

/-- A canonical opening sharing an honest signature's message and randomizer is that signature. -/
theorem canonical_signed_eq (f : QueryImpl HashSpec Id) (sk : Seeded.SecretKey) (message : Message)
    (randomness : Randomness) (signature honest : Signature)
    (hland : Landed sk.parameter (digestIndex (Completeness.digestValue f sk message randomness)))
    (hfinish : evalWithAnswerFn f (Randomized.finishSign sk message randomness) = some honest)
    (hrandomness : honest.randomness = signature.randomness) (counter : Counter)
    (hchosen : SignatureWitness.chosenCounter f sk.parameter sk.seed
      (SignatureWitness.index f ⟨sk.root, sk.parameter⟩ message signature) = some counter)
    (hcanonical : SignatureWitness.CanonicalOpening f ⟨sk.root, sk.parameter⟩ sk.seed message signature counter
      (SignatureWitness.chosenWord f sk.parameter sk.seed
        (SignatureWitness.index f ⟨sk.root, sk.parameter⟩ message signature))) :
    signature = honest := by
  have hindex : SignatureWitness.index f ⟨sk.root, sk.parameter⟩ message honest =
      SignatureWitness.index f ⟨sk.root, sk.parameter⟩ message signature := by
    simp only [SignatureWitness.index, verificationDigest, hrandomness]
  have hcounter := honest_counter f sk message randomness honest hland hfinish
  rw [hindex, hchosen, Option.some.injEq] at hcounter
  obtain ⟨word, href, hhonest⟩ := SignatureWitness.canonical_of_finishSign f sk message randomness honest
    hland hfinish
  rw [hindex] at href
  rw [← hcounter] at href hhonest
  -- the honest word is the chosen word
  obtain ⟨pair, hpair⟩ : ∃ pair, ReferenceChoice.selection f sk.parameter topLayer rootTree
      (SignatureWitness.index f ⟨sk.root, sk.parameter⟩ message signature)
      (SignatureWitness.canonicalForest f sk.parameter sk.seed
        (SignatureWitness.index f ⟨sk.root, sk.parameter⟩ message signature)) = some pair := by
    cases h : ReferenceChoice.selection f sk.parameter topLayer rootTree
        (SignatureWitness.index f ⟨sk.root, sk.parameter⟩ message signature)
        (SignatureWitness.canonicalForest f sk.parameter sk.seed
          (SignatureWitness.index f ⟨sk.root, sk.parameter⟩ message signature)) with
    | none => simp [SignatureWitness.chosenCounter, h] at hchosen
    | some pair => exact ⟨pair, rfl⟩
  have hpairCounter : pair.1 = counter := by
    simpa [SignatureWitness.chosenCounter, hpair] using hchosen
  have hencode := ReferenceChoice.firstEncoding_sound f sk.parameter topLayer rootTree _ _
    encodingAttemptLimit 0 pair.1 pair.2 hpair
  rw [hpairCounter] at hencode
  have hword : word = SignatureWitness.chosenWord f sk.parameter sk.seed
      (SignatureWitness.index f ⟨sk.root, sk.parameter⟩ message signature) := by
    have h := href.symm.trans hencode
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
  have hread : cacheF (tweakableHashInput (truncateHash parameterOutput) .message
      (messageDigestPayload root message signature.randomness)) =
      some (f (tweakableHashInput (truncateHash parameterOutput) .message
        (messageDigestPayload root message signature.randomness))) := by
    have hentry := htrace _ (digestInputs_mem f ⟨root, truncateHash parameterOutput⟩ message signature)
    have hnot := message_not_row parameterOutput highs table
      (messageDigestPayload root message signature.randomness)
    obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp (hcached _ hentry hnot)
    have hfin := finalFn_unparsed parameterOutput highs table cacheF _ hnot
    rw [hanswer] at hfin
    rw [hanswer, (hagree _ hentry).trans hfin]
    rfl
  unfold cachedDigest verificationDigest
  rw [hread]
  simp only [messageDigest, messageDigestCall, oracleHash, HasQuery.query, evalWithAnswerFn_bind,
    evalWithAnswerFn_pure]
  rfl

/-! ### The win implication -/

attribute [local irreducible] ReferenceChoice.selection encodingAttemptLimit

/-- **Case analysis.** For any answer function consistent with the sample and agreeing with the
final cache on the run's queries, an accepted fresh forgery yields a cached target hit or FORS
coverage. -/
theorem bad_of_accepted (hb : 0 < subtreeHeight) (parameterOutput : HashOutput) (fixed : HiddenGraph.Table)
    (highs : CoordinateHighs) (remaining : RemainingOutputs) (table : HiddenGraph.Table)
    (htable : tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table)
    (results : Index → Option (Counter × Encoding)) (cacheF : QueryCache HashSpec)
    (reveals : List Coordinate) (entries : List (HiddenCost.Entry HashInput))
    (f : QueryImpl HashSpec Id) (seed : MasterSeed)
    (hcons : GraphCorrectness.Consistent f (truncateHash parameterOutput) seed
      (labelsOf (materialT parameterOutput fixed highs remaining table)
        (answersT parameterOutput fixed highs remaining table)))
    (hbound : GraphCorrectness.BoundaryCorrect f (truncateHash parameterOutput) seed
      (labelsOf (materialT parameterOutput fixed highs remaining table)
        (answersT parameterOutput fixed highs remaining table)))
    (hdata : GraphView.DataCorrect f (truncateHash parameterOutput) seed
      (sampleData parameterOutput fixed highs remaining))
    (hcoord : GraphView.CoordinatesCorrect f (truncateHash parameterOutput) seed table)
    (hfors : ∀ leaf : Index, SignatureWitness.canonicalForest f (truncateHash parameterOutput) seed leaf =
      (sampleData parameterOutput fixed highs remaining).forestKey leaf)
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
    (hgood : LogGood f (truncateHash parameterOutput) seed (sampleData parameterOutput fixed highs remaining)
      log reveals)
    (hverify : evalWithAnswerFn f (Concrete.verify ⟨(sampleData parameterOutput fixed highs remaining).root,
      truncateHash parameterOutput⟩ forgery.message forgery.signature : OracleComp HashSpec Bool) = true)
    (hvalid : SigningTranscript.Valid log) (hnotContains : ¬SigningTranscript.Contains log forgery) :
    CacheMatch.Bad (targets (truncateHash parameterOutput)
        (compTable parameterOutput fixed highs remaining table results)) cacheF ∨
      ForestCover (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining).root
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
    ⟨counter, hchosen, hcanon⟩ | htree | ⟨hland, hexc⟩
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
      have hmarks := funext (digestMarks_eq (verificationDigest f ⟨(sampleData parameterOutput fixed highs
        remaining).root, truncateHash parameterOutput⟩ forgery.message forgery.signature))
      have hopen := hcanon.2.2.2.2
      have hrun := SignatureWitness.verification_forest_run f ⟨(sampleData parameterOutput fixed highs
        remaining).root, truncateHash parameterOutput⟩ forgery.message forgery.signature
      rw [hmarks] at hopen hrun
      rcases Forest.Opening.covered_or_hidden f (truncateHash parameterOutput) _ seed _
          forgery.signature.forest (revealedSet reveals) _ hopen hrun with
        hcovered | ⟨index, c, s, j, a, i, t, hnot, hmem⟩
      · refine ⟨hvalid, _, cachedDigest_eq parameterOutput highs table cacheF f entries hagree hcached _
          forgery.message forgery.signature htrace, hcanon.1, ?_, hcovered⟩
        intro entry hentry honest hhonest hpair
        exact hsigned ⟨entry, hentry, honest, hhonest, hpair.1, hpair.2⟩
      · exfalso
        rw [show Completeness.chainValueOf f (truncateHash parameterOutput) index c s j a i seed t.val =
          table (.fchain index c s j a i ⟨t.val, by have := t.isLt; omega⟩) from
          (hcoord.2 index c s j a i ⟨t.val, by have := t.isLt; omega⟩).symm] at hmem
        obtain ⟨q, hq, hrev⟩ := queried_fchain_revealed parameterOutput highs fixed table reveals entries hguess
          index c s j a i t (htrace _ hmem)
        have := hnot q (by simp only [revealedSet, Finset.mem_filter, Finset.mem_univ, true_and]; exact hrev)
        omega
  · left
    obtain ⟨input, hinput, hmem⟩ := treeHit_hit f (truncateHash parameterOutput) seed _ hcons hbound _ rfl
      forgery.message forgery.signature htree
    exact hhit input hinput (graph_targets_subset _ _ _ _ _ hmem)
  · rcases hexc with henc | hleafMatch | hchain | ⟨hforsExc, -⟩
    · left
      obtain ⟨input, hinput, hmem⟩ := encodingMatch_hit f (truncateHash parameterOutput) seed _ _ _ henc
      exact hhit input hinput hmem
    · left
      obtain ⟨input, hinput, hmem⟩ := leafOutput_hit f (truncateHash parameterOutput) seed _ hcons _ hland _
        hleafMatch
      exact hhit input hinput (graph_targets_subset _ _ _ _ _ hmem)
    · rcases Wots.ChainException.hidden_or_output f _ _ _ _ _ _ hchain with
        ⟨chain, step, hlt, hmem⟩ | houtput
      · exfalso
        have hvalue := hcoord.1 _ hland chain ⟨step.val, by have := step.isLt; omega⟩
        rw [← hvalue] at hmem
        have hle := queried_chain_reach parameterOutput highs fixed table reveals entries hguess _ hland
          (SignatureWitness.chosenWord f (truncateHash parameterOutput) seed
            (SignatureWitness.index f _ forgery.message forgery.signature))
          (fun chain position h => revealed_chain_word f _ seed _ log reveals hgood hfors _ chain position h)
          chain step (htrace _ hmem)
        dsimp only at hlt hle
        omega
      · left
        obtain ⟨input, hinput, hmem⟩ := chainOutput_hit f (truncateHash parameterOutput) seed _ hcons _ hland _
          houtput
        exact hhit input hinput (graph_targets_subset _ _ _ _ _ hmem)
    · left
      obtain ⟨input, hinput, hmem⟩ := forestException_hit f (truncateHash parameterOutput) seed _ hcons _ _ _
        hforsExc
      exact hhit input (SignatureWitness.verification_forest_run f _ forgery.message forgery.signature input hinput)
        (graph_targets_subset _ _ _ _ _ hmem)

/-- Prepared answers take priority over a sample function. -/
def preferCache (cache : QueryCache HashSpec) (f : QueryImpl HashSpec Id) : QueryImpl HashSpec Id :=
  fun input => (cache input).getD (f input)

omit [Params] in
theorem preferCache_agrees (cache : QueryCache HashSpec) (f : QueryImpl HashSpec Id) :
    cache.AgreesWithFn (preferCache cache f) := fun input answer h => by
  simp [preferCache, h]

/-- The outside table read off a final lazy cache. -/
noncomputable def finalTable (parameterOutput : HashOutput) (highs : CoordinateHighs)
    (table : HiddenGraph.Table) (cacheF : QueryCache HashSpec) : Eager.Table :=
  fun short => finalFn (sampleModel parameterOutput highs) table cacheF short.val

omit [Params] in
theorem encodingInput_short (parameter : PublicParameter) (leaf : Index) (key : Digest) (counter : Counter) :
    Short.IsShort (Wots.encodingInput parameter topLayer rootTree leaf key counter) := by
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
    (leaf : Index) (key : Digest) (counter : Counter) :
    f (Wots.encodingInput (truncateHash parameterOutput) topLayer rootTree leaf key counter) =
      preferCache prepCache f (Wots.encodingInput (truncateHash parameterOutput) topLayer rootTree leaf key counter) := by
  unfold preferCache
  cases hp : prepCache (Wots.encodingInput (truncateHash parameterOutput) topLayer rootTree leaf key counter) with
  | none => exact (Option.getD_none).symm
  | some answer =>
      rw [Option.getD_some, hagreeAll _ (encodingInput_short _ _ _ _) (tweakable_not_seedHit _ _ _ seed),
        finalFn_unparsed parameterOutput highs table cacheF _ (encoding_not_row parameterOutput highs table leaf _ counter),
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
theorem win_implies_bad (hb : 0 < subtreeHeight) (adversary : Adversary) (q : Nat) (hq : q < 2 ^ 256)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs)
    (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (table : HiddenGraph.Table)
    (htable : tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table)
    (outcome : Outcome) (reveals : List Coordinate) (entries : List (HiddenCost.Entry HashInput))
    (cacheF : QueryCache HashSpec)
    (hstop : some (((some outcome, reveals), entries), cacheF) ∈ support
      (HiddenOutside.stopped (sampleModel parameterOutput highs) table
        (HiddenCost.erase (HiddenCost.trace (richProgram (Internalize.internalize adversary) q
          (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining))))
        (knownOf (truncateHash parameterOutput) fixed) prepared.2))
    (hwin : outcomeWins outcome = true) :
    CacheMatch.Bad (targets (truncateHash parameterOutput)
        (compTable parameterOutput fixed highs remaining table prepared.1)) cacheF ∨
      ForestCover (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining).root
        outcome reveals cacheF := by
  obtain ⟨hgrow, hrun, hguess⟩ := lazy_support (sampleModel parameterOutput highs) table _
    (knownOf (truncateHash parameterOutput) fixed) prepared.2 cacheF _ entries hstop
  obtain ⟨-, hcached⟩ := lazy_cached (sampleModel parameterOutput highs) table _
    (knownOf (truncateHash parameterOutput) fixed) prepared.2 cacheF _ entries hstop
  have hOnly : OnlyC (richProgram (Internalize.internalize adversary) q (truncateHash parameterOutput)
      (sampleData parameterOutput fixed highs remaining)) :=
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
      (sampleData parameterOutput fixed highs remaining) := by
    have h := GraphView.publicData_correct f' _ seed _ hcons hbound
    rwa [publicData_T] at h
  have hcoord : GraphView.CoordinatesCorrect f' (truncateHash parameterOutput) seed table := by
    have h := GraphView.coordinates_correct f' _ seed _ hcons
    have heq := (Reduce.sampleCoordinates_eq (materialT parameterOutput fixed highs remaining table) seed
      (answersT parameterOutput fixed highs remaining table) (finalTable parameterOutput highs table cacheF)).trans
      (graphCoordinates_T parameterOutput fixed highs remaining table htable)
    unfold Assembly.sampleCoordinates at heq
    rwa [heq] at h
  obtain ⟨hverified, htrace, hgood⟩ := rich_support f' table (Internalize.internalize adversary) q
    (truncateHash parameterOutput) seed (sampleData parameterOutput fixed highs remaining) hdata hcoord
    outcome reveals entries hrun'
  have hfors : ∀ leaf : Index, SignatureWitness.canonicalForest f' (truncateHash parameterOutput) seed leaf =
      (sampleData parameterOutput fixed highs remaining).forestKey leaf := fun leaf => (hdata.forestKey leaf).symm
  have hencAgree : ∀ (leaf : Index) (counter : Counter),
      f' (Wots.encodingInput (truncateHash parameterOutput) topLayer rootTree leaf
        ((sampleData parameterOutput fixed highs remaining).forestKey leaf) counter) =
      preferCache prepared.2 f' (Wots.encodingInput (truncateHash parameterOutput) topLayer rootTree leaf
        ((sampleData parameterOutput fixed highs remaining).forestKey leaf) counter) :=
    fun leaf counter => encoding_preferCache parameterOutput highs table cacheF prepared.2 f' seed
      (fun input hshort hnot => hagreeAll input hshort hnot) hgrow leaf _ counter
  have hselection := selection_of_agree (truncateHash parameterOutput)
    (sampleData parameterOutput fixed highs remaining).forestKey prepared.1 f' (preferCache prepared.2 f')
    hstructPrep.2 hencAgree
  have hfull := fullTable_eq parameterOutput fixed highs remaining table prepared.1 f' seed hagreement
    hfors hselection
  obtain ⟨forgery, log, verified⟩ := outcome
  simp only [outcomeWins, Bool.and_eq_true, decide_eq_true_eq] at hwin
  obtain ⟨⟨hvalid, hnotContains⟩, rfl⟩ := hwin
  exact bad_of_accepted hb parameterOutput fixed highs remaining table htable prepared.1 cacheF reveals entries
    f' seed hcons hbound hdata hcoord hfors hfull hagree hcached hguess forgery log htrace hgood
    hverified.symm hvalid hnotContains

end Sphincs.Security.HiddenBridge
