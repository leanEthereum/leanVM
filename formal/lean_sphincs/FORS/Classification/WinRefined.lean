import FORS.Classification.RefinedEvents
import FORS.Classification.SignedReveals
import FORS.Classification.RecoveredFors

/-! Deterministic core of the refined classification: a winning non-stopped run of the rich
program, started from knowledge that also exposes the chain values at and above the prepared
word of every retained key, yields a cached first-order hit or one of the paired events of
`badA`. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.HiddenBridge

variable [Params]

open Concrete Completeness Graph GraphCorrectness TargetAssignment HiddenGraph Assembly SeedModel Reduce Eager

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable


/-! ### First-order inputs -/

/-- A second-order tweakable input is a chain input outside the retained keys' above-word steps or a
FORS leaf input. -/
theorem secondOrder_tweakable {parameter : PublicParameter} {results : OtsKey → Option (Counter × Encoding)}
    {domain : HashDomain} {payload : HashInput}
    (h : SecondOrderInput parameter results (tweakableHashInput parameter domain payload)) :
    (∃ lay tree leaf chain step, domain = .chain lay tree leaf chain step ∧
      ¬(PrunedGraph.KeyActive parameter lay tree leaf ∧
        (preparedWord results (lay, tree, leaf) chain).val ≤ step.val)) ∨
    ∃ index κ leaf, domain = .forsLeaf index κ leaf := by
  rcases h with ⟨lay, tree, leaf, chain, step, payload', heq, hnot⟩ | ⟨index, κ, leaf, payload', heq⟩
  · have hf := (tweakableInput_injective heq).1
    left
    refine ⟨lay, tree, leaf, chain, step, ?_, hnot⟩
    cases domain with
    | chain => exact hashFields_injective trivial trivial hf
    | _ => simp [hashDomainFields, tweakFields, treeFields] at hf
  · unfold fleafInput at heq
    have hf := (tweakableInput_injective heq).1
    right
    refine ⟨index, κ, leaf, ?_⟩
    cases domain with
    | forsLeaf => exact hashFields_injective trivial trivial hf
    | _ => simp [hashDomainFields, tweakFields, treeFields] at hf

/-- A tweakable input outside the chain and FORS leaf domains is first order. -/
theorem not_secondOrder (parameter : PublicParameter) (results : OtsKey → Option (Counter × Encoding))
    (domain : HashDomain) (payload : HashInput)
    (hchain : ∀ lay tree leaf chain step, domain ≠ .chain lay tree leaf chain step)
    (hfts : ∀ index κ leaf, domain ≠ .forsLeaf index κ leaf) :
    ¬SecondOrderInput parameter results (tweakableHashInput parameter domain payload) := by
  intro h
  rcases secondOrder_tweakable h with ⟨lay, tree, leaf, chain, step, heq, -⟩ | ⟨index, κ, leaf, heq⟩
  · exact hchain _ _ _ _ _ heq
  · exact hfts _ _ _ heq

/-- A chain input of a retained key at or above its prepared word is first order. -/
theorem not_secondOrder_chain (parameter : PublicParameter) (results : OtsKey → Option (Counter × Encoding))
    (key : OtsKey) (chain : ChainIndex) (step : ChainStep) (payload : Digest)
    (h : PrunedGraph.KeyActive parameter key.1 key.2.1 key.2.2 ∧ (preparedWord results key chain).val ≤ step.val) :
    ¬SecondOrderInput parameter results (chainInput parameter key chain step payload) := by
  intro hs
  rcases secondOrder_tweakable (domain := .chain key.1 key.2.1 key.2.2 chain step) hs with
    ⟨lay', tree', leaf', chain', step', heq, hnot⟩ | ⟨index, κ, leaf, heq⟩
  · simp only [HashDomain.chain.injEq] at heq
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := heq
    exact hnot h
  · cases heq

section Sample

variable (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
  (remaining : RemainingOutputs) (table : HiddenGraph.Table)

/-- A first-order target hit at a recorded, non-canonical query is a cached first-order hit. -/
theorem cached_hitA (htable : tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table)
    (results : OtsKey → Option (Counter × Encoding)) (cacheF : QueryCache HashSpec)
    (f : QueryImpl HashSpec Id) (entries : List (HiddenCost.Entry HashInput))
    (hagree : ∀ input, Sum.inl input ∈ entries →
      f input = finalFn (sampleModel parameterOutput highs) table cacheF input)
    (hcached : CachedQueries (sampleModel parameterOutput highs) table cacheF entries)
    (input : HashInput) (hentry : Sum.inl input ∈ entries)
    (hmem : truncateHash (f input) ∈ targets (truncateHash parameterOutput)
      (compTable parameterOutput fixed highs remaining table results) input)
    (hfirst : ¬SecondOrderInput (truncateHash parameterOutput) results input) :
    CacheMatch.Bad (targetsA (truncateHash parameterOutput) results
      (compTable parameterOutput fixed highs remaining table results)) cacheF := by
  have hnot := not_canonicalRow_of_target parameterOutput fixed highs remaining table htable
    results input ⟨_, hmem⟩
  obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp (hcached input hentry hnot)
  have hfin := finalFn_unparsed parameterOutput highs table cacheF input hnot
  rw [hanswer] at hfin
  refine ⟨input, answer, hanswer, ?_⟩
  have hvalue : f input = answer := (hagree input hentry).trans hfin
  unfold targetsA
  rw [if_neg hfirst, ← hvalue]
  exact hmem

/-- A recorded query that is not a correct guess is cached with its answer. -/
theorem cached_read (cacheF : QueryCache HashSpec) (f : QueryImpl HashSpec Id)
    (entries : List (HiddenCost.Entry HashInput))
    (hagree : ∀ input, Sum.inl input ∈ entries →
      f input = finalFn (sampleModel parameterOutput highs) table cacheF input)
    (hcached : CachedQueries (sampleModel parameterOutput highs) table cacheF entries)
    (input : HashInput) (hentry : Sum.inl input ∈ entries)
    (hnot : ∀ query, (sampleModel parameterOutput highs).parse input = some query →
      ¬query.2 = table ((sampleModel parameterOutput highs).incoming query.1)) :
    cacheF input = some (f input) := by
  obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp (hcached input hentry hnot)
  have hfin := finalFn_unparsed parameterOutput highs table cacheF input hnot
  rw [hanswer] at hfin
  rw [hanswer, (hagree input hentry).trans hfin]
  rfl

/-- A chain input whose payload is not the table value is not a correct guess. -/
theorem chain_not_row (key : OtsKey)
    (hactive : PrunedGraph.KeyActive (truncateHash parameterOutput) key.1 key.2.1 key.2.2)
    (chain : ChainIndex) (step : ChainStep) (payload : Digest)
    (hne : payload ≠ table (.chain key.1 key.2.1 key.2.2 chain ⟨step.val, by have := step.isLt; omega⟩)) :
    ∀ query, (sampleModel parameterOutput highs).parse
      (chainInput (truncateHash parameterOutput) key chain step payload) = some query →
      ¬query.2 = table ((sampleModel parameterOutput highs).incoming query.1) := by
  intro query hparse hmatch
  have hp : (sampleModel parameterOutput highs).parse
      (chainInput (truncateHash parameterOutput) key chain step payload) =
      some (.chain key.1 key.2.1 key.2.2 chain step, payload) := by
    rw [sampleModel_parse]
    exact parse_input _ _ (.chain key.1 key.2.1 key.2.2 chain step, payload) hactive
  rw [hp, Option.some.injEq] at hparse
  subst hparse
  rw [sampleModel_incoming] at hmatch
  exact hne hmatch

/-- A FORS leaf input whose payload is not the table secret is not a correct guess. -/
theorem fleaf_not_row (index : Index) (κ : FTree) (leaf : FLeaf) (payload : Digest)
    (hne : payload ≠ table (.fors index κ leaf 0)) :
    ∀ query, (sampleModel parameterOutput highs).parse
      (fleafInput (truncateHash parameterOutput) index κ leaf payload) = some query →
      ¬query.2 = table ((sampleModel parameterOutput highs).incoming query.1) := by
  intro query hparse hmatch
  have hp : (sampleModel parameterOutput highs).parse
      (fleafInput (truncateHash parameterOutput) index κ leaf payload) =
      some (.fleaf index κ leaf, payload) := by
    rw [sampleModel_parse]
    exact parse_input _ _ (.fleaf index κ leaf, payload) trivial
  rw [hp, Option.some.injEq] at hparse
  subst hparse
  rw [sampleModel_incoming] at hmatch
  exact hne hmatch

end Sample

/-! ### Reachable coordinates from exposed knowledge -/

section Reach

variable (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
  (results : OtsKey → Option (Counter × Encoding)) (known : HiddenReveal.Knowledge Coordinate)
  (hknown : ∀ c v, known c = some v →
    knownOf (truncateHash parameterOutput) fixed c = some v ∨ AboveWord (truncateHash parameterOutput) results c)

include hknown in
/-- A coordinate reachable from exposed knowledge is reachable from the fixed knowledge and the
reveals together with the above-word coordinates. -/
theorem reach_expose (reveals : List Coordinate) {coordinate : Coordinate}
    (h : Reach (sampleModel parameterOutput highs) known reveals coordinate) :
    Reach (sampleModel parameterOutput highs) (knownOf (truncateHash parameterOutput) fixed)
      (reveals ++ aboveList (truncateHash parameterOutput) results) coordinate :=
  reach_mono _ (fun c v hc => by
      rcases hknown c v hc with h | h
      · exact .known c v h
      · exact .reveal c (List.mem_append_right _ (mem_aboveList.mpr h)))
    (fun c hc => .reveal c (List.mem_append_left _ hc)) h

include hknown in
/-- A queried canonical FORS secret was revealed: exposure adds no FORS secrets. -/
theorem queried_fleaf_revealedA (table : HiddenGraph.Table) (reveals : List Coordinate)
    (entries : List (HiddenCost.Entry HashInput))
    (hguess : NoHiddenGuess (sampleModel parameterOutput highs) table known reveals entries)
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
  have hmem' := reach_fors parameterOutput highs fixed _ _
    (reach_expose parameterOutput fixed highs results known hknown reveals hreach) index κ leaf rfl
  rcases List.mem_append.mp hmem' with h | h
  · exact h
  · exact False.elim (mem_aboveList.mp h)

include hknown in
/-- A queried canonical chain value of a retained key is at or above its prepared word. -/
theorem queried_chain_reachA (table : HiddenGraph.Table) (reveals : List Coordinate)
    (entries : List (HiddenCost.Entry HashInput))
    (hguess : NoHiddenGuess (sampleModel parameterOutput highs) table known reveals entries)
    (key : OtsKey) (hactive : PrunedGraph.KeyActive (truncateHash parameterOutput) key.1 key.2.1 key.2.2)
    (hreveals : ∀ (chain : ChainIndex) (position : Digit),
      Coordinate.chain key.1 key.2.1 key.2.2 chain position ∈ reveals →
        (preparedWord results key chain).val ≤ position.val)
    (chain : ChainIndex) (step : ChainStep)
    (hmem : Sum.inl (tweakableHashInput (truncateHash parameterOutput) (.chain key.1 key.2.1 key.2.2 chain step)
      (bytesLE 16 (table (.chain key.1 key.2.1 key.2.2 chain ⟨step.val, by have := step.isLt; omega⟩)))) ∈
        entries) :
    (preparedWord results key chain).val ≤ step.val := by
  have hparse : (sampleModel parameterOutput highs).parse
      (tweakableHashInput (truncateHash parameterOutput) (.chain key.1 key.2.1 key.2.2 chain step)
        (bytesLE 16 (table (.chain key.1 key.2.1 key.2.2 chain ⟨step.val, by have := step.isLt; omega⟩)))) =
      some (.chain key.1 key.2.1 key.2.2 chain step,
        table (.chain key.1 key.2.1 key.2.2 chain ⟨step.val, by have := step.isLt; omega⟩)) := by
    rw [sampleModel_parse]
    exact parse_input _ _ (.chain key.1 key.2.1 key.2.2 chain step, _) hactive
  have hreach := hguess _ hmem _ hparse (by rw [sampleModel_incoming]; rfl)
  rw [sampleModel_incoming] at hreach
  refine reach_chain parameterOutput highs fixed _ key.1 key.2.1 key.2.2 hactive (preparedWord results key) ?_ _
    (reach_expose parameterOutput fixed highs results known hknown reveals hreach) chain _ rfl
  intro chain' position hposition
  rcases List.mem_append.mp hposition with h | h
  · exact hreveals chain' position h
  · exact (mem_aboveList.mp h).2

include hknown in
/-- A recorded chain query below the prepared word of a retained key is not a correct guess. -/
theorem chain_below_ne (table : HiddenGraph.Table) (reveals : List Coordinate)
    (entries : List (HiddenCost.Entry HashInput))
    (hguess : NoHiddenGuess (sampleModel parameterOutput highs) table known reveals entries)
    (key : OtsKey) (hactive : PrunedGraph.KeyActive (truncateHash parameterOutput) key.1 key.2.1 key.2.2)
    (hreveals : ∀ (chain : ChainIndex) (position : Digit),
      Coordinate.chain key.1 key.2.1 key.2.2 chain position ∈ reveals →
        (preparedWord results key chain).val ≤ position.val)
    (chain : ChainIndex) (step : ChainStep) (payload : Digest)
    (hlt : step.val < (preparedWord results key chain).val)
    (hmem : Sum.inl (chainInput (truncateHash parameterOutput) key chain step payload) ∈ entries) :
    payload ≠ table (.chain key.1 key.2.1 key.2.2 chain ⟨step.val, by have := step.isLt; omega⟩) := by
  intro heq
  rw [heq] at hmem
  have hle := queried_chain_reachA parameterOutput fixed highs results known hknown table reveals entries
    hguess key hactive hreveals chain step hmem
  omega

end Reach

/-! ### First-order hits at explicit inputs -/

section Hits

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (seed : MasterSeed)
  (labels : CanonicalGraphLabels) (hconsistent : Consistent f parameter seed labels)

include hconsistent in
/-- A tree hit at a queried node input, which is first order. -/
theorem treeHit_hitA (hboundary : BoundaryCorrect f parameter seed labels) (pk : PublicKey)
    (hparameter : pk.parameter = parameter) (message : Message) (signature : Signature) (j : Nat)
    (h : SignatureWitness.TreeHit f pk seed message signature j) :
    ∃ input ∈ SignatureWitness.trace f pk message signature,
      truncateHash (f input) ∈ targets parameter (graphTable f parameter seed labels) input ∧
      ∀ results, ¬SecondOrderInput parameter results input := by
  subst hparameter
  obtain ⟨-, value, -, hrun, hcase⟩ := h
  generalize hlay : layerUp j = lay at hrun hcase
  generalize htree : SignatureWitness.keyTree (SignatureWitness.index f pk message signature) lay = tree
    at hrun hcase
  generalize hleaf : SignatureWitness.keyLeaf (SignatureWitness.index f pk message signature) lay = leaf
    at hrun hcase
  generalize hpath : signaturePath signature lay = path at hrun hcase
  have hmem : ∀ level, level < layerHeight lay →
      merkleInput f pk.parameter (fun height index => .node lay tree height index) leaf.val path
        value level ∈ SignatureWitness.trace f pk message signature := by
    intro level hlevel
    apply hrun
    rw [← merkleFold_treeFold]
    exact merkleInput_mem f pk.parameter _ leaf.val path value (layerHeight lay) level hlevel
  have hnode : ∀ level results, ¬SecondOrderInput pk.parameter results
      (merkleInput f pk.parameter (fun height index => .node lay tree height index) leaf.val path
        value level) := fun level results => by
    unfold merkleInput
    exact not_secondOrder _ _ _ _ (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)
  rcases hcase with ⟨reference, hreference, level, hlevel, hparent, hne, hout⟩ |
    ⟨hlaytop, level, hlevel, ⟨hlower, hpositive, hsurrogate⟩, haddress⟩
  · refine ⟨_, hmem level hlevel, ?_, hnode level⟩
    have hpos := active_hit f pk.parameter seed labels
      (treePosition lay tree (level + 1) (hlevel.trans_le (layerHeight_le lay))
        ⟨reference.val / 2 ^ (level + 1), (Nat.div_le_self _ _).trans_lt reference.isLt⟩)
      (tree_path_active pk.parameter lay tree reference hreference (level + 1) hlevel)
      (orderedPayload (leaf.val.testBit level)
        (merkleValue f pk.parameter (fun height index => .node lay tree height index) leaf.val
          path value level) (path level))
      (by
        rw [tree_path_input f pk.parameter seed labels hconsistent hboundary lay tree reference
          hreference level hlevel]
        intro heq
        apply hne
        unfold merkleInput
        rw [hparent]
        exact heq)
      (by
        rw [tree_path_value f pk.parameter seed labels hconsistent hboundary lay tree reference
          hreference (level + 1) hlevel]
        change truncateHash (f (tweakableHashInput pk.parameter
          (.node lay tree (level + 1) (reference.val / 2 ^ (level + 1))) _)) = _
        rw [← hparent]
        exact hout)
    unfold merkleInput
    rw [hparent]
    exact hpos
  · subst hlaytop
    have htop : tree = rootTree := by
      rw [← htree]; exact Completeness.treeIndexAt_top _
    subst htop
    refine ⟨_, hmem (level - 1) (by omega), ?_, hnode (level - 1)⟩
    have hlevel' : level < maxLayerHeight := hlevel.trans_le (layerHeight_le _)
    have hentry := PrunedGraph.referenceTable_surrogate pk.parameter (otsSecrets f pk.parameter seed)
      (ftsSecrets f pk.parameter seed) (surrogates f pk.parameter seed) labels topLayer rootTree
      ⟨level, hlevel'⟩ hpositive rfl rfl hlower
    have hinput : merkleInput f pk.parameter (fun height index => .node topLayer rootTree height index)
        leaf.val path value (level - 1) =
        tweakableHashInput pk.parameter (.node topLayer rootTree level (boundaryIndex pk.parameter level))
          (orderedPayload (leaf.val.testBit (level - 1))
            (merkleValue f pk.parameter (fun height index => .node topLayer rootTree height index)
              leaf.val path value (level - 1)) (path (level - 1))) := by
      simp only [merkleInput, Nat.sub_add_cancel hpositive, haddress]
    rw [hinput]
    unfold graphTable
    rw [targets_at_entry _ _ _ _ _ hentry]
    simp only [reduceCtorEq, ↓reduceIte, Finset.mem_singleton]
    rw [← hinput]
    exact hsurrogate

include hconsistent in
/-- A FORS node match hits at a queried first-order input. -/
theorem nodeException_hitA (index : Index) (leaves : FTree → FLeaf) (opening : FTree → TreeOpening)
    (h : Fors.NodeException f parameter index seed leaves opening) :
    ∃ input ∈ queriedInputs f (forsRecover parameter index leaves opening : OracleComp HashSpec ForsKey),
      truncateHash (f input) ∈ targets parameter (graphTable f parameter seed labels) input ∧
      ∀ results, ¬SecondOrderInput parameter results input := by
  obtain ⟨κ, level, hlevel, -, hneq, hout⟩ := h
  have hcanon : Fors.leafValue f parameter index κ (leaves κ)
      (Completeness.forsSecretValue f parameter index κ seed (leaves κ)) =
        Completeness.forsLeafValue f parameter index κ seed (leaves κ) := by
    rw [Fors.leafValue_canonical, Completeness.forsNodeValue_zero]
  have hfolded := hlevel
  have hlevel : level < forsHeight := by omega
  have hl1 : level + 1 ≤ forsHeight := hlevel
  rw [hcanon] at hneq hout
  have hdom : Fors.forsDomain index κ (level + 1) ((leaves κ).val / 2 ^ (level + 1)) =
      HashDomain.forsNode index κ ⟨level, by omega⟩
        ⟨(leaves κ).val / 2 ^ (level + 1), (Nat.div_le_self _ _).trans_lt (leaves κ).isLt⟩ := by
    rw [Fors.forsDomain, dif_pos ⟨by omega, by omega⟩]
    congr 2
    exact Nat.mod_eq_of_lt ((Nat.div_le_self _ _).trans_lt (leaves κ).isLt)
  refine ⟨_, Fors.nodeInput_mem f parameter index leaves opening κ level hfolded,
    active_hit' f parameter seed labels (forsPosition index κ (level + 1) hl1
      ⟨(leaves κ).val / 2 ^ (level + 1), (Nat.div_le_self _ _).trans_lt (leaves κ).isLt⟩)
      trivial _ ⟨_, by simp only [merkleInput]; rw [hdom]; rfl⟩ ?_ ?_, fun results => ?_⟩
  · rw [fors_path_input f parameter seed labels hconsistent index κ _ level hlevel]
    exact hneq
  · rw [fors_path_value f parameter seed labels hconsistent index κ _ (level + 1) hl1]
    exact hout
  · unfold merkleInput
    rw [hdom]
    exact not_secondOrder _ _ _ _ (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h)

end Hits

/-! ### FORS leaf contacts -/

/-- A FORS leaf match at a recorded input is a leaf contact at the tree's selected leaf. -/
theorem leafMatch_contact (parameterOutput : HashOutput) (highs : CoordinateHighs) (table : HiddenGraph.Table)
    (cacheF : QueryCache HashSpec) (f : QueryImpl HashSpec Id) (entries : List (HiddenCost.Entry HashInput))
    (hagree : ∀ input, Sum.inl input ∈ entries →
      f input = finalFn (sampleModel parameterOutput highs) table cacheF input)
    (hcached : CachedQueries (sampleModel parameterOutput highs) table cacheF entries)
    (seed : MasterSeed) (hcoord : GraphView.CoordinatesCorrect f (truncateHash parameterOutput) seed table)
    (index : Index) (κ : FTree) (leaf : FLeaf) (secret : Digest)
    (hmatch : Fors.LeafMatch f (truncateHash parameterOutput) index κ seed leaf secret)
    (hmem : Sum.inl (fleafInput (truncateHash parameterOutput) index κ leaf secret) ∈ entries) :
    FContactAt (truncateHash parameterOutput) table cacheF index κ leaf := by
  obtain ⟨hne, heq⟩ := hmatch
  have hcanon : Fors.leafValue f (truncateHash parameterOutput) index κ leaf
      (Completeness.forsSecretValue f (truncateHash parameterOutput) index κ seed leaf) =
        Completeness.forsLeafValue f (truncateHash parameterOutput) index κ seed leaf := by
    rw [Fors.leafValue_canonical, Completeness.forsNodeValue_zero]
  have hne' : secret ≠ table (.fors index κ leaf 0) := by
    rw [(hcoord.2 index κ leaf).1]
    exact hne
  refine ⟨secret, f (fleafInput (truncateHash parameterOutput) index κ leaf secret), hne',
    cached_read parameterOutput highs table cacheF f entries hagree hcached _ hmem
      (fleaf_not_row parameterOutput highs table index κ leaf secret hne'), ?_⟩
  rw [(hcoord.2 index κ leaf).2, ← hcanon, ← heq]
  simp only [fleafInput, Fors.leafValue, forsLeafHash, Completeness.eval_tweakableHash]

/-! ### The refined case analysis -/

attribute [local irreducible] ReferenceChoice.selection encodingAttemptLimit

set_option maxHeartbeats 1000000 in
/-- **Refined case analysis.** For any answer function consistent with the sample and agreeing
with the final cache on the run's queries, an accepted fresh forgery yields a cached first-order
hit, a WOTS event at a retained key, a FORS contact at a revealed leaf, two FORS contacts at one
instance, a near cover, or a cover of a cached, landed, unsigned digest. -/
theorem badA_of_accepted (hb : 0 < keptHeight topLayer) (parameterOutput : HashOutput) (fixed : HiddenGraph.Table)
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
    (hword : ∀ key : OtsKey, PrunedGraph.KeyActive (truncateHash parameterOutput) key.1 key.2.1 key.2.2 →
      ReferenceChoice.word f (truncateHash parameterOutput) key.1 key.2.1 key.2.2
        (SignatureWitness.keyMessageValue f (truncateHash parameterOutput) seed key) = preparedWord results key)
    (hagree : ∀ input, Sum.inl input ∈ entries →
      f input = finalFn (sampleModel parameterOutput highs) table cacheF input)
    (hcached : CachedQueries (sampleModel parameterOutput highs) table cacheF entries)
    (known : HiddenReveal.Knowledge Coordinate)
    (hknown : ∀ c v, known c = some v → knownOf (truncateHash parameterOutput) fixed c = some v ∨
      AboveWord (truncateHash parameterOutput) results c)
    (hguess : NoHiddenGuess (sampleModel parameterOutput highs) table known reveals entries)
    (forgery : Forgery) (log : QueryLog SigningSpec)
    (htrace : ∀ input ∈ SignatureWitness.trace f ⟨(sampleData parameterOutput fixed highs remaining).root,
      truncateHash parameterOutput⟩ forgery.message forgery.signature, Sum.inl input ∈ entries)
    (hgood : LogGood f (truncateHash parameterOutput) seed (sampleData parameterOutput fixed highs remaining steps)
      log reveals)
    (hsigned : SignedRevealed f (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps)
      log reveals)
    (hverify : evalWithAnswerFn f (Concrete.verify ⟨(sampleData parameterOutput fixed highs remaining).root,
      truncateHash parameterOutput⟩ forgery.message forgery.signature : OracleComp HashSpec Bool) = true)
    (hvalid : SigningTranscript.Valid log) (hnotContains : ¬SigningTranscript.Contains log forgery) :
    badA parameterOutput fixed highs remaining results table
      (((some (forgery, log, true), reveals), entries), cacheF) := by
  -- first-order hits
  have hfirstFull : ∀ input ∈ SignatureWitness.trace f ⟨(sampleData parameterOutput fixed highs remaining).root,
      truncateHash parameterOutput⟩ forgery.message forgery.signature,
      truncateHash (f input) ∈ targets (truncateHash parameterOutput)
        (fullTable f (truncateHash parameterOutput) seed
          (labelsOf (materialT parameterOutput fixed highs remaining table)
            (answersT parameterOutput fixed highs remaining table))) input →
      ¬SecondOrderInput (truncateHash parameterOutput) results input →
      badA parameterOutput fixed highs remaining results table
        (((some (forgery, log, true), reveals), entries), cacheF) := by
    intro input hinput hmem hnot
    left
    rw [hfull] at hmem
    exact cached_hitA parameterOutput fixed highs remaining table htable results cacheF f entries hagree hcached
      input (htrace input hinput) hmem hnot
  have hfirst : ∀ input ∈ SignatureWitness.trace f ⟨(sampleData parameterOutput fixed highs remaining).root,
      truncateHash parameterOutput⟩ forgery.message forgery.signature,
      truncateHash (f input) ∈ targets (truncateHash parameterOutput)
        (graphTable f (truncateHash parameterOutput) seed
          (labelsOf (materialT parameterOutput fixed highs remaining table)
            (answersT parameterOutput fixed highs remaining table))) input →
      ¬SecondOrderInput (truncateHash parameterOutput) results input →
      badA parameterOutput fixed highs remaining results table
        (((some (forgery, log, true), reveals), entries), cacheF) :=
    fun input hinput hmem => hfirstFull input hinput (graph_targets_subset _ _ _ _ _ hmem)
  -- revealed chain values are at or above the word, so chain queries below it are not guesses
  have hreveals : ∀ key : OtsKey, PrunedGraph.KeyActive (truncateHash parameterOutput) key.1 key.2.1 key.2.2 →
      ∀ (chain : ChainIndex) (position : Digit),
      Coordinate.chain key.1 key.2.1 key.2.2 chain position ∈ reveals →
        (preparedWord results key chain).val ≤ position.val := by
    intro key hactive chain position h
    rw [← hword key hactive]
    exact revealed_chain_word f _ seed _ log reveals hgood hdata key.1 key.2.1 key.2.2 hactive chain position h
  have hbelow : ∀ key : OtsKey, PrunedGraph.KeyActive (truncateHash parameterOutput) key.1 key.2.1 key.2.2 →
      ∀ (chain : ChainIndex) (step : ChainStep) (payload : Digest),
      step.val < (preparedWord results key chain).val →
      Sum.inl (chainInput (truncateHash parameterOutput) key chain step payload) ∈ entries →
      payload ≠ table (.chain key.1 key.2.1 key.2.2 chain ⟨step.val, by have := step.isLt; omega⟩) ∧
      cacheF (chainInput (truncateHash parameterOutput) key chain step payload) =
        some (f (chainInput (truncateHash parameterOutput) key chain step payload)) := by
    intro key hactive chain step payload hlt hmem
    have hne := chain_below_ne parameterOutput fixed highs results known hknown table reveals entries hguess
      key hactive (hreveals key hactive) chain step payload hlt hmem
    exact ⟨hne, cached_read parameterOutput highs table cacheF f entries hagree hcached _ hmem
      (chain_not_row parameterOutput highs table key hactive chain step payload hne)⟩
  set pk : PublicKey := ⟨(sampleData parameterOutput fixed highs remaining).root,
    truncateHash parameterOutput⟩ with hpk
  rcases SignatureWitness.accepted_recovered_classification f pk seed forgery.message forgery.signature hb
      hdata.root hverify with
    ⟨counter, hchosen, hrec⟩ | ⟨j, -, htree⟩ | ⟨hland, lay, hwots⟩
  · -- the FORS part recovers the canonical key
    set digest := verificationDigest f pk forgery.message forgery.signature with hdigestDef
    set index := SignatureWitness.index f pk forgery.message forgery.signature with hindex
    set leaves := digestLeaves digest with hleavesDef
    have hindex' : index = digestIndex digest := rfl
    have hleafMem : ∀ κ, Sum.inl (fleafInput (truncateHash parameterOutput) index κ (leaves κ)
        (forgery.signature.fors κ).secret) ∈ entries := fun κ =>
      htrace _ (SignatureWitness.verification_fors_run f pk forgery.message forgery.signature _
        (Fors.leafInput_mem f _ index leaves forgery.signature.fors κ))
    have hcov : ∀ κ, Coordinate.fors index κ (leaves κ) 0 ∈ reveals →
        TreeCov (revealedSet reveals) (fullDigestView digest) κ := by
      intro κ h
      simp only [TreeCov, fullDigestView, revealedSet, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hindex', ← hleavesDef]
      exact h
    rcases hrec.fors_classification with hN | hall
    · obtain ⟨input, hinput, hmem, hnot⟩ := nodeException_hitA f (truncateHash parameterOutput) seed _ hcons
        index leaves forgery.signature.fors hN
      exact hfirst input (SignatureWitness.verification_fors_run f pk _ _ _ hinput) hmem (hnot results)
    -- the contacts of the leaf matches
    have hcontact : ∀ κ, Fors.LeafMatch f (truncateHash parameterOutput) index κ seed (leaves κ)
        (forgery.signature.fors κ).secret →
        FContactAt (truncateHash parameterOutput) table cacheF index κ (leaves κ) :=
      fun κ hm => leafMatch_contact parameterOutput highs table cacheF f entries hagree hcached seed hcoord
        index κ (leaves κ) _ hm (hleafMem κ)
    -- a canonical secret was queried, so it was revealed
    have hcanonRev : ∀ κ, (forgery.signature.fors κ).secret =
        Completeness.forsSecretValue f (truncateHash parameterOutput) index κ seed (leaves κ) →
        Coordinate.fors index κ (leaves κ) 0 ∈ reveals := by
      intro κ hval
      have hm := hleafMem κ
      rw [hval, ← (hcoord.2 index κ (leaves κ)).1] at hm
      exact queried_fleaf_revealedA parameterOutput fixed highs results known hknown table reveals entries
        hguess index κ (leaves κ) hm
    -- a contact at a revealed secret
    by_cases hrc : ∃ κ, Fors.LeafMatch f (truncateHash parameterOutput) index κ seed (leaves κ)
        (forgery.signature.fors κ).secret ∧ Coordinate.fors index κ (leaves κ) 0 ∈ reveals
    · obtain ⟨κ, hm, hrev⟩ := hrc
      exact Or.inr (Or.inr (Or.inl ⟨index, κ, leaves κ, hrev, hcontact κ hm⟩))
    push Not at hrc
    -- a signed pair would be canonical
    by_cases hsignedPair : ∃ entry ∈ log, ∃ honest, entry.2 = some honest ∧ entry.1 = forgery.message ∧
        honest.randomness = forgery.signature.randomness
    · exfalso
      obtain ⟨entry, hentry, honest, hhonest, hmessage, hrandomness⟩ := hsignedPair
      have hrevAll : ∀ κ, Coordinate.fors index κ (leaves κ) 0 ∈ reveals := by
        intro κ
        have h := SignedRevealed.fors_mem f hsigned entry hentry honest hhonest κ 0
        rw [hmessage, hrandomness] at h
        exact h
      have hopen : Fors.Opening f (truncateHash parameterOutput) index seed leaves forgery.signature.fors := by
        intro κ
        refine ⟨?_, (hall κ).1⟩
        rcases (hall κ).2 with hcan | hm
        · exact hcan
        · exact absurd (hrevAll κ) (hrc κ hm)
      obtain ⟨randomness, hlandR, hfinish⟩ := hgood.1 entry hentry honest hhonest
      rw [hmessage] at hlandR hfinish
      have heq := canonical_signed_eq f ⟨seed, truncateHash parameterOutput,
        (sampleData parameterOutput fixed highs remaining).root⟩ forgery.message randomness
        forgery.signature honest hlandR hfinish hrandomness counter hchosen (hrec.canonical hopen)
      apply hnotContains
      exact ⟨entry, hentry, hmessage, by rw [hhonest, heq]⟩
    have hunsigned : ∀ entry ∈ log, ∀ signature, entry.2 = some signature →
        ¬(entry.1 = forgery.message ∧ signature.randomness = forgery.signature.randomness) :=
      fun entry hentry honest hhonest hpair => hsignedPair ⟨entry, hentry, honest, hhonest, hpair.1, hpair.2⟩
    have hdig := cachedDigest_eq parameterOutput highs table cacheF f entries hagree hcached _
      forgery.message forgery.signature htrace
    by_cases htwo : ∃ κ κ', κ ≠ κ' ∧
        Fors.LeafMatch f (truncateHash parameterOutput) index κ seed (leaves κ)
          (forgery.signature.fors κ).secret ∧
        Fors.LeafMatch f (truncateHash parameterOutput) index κ' seed (leaves κ')
          (forgery.signature.fors κ').secret
    · obtain ⟨κ, κ', hne, hm, hm'⟩ := htwo
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨index, κ, leaves κ, κ', leaves κ',
        fun h => hne (congrArg Prod.fst h), hcontact κ hm, hcontact κ' hm'⟩)))
    by_cases hone : ∃ κ, Fors.LeafMatch f (truncateHash parameterOutput) index κ seed (leaves κ)
        (forgery.signature.fors κ).secret
    · obtain ⟨κ, hm⟩ := hone
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨(forgery, log, true), rfl, Or.inl
        ⟨hvalid, _, hdig, hrec.1, hunsigned, κ, hcontact κ hm, fun κ' hne => ?_⟩⟩)))
      rcases (hall κ').2 with hcan | hm'
      · exact hcov κ' (hcanonRev κ' hcan)
      · exact (htwo ⟨κ', κ, hne, hm', hm⟩).elim
    · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨(forgery, log, true), rfl, Or.inr
        ⟨hvalid, _, hdig, hrec.1, hunsigned, fun κ => ?_⟩⟩)))
      rcases (hall κ).2 with hcan | hm
      · exact hcov κ (hcanonRev κ hcan)
      · exact (hone ⟨κ, hm⟩).elim
  · obtain ⟨input, hinput, hmem, hnot⟩ := treeHit_hitA f (truncateHash parameterOutput) seed _ hcons hbound pk rfl
      forgery.message forgery.signature j htree
    exact hfirst input hinput hmem (hnot results)
  · generalize hidx : SignatureWitness.index f pk forgery.message forgery.signature = idx at hland hwots
    have hactive : PrunedGraph.KeyActive (truncateHash parameterOutput) lay (treeIndexAt idx lay)
        (leafIndexAt idx lay) := ⟨_, hland, rfl, rfl⟩
    have hwordK : SignatureWitness.chosenWord f (truncateHash parameterOutput) seed idx lay =
        preparedWord results (lay, treeIndexAt idx lay, leafIndexAt idx lay) := hword (lay, treeIndexAt idx lay, leafIndexAt idx lay) hactive
    unfold SignatureWitness.WotsException at hwots
    have hparam : pk.parameter = truncateHash parameterOutput := rfl
    simp only [hidx, hparam] at hwots
    rcases hwots with henc | hleafMatch | hchain
    · obtain ⟨message, counter, hexempt, hmem, hout⟩ := henc
      have hmsg := labelMessage_eq parameterOutput fixed highs remaining steps table f seed hdata
        (lay, treeIndexAt idx lay, leafIndexAt idx lay) hactive
      obtain ⟨input, hinput, hhit⟩ := encodingMatch_hit f (truncateHash parameterOutput) seed
        (labelsOf (materialT parameterOutput fixed highs remaining table)
          (answersT parameterOutput fixed highs remaining table)) (lay, treeIndexAt idx lay, leafIndexAt idx lay)
        [Wots.encodingInput (truncateHash parameterOutput) lay (treeIndexAt idx lay) (leafIndexAt idx lay)
          message counter]
        (by rw [hmsg]; exact ⟨message, counter, hexempt, List.mem_singleton_self _, hout⟩)
      rw [List.mem_singleton] at hinput
      subst hinput
      exact hfirstFull _ hmem hhit
        (not_secondOrder _ _ _ _ (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h))
    · obtain ⟨endpoints, hne, hmem, hout⟩ := hleafMatch
      obtain ⟨input, hinput, hhit⟩ := leafOutput_hit f (truncateHash parameterOutput) seed _ hcons _ _ _ hactive
        [tweakableHashInput (truncateHash parameterOutput) (.leaf lay (treeIndexAt idx lay) (leafIndexAt idx lay))
          (leafPayload endpoints)]
        ⟨endpoints, hne, List.mem_singleton_self _, hout⟩
      rw [List.mem_singleton] at hinput
      subst hinput
      exact hfirst _ hmem hhit
        (not_secondOrder _ _ _ _ (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h))
    · have hfrontier : ∀ chain, Wots.frontier f (truncateHash parameterOutput) lay (treeIndexAt idx lay)
          (leafIndexAt idx lay) (SignatureWitness.chosenWord f (truncateHash parameterOutput) seed idx lay)
          (Completeness.otsSecret f (truncateHash parameterOutput) lay (treeIndexAt idx lay) (leafIndexAt idx lay)
            seed) chain =
          frontierValue results table (lay, treeIndexAt idx lay, leafIndexAt idx lay) chain := by
        intro chain
        unfold Wots.frontier frontierValue chainValue
        rw [hcoord.1 _ _ _ hactive chain, hwordK]
      have hcontactAt : ∀ chain, Chain.Contact f (truncateHash parameterOutput) lay (treeIndexAt idx lay)
          (leafIndexAt idx lay) chain
          (SignatureWitness.chosenWord f (truncateHash parameterOutput) seed idx lay chain)
          (Wots.frontier f (truncateHash parameterOutput) lay (treeIndexAt idx lay) (leafIndexAt idx lay)
            (SignatureWitness.chosenWord f (truncateHash parameterOutput) seed idx lay)
            (Completeness.otsSecret f (truncateHash parameterOutput) lay (treeIndexAt idx lay) (leafIndexAt idx lay)
              seed) chain)
          (SignatureWitness.trace f pk forgery.message forgery.signature) →
          ContactAt (truncateHash parameterOutput) results table cacheF (lay, treeIndexAt idx lay, leafIndexAt idx lay) chain := by
        rintro chain ⟨step, payload, hstep, hmem, hout⟩
        have hstep' : step.val + 1 = (preparedWord results (lay, treeIndexAt idx lay, leafIndexAt idx lay) chain).val := by
          rw [← hwordK]; exact hstep
        obtain ⟨hne, hc⟩ := hbelow (lay, treeIndexAt idx lay, leafIndexAt idx lay) hactive chain step payload (by omega) (htrace _ hmem)
        exact ⟨step, payload, _, hstep', hne, hc, hout.trans (hfrontier chain)⟩
      rcases hchain with ⟨chain, step, payload, hle, hmem, hhit⟩ |
        ⟨chain, first, second, payload, middle, hfs, hsw, hmem1, hmem2, hmid, hfront⟩ |
        ⟨left, right, hne, hcl, hcr⟩ | ⟨chain, ⟨message, counter, candidate, hmemE, hdecode, hneighbor⟩, hcontact⟩
      · obtain ⟨input, hinput, hhit'⟩ := chainOutput_hit f (truncateHash parameterOutput) seed _ hcons _ _ _ hactive
          [tweakableHashInput (truncateHash parameterOutput)
            (.chain lay (treeIndexAt idx lay) (leafIndexAt idx lay) chain step) (bytesLE 16 payload)]
          ⟨chain, step, payload, List.mem_singleton_self _, hhit⟩
        rw [List.mem_singleton] at hinput
        subst hinput
        have hle' : (preparedWord results (lay, treeIndexAt idx lay, leafIndexAt idx lay) chain).val ≤ step.val := by
          rw [← hwordK]; exact hle
        have hns : ¬SecondOrderInput (truncateHash parameterOutput) results
            (tweakableHashInput (truncateHash parameterOutput)
              (.chain lay (treeIndexAt idx lay) (leafIndexAt idx lay) chain step) (bytesLE 16 payload)) :=
          not_secondOrder_chain _ _ (lay, treeIndexAt idx lay, leafIndexAt idx lay) chain step payload ⟨hactive, hle'⟩
        exact hfirst _ hmem hhit' hns
      · have hsw' : second.val + 1 = (preparedWord results (lay, treeIndexAt idx lay, leafIndexAt idx lay) chain).val := by
          rw [← hwordK]; exact hsw
        obtain ⟨-, hc1⟩ := hbelow (lay, treeIndexAt idx lay, leafIndexAt idx lay) hactive chain first payload (by omega) (htrace _ hmem1)
        obtain ⟨-, hc2⟩ := hbelow (lay, treeIndexAt idx lay, leafIndexAt idx lay) hactive chain second middle (by omega) (htrace _ hmem2)
        have hmid' : truncateHash (f (chainInput (truncateHash parameterOutput) (lay, treeIndexAt idx lay, leafIndexAt idx lay) chain first
          payload)) = middle := hmid
        refine Or.inr (Or.inl ⟨(lay, treeIndexAt idx lay, leafIndexAt idx lay), hactive, Or.inl ⟨chain, first, second, payload,
          f (chainInput (truncateHash parameterOutput) (lay, treeIndexAt idx lay, leafIndexAt idx lay) chain first payload),
          f (chainInput (truncateHash parameterOutput) (lay, treeIndexAt idx lay, leafIndexAt idx lay) chain second middle), hfs, hsw', hc1, ?_,
          hfront.trans (hfrontier chain)⟩⟩)
        rw [hmid']
        exact hc2
      · exact Or.inr (Or.inl ⟨(lay, treeIndexAt idx lay, leafIndexAt idx lay), hactive, Or.inr (Or.inr
          ⟨left, right, hne, hcontactAt left hcl, hcontactAt right hcr⟩)⟩)
      · have hmarker : MarkerAt (truncateHash parameterOutput) results cacheF (lay, treeIndexAt idx lay, leafIndexAt idx lay) chain :=
          ⟨message, counter, _, candidate,
            cached_read parameterOutput highs table cacheF f entries hagree hcached _ (htrace _ hmemE)
              (encoding_not_row parameterOutput highs table lay _ _ message counter),
            hdecode, by rw [← hwordK]; exact hneighbor⟩
        exact Or.inr (Or.inl ⟨(lay, treeIndexAt idx lay, leafIndexAt idx lay), hactive, Or.inr (Or.inl ⟨chain, hcontactAt chain hcontact, hmarker⟩)⟩)

/-! ### The win implication -/

/-- **Refined win implication.** In every non-stopped lazy run of the rich program from
knowledge that contains the fixed knowledge and otherwise only above-word chain values, a
winning outcome yields the refined bad event of the table. -/
theorem win_implies_badA (hb : 0 < keptHeight topLayer) (adversary : Adversary) (q : Nat) (hq : q < 2 ^ 256)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (steps : Message → Randomness)
    (prepared : (OtsKey → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (known : HiddenReveal.Knowledge Coordinate)
    (hknownOf : ∀ c v, knownOf (truncateHash parameterOutput) fixed c = some v → known c = some v)
    (hknown : ∀ c v, known c = some v →
      knownOf (truncateHash parameterOutput) fixed c = some v ∨ AboveWord (truncateHash parameterOutput) prepared.1 c)
    (table : HiddenGraph.Table) (htable : tableExtending known table = table)
    (outcome : Outcome) (reveals : List Coordinate) (entries : List (HiddenCost.Entry HashInput))
    (cacheF : QueryCache HashSpec)
    (hstop : some (((some outcome, reveals), entries), cacheF) ∈ support
      (HiddenOutside.stopped (sampleModel parameterOutput highs) table
        (HiddenCost.erase (HiddenCost.trace (richProgram (Internalize.internalize adversary) q
          (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps))))
        known prepared.2))
    (hwin : outcomeWins outcome = true) :
    badA parameterOutput fixed highs remaining prepared.1 table (((some outcome, reveals), entries), cacheF) := by
  have htable' : tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table := by
    have hag := (ForsPotential.agrees_iff_extending known table).2 htable
    exact (ForsPotential.agrees_iff_extending _ table).1 fun c v hc => hag c v (hknownOf c v hc)
  obtain ⟨hgrow, hrun, hguess⟩ := lazy_support (sampleModel parameterOutput highs) table _
    known prepared.2 cacheF _ entries hstop
  obtain ⟨-, hcached⟩ := lazy_cached (sampleModel parameterOutput highs) table _
    known prepared.2 cacheF _ entries hstop
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
  have hagreeAll := sampleFn_final parameterOutput fixed highs remaining table htable' cacheF seed hstruct
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
      (graphCoordinates_T parameterOutput fixed highs remaining table htable')
    unfold Assembly.sampleCoordinates at heq
    rwa [heq] at h
  obtain ⟨hverified, htrace, hgood⟩ := rich_support f' table (Internalize.internalize adversary) q
    (truncateHash parameterOutput) seed (sampleData parameterOutput fixed highs remaining steps) hdata hcoord
    outcome reveals entries hrun'
  have hsigned := rich_revealed f' table (Internalize.internalize adversary) q (truncateHash parameterOutput)
    (sampleData parameterOutput fixed highs remaining steps) outcome reveals entries hrun'
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
  have hword : ∀ key : OtsKey, PrunedGraph.KeyActive (truncateHash parameterOutput) key.1 key.2.1 key.2.2 →
      ReferenceChoice.word f' (truncateHash parameterOutput) key.1 key.2.1 key.2.2
        (SignatureWitness.keyMessageValue f' (truncateHash parameterOutput) seed key) =
      preparedWord prepared.1 key := by
    intro key hactive
    have hmsg : SignatureWitness.keyMessageValue f' (truncateHash parameterOutput) seed key =
        keyMessages (sampleData parameterOutput fixed highs remaining) key :=
      (hdata.keyMessage key.1 key.2.1 key.2.2 hactive).symm
    unfold ReferenceChoice.word preparedWord
    rw [hmsg, hselection key]
  obtain ⟨forgery, log, verified⟩ := outcome
  simp only [outcomeWins, Bool.and_eq_true, decide_eq_true_eq] at hwin
  obtain ⟨⟨hvalid, hnotContains⟩, rfl⟩ := hwin
  exact badA_of_accepted hb parameterOutput fixed highs remaining steps table htable' prepared.1 cacheF reveals entries
    f' seed hcons hbound hdata hcoord hfull hword hagree hcached known hknown hguess forgery log
    htrace hgood hsigned hverified.symm hvalid hnotContains

/-! ### Exposed knowledge -/

section ExposeSupport

variable {ι : Type}
noncomputable local instance exposeSupportDecEq : DecidableEq ι := Classical.decEq _

/-- Sampling a known coordinate returns its value and keeps the knowledge. -/
theorem randomOracle_run_some (known : HiddenReveal.Knowledge ι) (c : ι) (value : Digest)
    (hc : known c = some value) (r : Digest × HiddenReveal.Knowledge ι)
    (hr : r ∈ support ((randomOracle (spec := ι →ₒ Digest) c).run known)) : r = (value, known) := by
  rw [QueryImpl.withCaching_run_some _ hc, support_pure, Set.mem_singleton_iff] at hr
  exact hr

/-- Sampling an unknown coordinate changes the knowledge only there. -/
theorem randomOracle_run_none (known : HiddenReveal.Knowledge ι) (c : ι) (hc : known c = none)
    (r : Digest × HiddenReveal.Knowledge ι)
    (hr : r ∈ support ((randomOracle (spec := ι →ₒ Digest) c).run known)) :
    ∀ c', c' ≠ c → r.2 c' = known c' := by
  rw [QueryImpl.withCaching_run_none _ hc, support_map] at hr
  obtain ⟨value, _, rfl⟩ := hr
  intro c' hne
  exact QueryCache.cacheQuery_of_ne _ _ hne

/-- Exposing a list of coordinates keeps the base knowledge and adds only listed coordinates. -/
theorem exposeR_known_support (P : ι → Prop) :
    ∀ (cs : List ι) (base known k : HiddenReveal.Knowledge ι),
      (∀ c ∈ cs, P c) →
      (∀ c v, base c = some v → known c = some v) →
      (∀ c v, known c = some v → base c = some v ∨ P c) →
      k ∈ support (exposeR cs known) →
      (∀ c v, base c = some v → k c = some v) ∧ (∀ c v, k c = some v → base c = some v ∨ P c)
  | [], base, known, k, _, h1, h2, hk => by
      rw [exposeR, support_pure, Set.mem_singleton_iff] at hk
      subst hk
      exact ⟨h1, h2⟩
  | c :: cs, base, known, k, hP, h1, h2, hk => by
      rw [exposeR, mem_support_bind_iff] at hk
      obtain ⟨r, hr, hk⟩ := hk
      have hrest : ∀ c' ∈ cs, P c' := fun c' hc' => hP c' (List.mem_cons_of_mem _ hc')
      cases hc : known c with
      | none =>
          have hr' := randomOracle_run_none known c hc r hr
          refine exposeR_known_support P cs base r.2 k hrest (fun c' v hv => ?_) (fun c' v hv => ?_) hk
          · have hne : c' ≠ c := by
              rintro rfl
              rw [h1 c' v hv] at hc
              cases hc
            rw [hr' c' hne]
            exact h1 c' v hv
          · by_cases hne : c' = c
            · subst hne
              exact Or.inr (hP c' List.mem_cons_self)
            · rw [hr' c' hne] at hv
              exact h2 c' v hv
      | some value =>
          have hr' := randomOracle_run_some known c value hc r hr
          subst hr'
          exact exposeR_known_support P cs base known k hrest h1 h2 hk

end ExposeSupport

/-- **The above-word exposure satisfies the knowledge hypotheses.** -/
theorem expose_known_support (parameter : PublicParameter) (fixed : HiddenGraph.Table)
    (results : OtsKey → Option (Counter × Encoding)) (k : HiddenReveal.Knowledge Coordinate)
    (hk : k ∈ support (exposeR (aboveList parameter results) (knownOf parameter fixed))) :
    (∀ c v, knownOf parameter fixed c = some v → k c = some v) ∧
      (∀ c v, k c = some v → knownOf parameter fixed c = some v ∨ AboveWord parameter results c) :=
  exposeR_known_support _ _ _ _ k (fun _ hc => mem_aboveList.mp hc) (fun _ _ h => h)
    (fun _ _ h => Or.inl h) hk

end FORS.Security.HiddenBridge
