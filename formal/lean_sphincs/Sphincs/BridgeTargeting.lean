import Sphincs.BridgeImplication
import Sphincs.BridgeSignerForest
import Sphincs.BridgeInterpSupport

/-! Hit inclusion: the sample's fixed targets, read as a `Targeting` of the saturation potential.
Row addresses (chain steps and FORS leaves) target their output coordinate; every other address
keeps a target that does not depend on the hidden table. Prepared cache entries never hit, so a
cached target hit of the win implication, or a correct recorded guess, is a `Hit` for every
state that keeps the prepared cache and every table that agrees with its exposed coordinates. -/

open OracleComp OracleSpec

namespace Sphincs.Security.HiddenBridge

open Concrete Completeness Graph GraphCorrectness TargetAssignment HiddenGraph Assembly SeedModel Reduce Eager

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

/-! ### Row addresses of tweak fields -/

omit [Params] in
theorem address_position_injective {left right : Address} (h : left.position = right.position) :
    left = right := by
  cases left <;> cases right <;> simp_all [Address.position]

omit [Params] in
theorem address_fields_injective {left right : Address}
    (h : hashDomainFields left.position.domain = hashDomainFields right.position.domain) : left = right :=
  address_position_injective (Position.domain_injective
    (hashFields_injective (Position.domain_inRange _) (Position.domain_inRange _) h))

/-- The row address hashed at these tweak fields, if any. -/
noncomputable def rowAt (fields : TweakFields) : Option Address :=
  if h : ∃ address : Address, hashDomainFields address.position.domain = fields then some h.choose
  else none

omit [Params] in
theorem rowAt_some_iff (fields : TweakFields) (address : Address) :
    rowAt fields = some address ↔ hashDomainFields address.position.domain = fields := by
  unfold rowAt
  split
  · rename_i h
    rw [Option.some.injEq]
    constructor
    · rintro rfl; exact h.choose_spec
    · intro ha; exact address_fields_injective (h.choose_spec.trans ha.symm)
  · rename_i h
    constructor
    · intro heq; cases heq
    · intro ha; exact (h ⟨address, ha⟩).elim

omit [Params] in
theorem rowAt_address (address : Address) :
    rowAt (hashDomainFields address.position.domain) = some address :=
  (rowAt_some_iff _ _).2 rfl

omit [Params] in
theorem not_row_of_rowAt_none (fields : TweakFields) (position : Position)
    (hp : positionAt fields = some position) (hnone : rowAt fields = none) : ¬IsRowPosition position := by
  intro hrow
  have hfields := (positionAt_some_iff fields position).1 hp
  cases position with
  | chain lay tree leaf chainIdx step =>
      have h := rowAt_address (.chain lay tree leaf chainIdx step)
      rw [show (Address.chain lay tree leaf chainIdx step).position = .chain lay tree leaf chainIdx step from rfl,
        hfields, hnone] at h
      cases h
  | fchain index c s j a i t =>
      have h := rowAt_address (.fchain index c s j a i t)
      rw [show (Address.fchain index c s j a i t).position = .fchain index c s j a i t from rfl,
        hfields, hnone] at h
      cases h
  | _ => exact hrow.elim

omit [Params] in
theorem output_ne_input (address : Address) : address.outputCoordinate ≠ address.inputCoordinate := by
  cases address <;> simp [Address.outputCoordinate, Address.inputCoordinate]

/-! ### Message-digest fields carry no target -/

omit [Params] in
theorem msg_fields (parameter : PublicParameter) (input : HashInput) (h : ForestSigner.IsMsgInput input)
    (fields : TweakFields) (hf : parseFields parameter input = some fields) :
    fields = hashDomainFields .message := by
  obtain ⟨parameter', payload, rfl⟩ := h
  obtain ⟨payload', heq⟩ := (parseFields_some_iff _ _ _).1 hf
  exact (fieldInput_injective heq).1.symm

omit [Params] in
theorem rowAt_message : rowAt (hashDomainFields .message) = none := by
  cases h : rowAt (hashDomainFields .message) with
  | none => rfl
  | some address =>
      have hd := hashFields_injective (Position.domain_inRange _) (by trivial) ((rowAt_some_iff _ _).1 h)
      cases address <;> simp [Address.position, Position.domain] at hd

omit [Params] in
theorem positionAt_message : positionAt (hashDomainFields .message) = none := by
  cases h : positionAt (hashDomainFields .message) with
  | none => rfl
  | some position =>
      have hd := hashFields_injective (Position.domain_inRange position) (by trivial)
        ((positionAt_some_iff _ position).mp h)
      cases position <;> simp [Position.domain] at hd

omit [Params] in
theorem encodingAt_message : encodingAt (hashDomainFields .message) = none := by
  unfold encodingAt
  rw [dite_eq_right]
  rintro ⟨leaf, h⟩
  have hd := hashFields_injective (by trivial) (by trivial) h
  cases hd

theorem compTable_message (parameterOutput : HashOutput) (fixed : HiddenGraph.Table)
    (highs : CoordinateHighs) (remaining : RemainingOutputs) (table : HiddenGraph.Table)
    (results : Index → Option (Counter × Encoding)) :
    compTable parameterOutput fixed highs remaining table results (hashDomainFields .message) = none := by
  unfold compTable
  rw [positionAt_message]
  simp only [encTable, encodingAt_message, Option.map_none]

omit [Params] in
theorem parse_msg_none (parameter : PublicParameter) (active : Address → Prop) (input : HashInput)
    (h : ForestSigner.IsMsgInput input) : HiddenGraph.parse parameter active input = none := by
  obtain ⟨parameter', payload, rfl⟩ := h
  cases hparse : HiddenGraph.parse parameter active (tweakableHashInput parameter' .message payload) with
  | none => rfl
  | some query =>
      obtain ⟨heq, -⟩ := (parse_some_iff parameter active _ query).mp hparse
      have hfields := (tweakableInput_injective heq).1
      have hd := hashFields_injective (by trivial) (Position.domain_inRange _) hfields
      cases hq : query.1 <;> simp [hq, Address.position, Position.domain] at hd

/-! ### Non-row targets do not depend on the hidden table -/

section Agree

variable (parameterOutput : HashOutput) (highs : CoordinateHighs) (remaining : RemainingOutputs)

theorem surrogates_agree (lows lows' : HiddenGraph.Table)
    (hagree : ∀ coordinate, KnownCoordinate (truncateHash parameterOutput) coordinate →
      lows coordinate = lows' coordinate) :
    materialSurrogates (splitMaterial parameterOutput highs remaining lows) =
      materialSurrogates (splitMaterial parameterOutput highs remaining lows') := by
  funext level
  exact congrArg truncateHash (assemble_agree highs remaining _ lows lows' hagree _
    (cellKnown_surrogate _ level))

theorem struct_agree (lows lows' : HiddenGraph.Table)
    (hagree : ∀ coordinate, KnownCoordinate (truncateHash parameterOutput) coordinate →
      lows coordinate = lows' coordinate)
    (position : Position) (hrow : ¬IsRowPosition position) :
    canonicalGraphInput (truncateHash parameterOutput)
        (materialOts (splitMaterial parameterOutput highs remaining lows))
        (materialFts (splitMaterial parameterOutput highs remaining lows)) position
        (labelsOf (splitMaterial parameterOutput highs remaining lows) (splitAnswers highs remaining lows)) =
      canonicalGraphInput (truncateHash parameterOutput)
        (materialOts (splitMaterial parameterOutput highs remaining lows'))
        (materialFts (splitMaterial parameterOutput highs remaining lows')) position
        (labelsOf (splitMaterial parameterOutput highs remaining lows') (splitAnswers highs remaining lows')) ∧
    labelsOf (splitMaterial parameterOutput highs remaining lows) (splitAnswers highs remaining lows) position =
      labelsOf (splitMaterial parameterOutput highs remaining lows') (splitAnswers highs remaining lows')
        position := by
  refine ⟨canonicalGraphInput_struct _ _ _ _ _ _ _ _ hrow fun child hchild => ?_, ?_⟩
  · exact labelsOf_agree parameterOutput highs remaining lows lows' hagree child
      (cellKnown_children _ position hrow child hchild)
  · exact labelsOf_agree parameterOutput highs remaining lows lows' hagree position
      (cellKnown_struct _ position hrow)

end Agree

section Targeting

variable (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
  (remaining : RemainingOutputs)

theorem mix_agree_mix (table table' : HiddenGraph.Table) :
    ∀ coordinate, KnownCoordinate (truncateHash parameterOutput) coordinate →
      mix (truncateHash parameterOutput) fixed table coordinate =
        mix (truncateHash parameterOutput) fixed table' coordinate :=
  fun coordinate h => (mix_known _ fixed table coordinate h).trans (mix_known _ fixed table' coordinate h).symm

/-- Away from row addresses, the sample's targets are the same for every hidden table. -/
theorem compTable_nonrow (table table' : HiddenGraph.Table) (results : Index → Option (Counter × Encoding))
    (fields : TweakFields) (hrow : rowAt fields = none) :
    compTable parameterOutput fixed highs remaining table results fields =
      compTable parameterOutput fixed highs remaining table' results fields := by
  have hagree := mix_agree_mix parameterOutput fixed table table'
  unfold compTable
  cases hp : positionAt fields with
  | none => rfl
  | some position =>
      dsimp only
      have hnot := not_row_of_rowAt_none fields position hp hrow
      obtain ⟨hinput, hlabel⟩ := struct_agree parameterOutput highs remaining _ _ hagree position hnot
      have hsur := surrogates_agree parameterOutput highs remaining _ _ hagree
      unfold materialT answersT
      simp only [referenceTable, hp]
      rw [hinput, hlabel, hsur]

/-- The kind of a target at given tweak fields: the output coordinate of a row address, or the
table-independent target of every other address. -/
noncomputable def kindAt (results : Index → Option (Counter × Encoding)) (fields : TweakFields) :
    HiddenDebt.TargetKind Coordinate :=
  (rowAt fields).elim
    ((compTable parameterOutput fixed highs remaining fixed results fields).elim .none
      fun entry => .fixed entry.value)
    fun address => .hidden address.outputCoordinate

/-- The target kind of an input, read from its tweak fields. -/
noncomputable def sampleKind (results : Index → Option (Counter × Encoding)) (input : HashInput) :
    HiddenDebt.TargetKind Coordinate :=
  (parseFields (truncateHash parameterOutput) input).elim .none
    (kindAt parameterOutput fixed highs remaining results)

/-- The targeting of one sample and preparation. -/
noncomputable def sampleTargeting (results : Index → Option (Counter × Encoding)) :
    HiddenDebt.Targeting HashInput HashOutput Coordinate where
  trunc := truncateHash
  kind := sampleKind parameterOutput fixed highs remaining results
  digest := ForestSigner.IsMsgInput

theorem sampleTargeting_kind_eq (results : Index → Option (Counter × Encoding)) :
    (sampleTargeting parameterOutput fixed highs remaining results).kind =
      sampleKind parameterOutput fixed highs remaining results := rfl

theorem sampleTargeting_kind (results : Index → Option (Counter × Encoding)) (input : HashInput)
    (fields : TweakFields) (hf : parseFields (truncateHash parameterOutput) input = some fields) :
    (sampleTargeting parameterOutput fixed highs remaining results).kind input =
      kindAt parameterOutput fixed highs remaining results fields := by
  rw [sampleTargeting_kind_eq]
  unfold sampleKind
  rw [hf]
  exact Option.elim_some _ _ _

theorem kindAt_row (results : Index → Option (Counter × Encoding)) (fields : TweakFields) (address : Address)
    (hr : rowAt fields = some address) :
    kindAt parameterOutput fixed highs remaining results fields = .hidden address.outputCoordinate := by
  unfold kindAt
  rw [hr]
  exact Option.elim_some _ _ _

theorem kindAt_nonrow (results : Index → Option (Counter × Encoding)) (fields : TweakFields)
    (hr : rowAt fields = none) :
    kindAt parameterOutput fixed highs remaining results fields =
      (compTable parameterOutput fixed highs remaining fixed results fields).elim .none
        fun entry => .fixed entry.value := by
  unfold kindAt
  rw [hr]
  exact Option.elim_none _ _

theorem sampleTargeting_msg (results : Index → Option (Counter × Encoding)) (input : HashInput)
    (h : ForestSigner.IsMsgInput input) :
    (sampleTargeting parameterOutput fixed highs remaining results).kind input = .none := by
  cases hf : parseFields (truncateHash parameterOutput) input with
  | none =>
      rw [sampleTargeting_kind_eq]
      unfold sampleKind
      rw [hf]
      exact Option.elim_none _ _
  | some fields =>
      rw [sampleTargeting_kind parameterOutput fixed highs remaining results input fields hf]
      obtain rfl := msg_fields _ input h fields hf
      rw [kindAt_nonrow parameterOutput fixed highs remaining results _ rowAt_message,
        compTable_message]
      exact Option.elim_none _ _

theorem sampleTargeting_compatible (results : Index → Option (Counter × Encoding)) :
    HiddenDebt.Compatible (sampleTargeting parameterOutput fixed highs remaining results)
      (sampleModel parameterOutput highs) where
  row := by
    intro bytes query hparse
    rw [sampleModel_parse] at hparse
    rw [sampleModel_incoming]
    obtain ⟨rfl, -⟩ := (parse_some_iff _ _ bytes query).1 hparse
    have hf : parseFields (truncateHash parameterOutput) (HiddenGraph.input (truncateHash parameterOutput) query) =
        some (hashDomainFields query.1.position.domain) := parseFields_tweakable _ _ _
    rw [sampleTargeting_kind parameterOutput fixed highs remaining results _ _ hf,
      kindAt_row parameterOutput fixed highs remaining results _ query.1 (rowAt_address query.1)]
    intro heq
    exact output_ne_input query.1 (HiddenDebt.TargetKind.hidden.inj heq)
  digestKind := fun bytes h => sampleTargeting_msg parameterOutput fixed highs remaining results bytes h
  digestParse := fun bytes h => by
    rw [sampleModel_parse]
    exact parse_msg_none _ _ bytes h

theorem boundary_row (parameter : PublicParameter) (surrogates : Fin totalHeight → Digest) (address : Address) :
    PrunedGraph.boundary parameter surrogates address.position = none := by
  cases address <;> rfl

/-- Every target of the sample is the fixed target of its kind, or the table value of its hidden
coordinate. -/
theorem target_kind (table : HiddenGraph.Table)
    (htable : tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table)
    (results : Index → Option (Counter × Encoding)) (input : HashInput) (value : Digest)
    (hmem : value ∈ targets (truncateHash parameterOutput)
      (compTable parameterOutput fixed highs remaining table results) input) :
    (sampleTargeting parameterOutput fixed highs remaining results).kind input = .fixed value ∨
      ∃ coordinate, (sampleTargeting parameterOutput fixed highs remaining results).kind input =
        .hidden coordinate ∧ value = table coordinate := by
  unfold targets at hmem
  cases hf : parseFields (truncateHash parameterOutput) input with
  | none =>
      rw [hf] at hmem
      exact absurd hmem (Finset.notMem_empty _)
  | some fields =>
      rw [hf] at hmem
      dsimp only at hmem
      cases he : compTable parameterOutput fixed highs remaining table results fields with
      | none =>
          rw [he] at hmem
          exact absurd hmem (Finset.notMem_empty _)
      | some entry =>
          rw [he] at hmem
          dsimp only at hmem
          have hvalue : value = entry.value := by
            split_ifs at hmem
            · exact absurd hmem (Finset.notMem_empty _)
            · exact Finset.mem_singleton.1 hmem
          subst hvalue
          rw [sampleTargeting_kind parameterOutput fixed highs remaining results input fields hf]
          cases hr : rowAt fields with
          | none =>
              left
              rw [kindAt_nonrow parameterOutput fixed highs remaining results fields hr,
                ← compTable_nonrow parameterOutput fixed highs remaining table fixed results fields hr, he]
              exact Option.elim_some _ _ _
          | some address =>
              right
              refine ⟨address.outputCoordinate, kindAt_row parameterOutput fixed highs remaining results fields
                address hr, ?_⟩
              have hfields := (rowAt_some_iff fields address).1 hr
              subst hfields
              by_cases hactive : PrunedGraph.active (truncateHash parameterOutput) address.position
              · have hentry : compTable parameterOutput fixed highs remaining table results
                    (hashDomainFields address.position.domain) =
                    some ⟨some (canonicalGraphInput (truncateHash parameterOutput)
                        (materialOts (materialT parameterOutput fixed highs remaining table))
                        (materialFts (materialT parameterOutput fixed highs remaining table)) address.position
                        (labelsOf (materialT parameterOutput fixed highs remaining table)
                          (answersT parameterOutput fixed highs remaining table))),
                      truncateHash (labelsOf (materialT parameterOutput fixed highs remaining table)
                        (answersT parameterOutput fixed highs remaining table) address.position)⟩ := by
                  simp only [compTable, (positionAt_some_iff _ address.position).2 rfl]
                  exact referenceTable_active _ _ _ _ _ _ address.position hactive
                rw [hentry, Option.some.injEq] at he
                subst he
                have hc := congrFun (graphCoordinates_T parameterOutput fixed highs remaining table htable)
                  address.outputCoordinate
                unfold graphCoordinates at hc
                rw [coordinates_outgoing] at hc
                exact hc
              · exfalso
                have hnone : compTable parameterOutput fixed highs remaining table results
                    (hashDomainFields address.position.domain) = none := by
                  simp only [compTable, (positionAt_some_iff _ address.position).2 rfl]
                  unfold referenceTable
                  rw [(positionAt_some_iff _ address.position).2 rfl]
                  dsimp only
                  rw [ite_eq_right hactive, boundary_row]
                  exact Option.map_none _
                rw [hnone] at he
                cases he

end Targeting

/-! ### The prepared cache never hits -/

omit [Params] in
theorem queriedInputs_sequenceFin_mem {α : Type} (f : QueryImpl HashSpec Id) :
    ∀ {n : Nat} (computation : Fin n → OracleComp HashSpec α) {input : HashInput},
      input ∈ queriedInputs f (Concrete.sequenceFin computation) →
        ∃ index, input ∈ queriedInputs f (computation index)
  | 0, computation, input, h => by
      rw [Concrete.sequenceFin, queriedInputs_pure] at h
      exact absurd h List.not_mem_nil
  | n + 1, computation, input, h => by
      rw [Concrete.sequenceFin, queriedInputs_bind, List.mem_append] at h
      rcases h with h0 | hrest
      · exact ⟨0, h0⟩
      · rw [queriedInputs_bind, queriedInputs_pure, List.append_nil] at hrest
        obtain ⟨index, hindex⟩ := queriedInputs_sequenceFin_mem f (fun index : Fin n => computation index.succ) hrest
        exact ⟨index.succ, hindex⟩

/-- **Preparation-cache cleanliness.** No prepared entry hits the sample's targets, whatever the
hidden table. -/
theorem prepared_clean (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs)
    (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (table : HiddenGraph.Table) (input : HashInput) (answer : HashOutput)
    (hcache : prepared.2 input = some answer) :
    truncateHash answer ∉ targets (truncateHash parameterOutput)
      (compTable parameterOutput fixed highs remaining table prepared.1) input := by
  obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn prepared.2
  have hsearch := (preparation_support _ _ _ prepared hprepared f hf).2
  rcases Graph.hash_cache_origin _ _ prepared.1 prepared.2 hprepared f hf input answer hcache with
    hstruct | hquery
  · -- a structural canonical input, exempt from its own target
    have hagree : ∀ coordinate, KnownCoordinate (truncateHash parameterOutput) coordinate →
        mix (truncateHash parameterOutput) fixed table coordinate = fixed coordinate :=
      fun coordinate h => mix_known _ fixed table coordinate h
    obtain ⟨position, hmem, rfl⟩ : ∃ position ∈ graphOrder (structActive (truncateHash parameterOutput)),
        input = canonicalGraphInput (truncateHash parameterOutput)
          (materialOts (splitMaterial parameterOutput highs remaining fixed))
          (materialFts (splitMaterial parameterOutput highs remaining fixed)) position
          (labelsOf (splitMaterial parameterOutput highs remaining fixed) (splitAnswers highs remaining fixed)) := by
      by_contra hno
      push Not at hno
      have hnone := programGraphCache_empty_none (truncateHash parameterOutput)
        (materialOts (splitMaterial parameterOutput highs remaining fixed))
        (materialFts (splitMaterial parameterOutput highs remaining fixed))
        (labelsOf (splitMaterial parameterOutput highs remaining fixed) (splitAnswers highs remaining fixed))
        _ input hno
      unfold structCache at hstruct
      rw [splitMaterial_parameter, hnone] at hstruct
      cases hstruct
    obtain ⟨hactive, hrow⟩ := (mem_graphOrder _ _).mp hmem
    obtain ⟨hinput, -⟩ := struct_agree parameterOutput highs remaining _ _ hagree position hrow
    have hentry : compTable parameterOutput fixed highs remaining table prepared.1
        (hashDomainFields position.domain) =
        some ⟨some (canonicalGraphInput (truncateHash parameterOutput)
            (materialOts (materialT parameterOutput fixed highs remaining table))
            (materialFts (materialT parameterOutput fixed highs remaining table)) position
            (labelsOf (materialT parameterOutput fixed highs remaining table)
              (answersT parameterOutput fixed highs remaining table))),
          truncateHash (labelsOf (materialT parameterOutput fixed highs remaining table)
            (answersT parameterOutput fixed highs remaining table) position)⟩ := by
      simp only [compTable, (positionAt_some_iff _ position).2 rfl]
      exact referenceTable_active _ _ _ _ _ _ position hactive
    have hempty : targets (truncateHash parameterOutput)
        (compTable parameterOutput fixed highs remaining table prepared.1)
        (canonicalGraphInput (truncateHash parameterOutput)
          (materialOts (splitMaterial parameterOutput highs remaining fixed))
          (materialFts (splitMaterial parameterOutput highs remaining fixed)) position
          (labelsOf (splitMaterial parameterOutput highs remaining fixed) (splitAnswers highs remaining fixed))) =
        ∅ :=
      canonical_input_excluded _ _ _ (hashDomainFields position.domain) _ ⟨_, rfl⟩ hentry
        (congrArg some hinput)
    rw [hempty]
    exact Finset.notMem_empty _
  · -- an encoding search query: rejected, or the exempt successful trial
    obtain ⟨leaf, hleaf⟩ := queriedInputs_sequenceFin_mem f _ hquery
    have hanswer : f input = answer := hf hcache
    rw [← hanswer]
    refine ReferenceChoice.search_targets_empty_or_miss f _ topLayer rootTree leaf _ _ ?_ input hleaf
    have hsel : ReferenceChoice.selection f (truncateHash parameterOutput) topLayer rootTree leaf
        ((sampleData parameterOutput fixed highs remaining).forestKey leaf) = prepared.1 leaf := hsearch leaf
    unfold compTable
    rw [encoding_positionAt]
    dsimp only
    unfold encTable
    rw [encodingAt_encoding, Option.map_some]
    unfold ReferenceChoice.exemptInput ReferenceChoice.target ReferenceChoice.word
    rw [hsel]

/-! ### Hit inclusion -/

omit [Params] in
theorem hit_of_debt {tg : HiddenDebt.Targeting HashInput HashOutput Coordinate}
    {initial : QueryCache HashSpec} {table : HiddenGraph.Table}
    {state : HiddenDebt.DebtState HashInput HashOutput Coordinate} (hagree : HiddenDebt.Agrees state.known table)
    (coordinate : Coordinate) (h : table coordinate ∈ HiddenDebt.debts tg initial state coordinate) :
    HiddenDebt.Hit tg initial table state := by
  cases hk : state.known coordinate with
  | none => exact Or.inr ⟨coordinate, hk, h⟩
  | some value =>
      have hv : table coordinate = value := hagree coordinate value hk
      exact Or.inl (Or.inr ⟨coordinate, value, hk, hv ▸ h⟩)

/-- **Hit inclusion.** For the sample's targeting, a correct recorded guess or a cached hit of the
sample's fixed targets is a saturation `Hit`, for every state keeping the prepared cache and
agreeing with the table. -/
theorem sampleTargeting_hit (parameterOutput : HashOutput) (fixed : HiddenGraph.Table)
    (highs : CoordinateHighs) (remaining : RemainingOutputs)
    (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (table : HiddenGraph.Table)
    (htable : tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table)
    (s : HiddenDebt.DebtState HashInput HashOutput HiddenGraph.Coordinate)
    (hprep : HiddenDebt.Prepared prepared.2 s) (hagree : HiddenDebt.Agrees s.known table)
    (hbad : HiddenDebt.CorrectGuess table s ∨
      CacheMatch.Bad (targets (truncateHash parameterOutput)
        (compTable parameterOutput fixed highs remaining table prepared.1)) s.cache) :
    HiddenDebt.Hit (sampleTargeting parameterOutput fixed highs remaining prepared.1) prepared.2 table s := by
  rcases hbad with ⟨guess, hguess, hcorrect⟩ | ⟨input, answer, hcache, hmem⟩
  · refine hit_of_debt hagree guess.1 (Or.inl ?_)
    change (guess.1, table guess.1) ∈ s.guesses
    rw [hcorrect]
    exact hguess
  · cases hinit : prepared.2 input with
    | some old =>
        exfalso
        have hsame := hprep input old hinit
        rw [hcache, Option.some.injEq] at hsame
        subst hsame
        exact prepared_clean parameterOutput fixed highs remaining prepared hprepared table input answer hinit hmem
    | none =>
        rcases target_kind parameterOutput fixed highs remaining table htable prepared.1 input _ hmem with
          hfixed | ⟨coordinate, hhidden, hvalue⟩
        · exact Or.inl (Or.inl ⟨input, answer, _, hcache, hinit, hfixed, rfl⟩)
        · exact hit_of_debt hagree coordinate (Or.inr ⟨input, answer, hcache, hinit, hhidden, hvalue⟩)

set_option linter.unusedVariables false in
/-- **A targeting for the saturation bound** that covers the win implication's cached hits: its
kind map is compatible with the sample's row model, message-digest inputs are untargeted digest
queries, and a correct guess or cached target hit is a saturation `Hit`. -/
theorem exists_targeting (hb : 0 < subtreeHeight) (parameterOutput : HashOutput) (fixed : HiddenGraph.Table)
    (highs : CoordinateHighs) (remaining : RemainingOutputs)
    (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining)) :
    ∃ tg : HiddenDebt.Targeting HashInput HashOutput HiddenGraph.Coordinate,
      tg.trunc = truncateHash ∧
      HiddenDebt.Compatible tg (sampleModel parameterOutput highs) ∧
      (∀ x, ForestSigner.IsMsgInput x → tg.kind x = .none ∧ tg.digest x) ∧
      ∀ (table : HiddenGraph.Table),
        tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table →
        ∀ (s : HiddenDebt.DebtState HashInput HashOutput HiddenGraph.Coordinate),
          HiddenDebt.Prepared prepared.2 s → HiddenDebt.Agrees s.known table →
          (HiddenDebt.CorrectGuess table s ∨
            CacheMatch.Bad (targets (truncateHash parameterOutput)
              (compTable parameterOutput fixed highs remaining table prepared.1)) s.cache) →
          HiddenDebt.Hit tg prepared.2 table s :=
  ⟨sampleTargeting parameterOutput fixed highs remaining prepared.1, rfl,
    sampleTargeting_compatible parameterOutput fixed highs remaining prepared.1,
    fun x hx => ⟨sampleTargeting_msg parameterOutput fixed highs remaining prepared.1 x hx, hx⟩,
    fun table htable s hprep hagree hbad =>
      sampleTargeting_hit parameterOutput fixed highs remaining prepared hprepared table htable s hprep hagree hbad⟩

omit [Params] in
/-- Truncating a uniform hash output is uniform, for any targeting comparing by `truncateHash`. -/
theorem uniformTruncation_of_trunc (tg : HiddenDebt.Targeting HashInput HashOutput HiddenGraph.Coordinate)
    (h : tg.trunc = truncateHash) : HiddenDebt.UniformTruncation tg := by
  unfold HiddenDebt.UniformTruncation
  rw [h]
  exact evalDist_truncateHash_uniform

/-! ### Extending knowledge -/

omit [Params] in
theorem tableExtending_of_extends (known known' : HiddenReveal.Knowledge Coordinate)
    (h : ∀ coordinate value, known coordinate = some value → known' coordinate = some value)
    (fresh : HiddenGraph.Table) :
    tableExtending known (tableExtending known' fresh) = tableExtending known' fresh := by
  funext coordinate
  cases hk : known coordinate with
  | none => simp [tableExtending, hk]
  | some value => simp [tableExtending, hk, h coordinate value hk]

end Sphincs.Security.HiddenBridge
