import Sphincs.BridgeHiddenStop
import Sphincs.SecurityHiddenGraphSampling

/-! The seed-free graph oracle is the candidate hidden-row oracle: canonical WOTS and forest
chain rows read the coordinate table, every other input reads a structural cache over an
independent short-input table. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.HiddenBridge

open Completeness SeedModel Graph Assembly Reduce HiddenGraph Eager

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- WOTS and forest chain steps are the hidden rows; every other position is structural. -/
def IsRowPosition : Position → Prop
  | .chain .. => True
  | .fchain .. => True
  | _ => False

variable [Params]

def structActive (parameter : PublicParameter) (position : Position) : Prop :=
  PrunedGraph.active parameter position ∧ ¬IsRowPosition position

noncomputable def structCache (material : Material) (answers : CanonicalGraphLabels) :
    QueryCache HashSpec :=
  programGraphCache (parameter material) (GraphCorrectness.materialOts material)
    (GraphCorrectness.materialFts material) (graphOrder (structActive (parameter material)))
    (labelsOf material answers) ∅

noncomputable def outsideFn (material : Material) (answers : CanonicalGraphLabels)
    (table : Eager.Table) : HashInput → HashOutput :=
  extend (structCache material answers) table

section Lookup

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : ForestSecrets) (labels : CanonicalGraphLabels)

omit [Params] in
theorem programGraphCache_empty_some (positions : List Position) (position : Position)
    (hmem : position ∈ positions) (bytes : HashInput)
    (heq : bytes = canonicalGraphInput parameter otsSecret ftsSecret position labels) :
    programGraphCache parameter otsSecret ftsSecret positions labels ∅ bytes = some (labels position) := by
  rw [heq]
  exact programGraphCache_label parameter otsSecret ftsSecret labels positions ∅ _ hmem

omit [Params] in
theorem programGraphCache_empty_none (positions : List Position) (bytes : HashInput)
    (hmiss : ∀ position ∈ positions,
      bytes ≠ canonicalGraphInput parameter otsSecret ftsSecret position labels) :
    programGraphCache parameter otsSecret ftsSecret positions labels ∅ bytes = none := by
  rw [programGraphCache_preserves_other parameter otsSecret ftsSecret labels positions ∅ bytes hmiss]
  rfl

end Lookup

/-- The seed-free oracle is the concrete hidden-row oracle. -/
theorem graphFn_eq_answer (material : Material) (answers : CanonicalGraphLabels)
    (table : Eager.Table) :
    graphFn material answers table =
      HiddenGraph.answer (parameter material) (candidateActive (parameter material))
        (graphCoordinates material answers) (highHalves (labelsOf material answers))
        (outsideFn material answers table) := by
  funext bytes
  set p := parameter material
  set ots := GraphCorrectness.materialOts material
  set fts := GraphCorrectness.materialFts material
  set labels := labelsOf material answers
  unfold HiddenGraph.answer
  cases hparse : parse p (candidateActive p) bytes with
  | none =>
      suffices hcache : graphCache material answers bytes = structCache material answers bytes by
        simp only [Option.elim_none, graphFn, outsideFn, extend, hcache]
      simp only [graphCache, structCache]
      by_cases hex : ∃ position ∈ graphOrder (PrunedGraph.active p),
          bytes = canonicalGraphInput p ots fts position labels
      · obtain ⟨position, hmem, heq⟩ := hex
        have hactive := (mem_graphOrder _ _).mp hmem
        by_cases hrow : IsRowPosition position
        · exfalso
          have hrow' : ∃ address : Address, address.position = position := by
            cases position with
            | chain lay tree leaf chainIdx step => exact ⟨.chain lay tree leaf chainIdx step, rfl⟩
            | fchain index c s j a i t => exact ⟨.fchain index c s j a i t, rfl⟩
            | _ => exact hrow.elim
          obtain ⟨address, rfl⟩ := hrow'
          have hp := parse_input p (candidateActive p)
            (address, coordinates ots fts labels address.inputCoordinate) hactive
          rw [coordinates_input, ← heq, hparse] at hp
          cases hp
        · have hstruct : position ∈ graphOrder (structActive p) :=
            (mem_graphOrder _ _).mpr ⟨hactive, hrow⟩
          rw [programGraphCache_empty_some p ots fts labels _ position hmem bytes heq,
            programGraphCache_empty_some p ots fts labels _ position hstruct bytes heq]
      · push Not at hex
        rw [programGraphCache_empty_none p ots fts labels _ bytes hex,
          programGraphCache_empty_none p ots fts labels _ bytes (fun position hmem =>
            hex position ((mem_graphOrder _ _).mpr ((mem_graphOrder _ _).mp hmem).1))]
  | some query =>
      obtain ⟨address, value⟩ := query
      have hq := (parse_some_iff p (candidateActive p) bytes (address, value)).mp hparse
      obtain ⟨rfl, hactive⟩ := hq
      simp only [Option.elim_some]
      have hmem : address.position ∈ graphOrder (PrunedGraph.active p) :=
        (mem_graphOrder _ _).mpr hactive
      split_ifs with hvalue
      · simp only [graphFn, extend, graphCache]
        rw [programGraphCache_row_lookup p ots fts labels _ ∅ address hmem value,
          ite_eq_left (show value = coordinates ots fts labels address.inputCoordinate from hvalue)]
        change labels address.position = Prefix.combine (coordinates ots fts labels address.outputCoordinate)
          (highHalves labels address)
        rw [coordinates_outgoing]
        exact (Prefix.combine_split _).symm
      · simp only [graphFn, outsideFn, extend, graphCache, structCache]
        rw [programGraphCache_row_miss p ots fts labels _ ∅ address value hvalue,
          programGraphCache_row_miss p ots fts labels _ ∅ address value hvalue]

/-! ### Independence of the hidden coordinates -/

/-- Coordinates fixed before the stopped experiment: WOTS chain endpoints, forest chain tops, and
every coordinate at a pruned-away leaf. Only these are read outside the hidden rows. -/
def KnownCoordinate (parameter : PublicParameter) : Coordinate → Prop
  | .chain _ _ leaf _ position => position.val = chainLength - 1 ∨ ¬Landed parameter leaf
  | .fchain _ _ _ _ _ _ position => position.val = chainTop

noncomputable local instance hiddenSampleCellFintype : Fintype SampleCell := sampleCellFintype
noncomputable local instance hiddenSampleCellDecEq : DecidableEq SampleCell := Classical.decEq _

omit [Params] in
theorem coordinateAtCell_of_cell {coordinate : Coordinate} {cell : SampleCell}
    (h : coordinateCell coordinate = cell) : coordinateAtCell cell = some coordinate := by
  rw [← h, coordinateAtCell_cell]

/-- A sample cell all of whose coordinates are known. -/
def CellKnown (parameter : PublicParameter) (cell : SampleCell) : Prop :=
  ∀ coordinate, coordinateCell coordinate = cell → KnownCoordinate parameter coordinate

theorem cellKnown_of_none (parameter : PublicParameter) (cell : SampleCell)
    (h : coordinateAtCell cell = none) : CellKnown parameter cell := by
  intro coordinate hcell
  rw [coordinateAtCell_of_cell hcell] at h
  cases h

theorem cellKnown_struct (parameter : PublicParameter) (position : Position)
    (hrow : ¬IsRowPosition position) : CellKnown parameter (.inr position) := by
  apply cellKnown_of_none
  cases position <;> first | rfl | exact (hrow trivial).elim

theorem cellKnown_last (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) :
    CellKnown parameter (.inr (.chain lay tree leaf chainIdx Position.lastChainStep)) := by
  intro coordinate hcell
  have h := coordinateAtCell_of_cell hcell
  simp only [coordinateAtCell, Option.some.injEq] at h
  subst coordinate
  left
  simp [Position.lastChainStep, chainLength, winternitzBits]

theorem cellKnown_lastForest (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (j : SubIdx) (a : ChildIdx) (i : FChain) :
    CellKnown parameter (.inr (.fchain index c s j a i Position.lastForestStep)) := by
  intro coordinate hcell
  have h := coordinateAtCell_of_cell hcell
  simp only [coordinateAtCell, Option.some.injEq] at h
  subst coordinate
  simp [KnownCoordinate, Position.lastForestStep, chainTop]

theorem cellKnown_surrogate (parameter : PublicParameter) (level : Fin totalHeight) :
    CellKnown parameter (.inl (.inr (.inr level))) :=
  cellKnown_of_none parameter _ rfl

/-- Every child of a structural position has a known cell. -/
theorem cellKnown_children (parameter : PublicParameter) (position : Position)
    (hrow : ¬IsRowPosition position) (child : Position) (hchild : child ∈ position.children) :
    CellKnown parameter (.inr child) := by
  cases position with
  | chain => exact (hrow trivial).elim
  | fchain => exact (hrow trivial).elim
  | leaf lay tree leaf =>
      simp only [Position.children, List.mem_ofFn] at hchild
      obtain ⟨chainIdx, rfl⟩ := hchild
      exact cellKnown_last parameter lay tree leaf chainIdx
  | node lay tree level nodeIdx =>
      simp only [Position.children] at hchild
      split_ifs at hchild <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hchild <;>
        rcases hchild with rfl | rfl <;> exact cellKnown_struct parameter _ (fun h => h)
  | childLeaf index c s j a =>
      simp only [Position.children, List.mem_ofFn] at hchild
      obtain ⟨i, rfl⟩ := hchild
      exact cellKnown_lastForest parameter index c s j a i
  | subNode index c s j level nd =>
      simp only [Position.children] at hchild
      split_ifs at hchild <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hchild <;>
        rcases hchild with rfl | rfl <;> exact cellKnown_struct parameter _ (fun h => h)
  | superChild index c s =>
      simp only [Position.children, List.mem_cons, List.not_mem_nil, or_false] at hchild
      rcases hchild with rfl | rfl | rfl | rfl <;> exact cellKnown_struct parameter _ (fun h => h)
  | topNode index c level nd =>
      simp only [Position.children] at hchild
      split_ifs at hchild <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hchild <;>
        rcases hchild with rfl | rfl <;> exact cellKnown_struct parameter _ (fun h => h)
  | roots index =>
      simp only [Position.children, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hchild
      obtain ⟨c, -, rfl | rfl⟩ := hchild <;> exact cellKnown_struct parameter _ (fun h => h)

section Split

variable (parameterOutput : HashOutput) (highs : CoordinateHighs) (remaining : RemainingOutputs)

noncomputable def splitMaterial (lows : HiddenGraph.Table) : Material :=
  (parameterOutput, joinedSecrets (assemble lows highs remaining))

noncomputable def splitAnswers (lows : HiddenGraph.Table) : CanonicalGraphLabels :=
  joinedLabels (assemble lows highs remaining)

theorem assemble_agree (parameter : PublicParameter) (lows lows' : HiddenGraph.Table)
    (hagree : ∀ coordinate, KnownCoordinate parameter coordinate → lows coordinate = lows' coordinate)
    (cell : SampleCell) (hcell : CellKnown parameter cell) :
    assemble lows highs remaining cell = assemble lows' highs remaining cell := by
  by_cases hrange : ∃ coordinate, coordinateCell coordinate = cell
  · obtain ⟨coordinate, rfl⟩ := hrange
    rw [assemble_coordinate, assemble_coordinate, hagree coordinate (hcell coordinate rfl)]
  · push Not at hrange
    have hout : cell ∉ Set.range coordinateCell := by
      rintro ⟨coordinate, hc⟩
      exact hrange coordinate hc
    exact (assemble_remaining lows highs remaining ⟨cell, hout⟩).trans
      (assemble_remaining lows' highs remaining ⟨cell, hout⟩).symm

omit [Params] in
theorem splitMaterial_parameter (lows : HiddenGraph.Table) :
    parameter (splitMaterial parameterOutput highs remaining lows) = truncateHash parameterOutput := rfl

theorem labelsOf_agree (lows lows' : HiddenGraph.Table)
    (hagree : ∀ coordinate, KnownCoordinate (truncateHash parameterOutput) coordinate →
      lows coordinate = lows' coordinate)
    (position : Position) (hcell : CellKnown (truncateHash parameterOutput) (.inr position)) :
    labelsOf (splitMaterial parameterOutput highs remaining lows)
        (splitAnswers highs remaining lows) position =
      labelsOf (splitMaterial parameterOutput highs remaining lows')
        (splitAnswers highs remaining lows') position := by
  have hsurrogates : GraphCorrectness.materialSurrogates (splitMaterial parameterOutput highs remaining lows) =
      GraphCorrectness.materialSurrogates (splitMaterial parameterOutput highs remaining lows') := by
    funext level
    exact congrArg truncateHash (assemble_agree highs remaining _ lows lows' hagree _
      (cellKnown_surrogate _ level))
  simp only [labelsOf, completedLabels, splitMaterial_parameter, hsurrogates]
  split
  · exact assemble_agree highs remaining _ lows lows' hagree _ hcell
  · exact rfl

end Split

omit [Params] in
theorem programGraphCache_congr (parameter : PublicParameter)
    (otsSecret otsSecret' : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret ftsSecret' : ForestSecrets) (positions : List Position)
    (labels labels' : CanonicalGraphLabels) (cache : QueryCache HashSpec)
    (h : ∀ position ∈ positions,
      canonicalGraphInput parameter otsSecret ftsSecret position labels =
        canonicalGraphInput parameter otsSecret' ftsSecret' position labels' ∧
      labels position = labels' position) :
    programGraphCache parameter otsSecret ftsSecret positions labels cache =
      programGraphCache parameter otsSecret' ftsSecret' positions labels' cache := by
  induction positions generalizing cache with
  | nil => rfl
  | cons first rest ih =>
      obtain ⟨hinput, hlabel⟩ := h first List.mem_cons_self
      change programGraphCache parameter otsSecret ftsSecret rest labels
          (cache.cacheQuery (canonicalGraphInput parameter otsSecret ftsSecret first labels) (labels first)) =
        programGraphCache parameter otsSecret' ftsSecret' rest labels'
          (cache.cacheQuery (canonicalGraphInput parameter otsSecret' ftsSecret' first labels') (labels' first))
      rw [hinput, hlabel]
      exact ih _ (fun position hp => h position (List.mem_cons_of_mem _ hp))

omit [Params] in
theorem canonicalGraphInput_struct (parameter : PublicParameter)
    (otsSecret otsSecret' : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret ftsSecret' : ForestSecrets) (position : Position)
    (labels labels' : CanonicalGraphLabels) (hrow : ¬IsRowPosition position)
    (hchildren : ∀ child ∈ position.children, labels child = labels' child) :
    canonicalGraphInput parameter otsSecret ftsSecret position labels =
      canonicalGraphInput parameter otsSecret' ftsSecret' position labels' := by
  have hmap := List.map_congr_left (f := fun child => truncateHash (labels child))
    (g := fun child => truncateHash (labels' child))
    (fun child hchild => congrArg truncateHash (hchildren child hchild))
  unfold canonicalGraphInput
  congr 2
  cases position with
  | chain => exact (hrow trivial).elim
  | fchain => exact (hrow trivial).elim
  | _ => exact hmap

section Split

variable (parameterOutput : HashOutput) (highs : CoordinateHighs) (remaining : RemainingOutputs)

theorem structCache_agree (lows lows' : HiddenGraph.Table)
    (hagree : ∀ coordinate, KnownCoordinate (truncateHash parameterOutput) coordinate →
      lows coordinate = lows' coordinate) :
    structCache (splitMaterial parameterOutput highs remaining lows) (splitAnswers highs remaining lows) =
      structCache (splitMaterial parameterOutput highs remaining lows') (splitAnswers highs remaining lows') := by
  unfold structCache
  rw [splitMaterial_parameter, splitMaterial_parameter]
  apply programGraphCache_congr
  intro position hmem
  have hrow := ((mem_graphOrder _ _).mp hmem).2
  refine ⟨canonicalGraphInput_struct _ _ _ _ _ _ _ _ hrow fun child hchild => ?_, ?_⟩
  · exact labelsOf_agree parameterOutput highs remaining lows lows' hagree child
      (cellKnown_children _ position hrow child hchild)
  · exact labelsOf_agree parameterOutput highs remaining lows lows' hagree position
      (cellKnown_struct _ position hrow)

omit [Params] in
theorem publicData_congr (labels labels' : CanonicalGraphLabels)
    (h : ∀ position, ¬IsRowPosition position → labels position = labels' position) :
    GraphView.publicData labels = GraphView.publicData labels' := by
  have htree : ∀ lay tree level hlevel index,
      labels (GraphCorrectness.treePosition lay tree level hlevel index) =
        labels' (GraphCorrectness.treePosition lay tree level hlevel index) := by
    intro lay tree level hlevel index
    apply h
    cases level <;> simp [GraphCorrectness.treePosition, IsRowPosition]
  have hsub : ∀ index c s j level hlevel nd,
      labels (GraphCorrectness.subPosition index c s j level hlevel nd) =
        labels' (GraphCorrectness.subPosition index c s j level hlevel nd) := by
    intro index c s j level hlevel nd
    apply h
    cases level <;> simp [GraphCorrectness.subPosition, IsRowPosition]
  have htop : ∀ index c level hlevel nd,
      labels (GraphCorrectness.topPosition index c level hlevel nd) =
        labels' (GraphCorrectness.topPosition index c level hlevel nd) := by
    intro index c level hlevel nd
    apply h
    cases level <;> simp [GraphCorrectness.topPosition, IsRowPosition]
  unfold GraphView.publicData
  congr 1
  · rw [htree]
  · funext index
    rw [h (.roots index) (by simp [IsRowPosition])]
  · funext leaf level
    rw [htree]
  · funext index c s j a level
    rw [hsub]
  · funext index c s level
    rw [htop]

theorem publicData_agree (lows lows' : HiddenGraph.Table)
    (hagree : ∀ coordinate, KnownCoordinate (truncateHash parameterOutput) coordinate →
      lows coordinate = lows' coordinate) :
    GraphView.publicData (labelsOf (splitMaterial parameterOutput highs remaining lows)
      (splitAnswers highs remaining lows)) =
    GraphView.publicData (labelsOf (splitMaterial parameterOutput highs remaining lows')
      (splitAnswers highs remaining lows')) :=
  publicData_congr _ _ fun position hrow =>
    labelsOf_agree parameterOutput highs remaining lows lows' hagree position
      (cellKnown_struct _ position hrow)

theorem highHalves_split (lows : HiddenGraph.Table) (address : Address)
    (hactive : candidateActive (truncateHash parameterOutput) address) :
    highHalves (labelsOf (splitMaterial parameterOutput highs remaining lows)
      (splitAnswers highs remaining lows)) address = highs address.outputCoordinate := by
  unfold labelsOf
  rw [splitMaterial_parameter, completed_row_high _ _ _ address hactive]
  exact highHalves_assemble lows highs remaining address

end Split

omit [Params] in
theorem answer_congr_high (parameter : PublicParameter) (active : Address → Prop)
    (table : HiddenGraph.Table) (high high' : Address → Prefix.High) (outside : HashInput → HashOutput)
    (h : ∀ address, active address → high address = high' address) :
    HiddenGraph.answer parameter active table high outside =
      HiddenGraph.answer parameter active table high' outside := by
  funext bytes
  unfold HiddenGraph.answer
  cases hparse : parse parameter active bytes with
  | none => rfl
  | some query =>
      have hactive := ((parse_some_iff parameter active bytes query).mp hparse).2
      simp only [Option.elim_some, h query.1 hactive]

/-! ### The coordinate table as a completion of the known coordinates -/

/-- Chain coordinates above a pruned-away leaf's secret are masked to zero by preparation. -/
def Masked (parameter : PublicParameter) : Coordinate → Prop
  | .chain _ _ leaf _ position => position.val ≠ 0 ∧ ¬Landed parameter leaf
  | _ => False

theorem known_of_masked (parameter : PublicParameter) (coordinate : Coordinate)
    (h : Masked parameter coordinate) : KnownCoordinate parameter coordinate := by
  cases coordinate with
  | chain lay tree leaf chainIdx position => exact Or.inr h.2
  | fchain => exact h.elim

noncomputable def masked (parameter : PublicParameter) (lows : HiddenGraph.Table) : HiddenGraph.Table :=
  fun coordinate => if Masked parameter coordinate then 0 else lows coordinate

/-- Known coordinates hold the fixed table; all others come from the fresh table. -/
noncomputable def mix (parameter : PublicParameter) (fixed fresh : HiddenGraph.Table) : HiddenGraph.Table :=
  fun coordinate => if KnownCoordinate parameter coordinate then fixed coordinate else fresh coordinate

noncomputable def knownOf (parameter : PublicParameter) (fixed : HiddenGraph.Table) :
    HiddenReveal.Knowledge Coordinate :=
  QueryCache.ofFn fun coordinate => if KnownCoordinate parameter coordinate then some (masked parameter fixed coordinate)
    else none

theorem mix_known (parameter : PublicParameter) (fixed fresh : HiddenGraph.Table) (coordinate : Coordinate)
    (h : KnownCoordinate parameter coordinate) : mix parameter fixed fresh coordinate = fixed coordinate := by
  simp [mix, h]

theorem masked_mix (parameter : PublicParameter) (fixed fresh : HiddenGraph.Table) :
    masked parameter (mix parameter fixed fresh) = tableExtending (knownOf parameter fixed) fresh := by
  funext coordinate
  simp only [masked, mix, tableExtending, knownOf, QueryCache.ofFn_apply]
  by_cases hknown : KnownCoordinate parameter coordinate
  · simp [hknown]
  · have hmask : ¬Masked parameter coordinate := fun h => hknown (known_of_masked _ _ h)
    simp [hknown, hmask]

section Split

variable (parameterOutput : HashOutput) (highs : CoordinateHighs) (remaining : RemainingOutputs)

theorem graphCoordinates_split (lows : HiddenGraph.Table) :
    graphCoordinates (splitMaterial parameterOutput highs remaining lows) (splitAnswers highs remaining lows) =
      masked (truncateHash parameterOutput) lows := by
  funext coordinate
  have hcoord := congrFun (coordinates_assemble lows highs remaining) coordinate
  unfold graphCoordinates masked labelsOf
  rw [splitMaterial_parameter]
  cases coordinate with
  | chain lay tree leaf chainIdx position =>
      by_cases hzero : position.val = 0
      · have hm : ¬Masked (truncateHash parameterOutput) (.chain lay tree leaf chainIdx position) :=
          fun h => h.1 hzero
        rw [ite_eq_right hm, ← hcoord]
        simp only [HiddenGraph.coordinates, dite_eq_left hzero]
        rfl
      · by_cases hland : Landed (truncateHash parameterOutput) leaf
        · have hm : ¬Masked (truncateHash parameterOutput) (.chain lay tree leaf chainIdx position) :=
            fun h => h.2 hland
          rw [ite_eq_right hm, ← hcoord]
          simp only [HiddenGraph.coordinates, dite_eq_right hzero]
          rw [completed_active_label _ _ _ _ hland]
          rfl
        · have hm : Masked (truncateHash parameterOutput) (.chain lay tree leaf chainIdx position) :=
            ⟨hzero, hland⟩
          rw [ite_eq_left hm]
          simp only [HiddenGraph.coordinates, dite_eq_right hzero, completedLabels]
          rw [ite_eq_right (fun hmem => hland ((mem_graphOrder _ _).mp hmem))]
          simp only [PrunedGraph.initialLabels, PrunedGraph.boundary]
          rfl
  | fchain index c s j a i position =>
      rw [ite_eq_right (show ¬Masked (truncateHash parameterOutput) (.fchain index c s j a i position) from
        fun h => h), ← hcoord]
      by_cases hzero : position.val = 0
      · simp only [HiddenGraph.coordinates, dite_eq_left hzero]
        rfl
      · simp only [HiddenGraph.coordinates, dite_eq_right hzero]
        rw [completed_active_label _ _ _ _ trivial]
        rfl

theorem mix_agree (fixed fresh : HiddenGraph.Table) (coordinate : Coordinate)
    (h : KnownCoordinate (truncateHash parameterOutput) coordinate) :
    mix (truncateHash parameterOutput) fixed fresh coordinate = fixed coordinate :=
  mix_known _ fixed fresh coordinate h

/-- The seed-free run at a mixed coordinate table is the hidden-row run whose coordinate
table completes the known coordinates of the fixed table with the fresh table. Nothing else
depends on the fresh table. -/
theorem seedFreeRun_mix (adversary : Adversary) (q : Nat) (fixed fresh : HiddenGraph.Table)
    (table : Eager.Table) :
    seedFreeRun adversary q
        (splitMaterial parameterOutput highs remaining (mix (truncateHash parameterOutput) fixed fresh))
        (splitAnswers highs remaining (mix (truncateHash parameterOutput) fixed fresh)) table =
      Stop.costRun
        (HiddenGraph.answer (truncateHash parameterOutput) (candidateActive (truncateHash parameterOutput))
          (tableExtending (knownOf (truncateHash parameterOutput) fixed) fresh)
          (fun address => highs address.outputCoordinate)
          (outsideFn (splitMaterial parameterOutput highs remaining fixed)
            (splitAnswers highs remaining fixed) table))
        (tableExtending (knownOf (truncateHash parameterOutput) fixed) fresh)
        (HiddenCost.cap (GraphView.costGame (truncateHash parameterOutput)
          (GraphView.publicData (labelsOf (splitMaterial parameterOutput highs remaining fixed)
            (splitAnswers highs remaining fixed))) adversary) q) := by
  have hagree := mix_agree parameterOutput (fixed := fixed) (fresh := fresh)
  unfold seedFreeRun
  rw [graphFn_eq_answer, graphCoordinates_split, masked_mix, splitMaterial_parameter,
    publicData_agree parameterOutput highs remaining _ fixed hagree]
  rw [answer_congr_high _ _ _ _ (fun address => highs address.outputCoordinate) _
    (fun address hactive => highHalves_split parameterOutput highs remaining _ address hactive)]
  unfold outsideFn
  rw [structCache_agree parameterOutput highs remaining _ fixed hagree]

end Split

end Sphincs.Security.HiddenBridge
