import Whir.PCSBCSSourceFrozenAccessor

/-! Storage validity of the actual source freeze, independently of root honesty,
leaf availability, and padding acceptance. Ghost defaults remain unavailable. -/
set_option autoImplicit false
namespace Whir.PCSBCSSourceFrozenAccessorStructural
open Concrete FiatShamirGame PCSBCSMerkleRootCache PCSBCSMerkleLeafImages
open PCSBCSSourceRootReferences PCSBCSSourceFrozenAccessor
open PublicMerkleLog

private instance : Inhabited ImageCell := ⟨defaultCell 0 0⟩

private theorem forIn_yields {α β : Type} (xs : List α) (b : β)
    (f : α → β → Id (ForInStep β))
    (good : ∀ x ∈ xs, f x b = pure (.yield b)) :
    forIn xs b f = (pure b : Id β) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forIn_cons,good x (by simp)]
    simp only [pure_bind]
    exact ih (fun y hy => good y (by simp [hy]))

private theorem scan_all (xs : List Nat) (p : Nat → Bool) (initial : Bool) :
    (forIn xs initial (fun n valid =>
      if (!p n) = true then pure (.done false) else pure (.yield valid)) : Id Bool) =
      if xs.all p then initial else false := by
  induction xs with
  | nil => rfl
  | cons n xs ih =>
    rw [List.forIn_cons]
    cases hp : p n with
    | false => simp only [hp,Bool.not_false,↓reduceIte,pure_bind,List.all_cons,Bool.false_and]; rfl
    | true =>
      simp only [hp,Bool.not_true,Bool.false_eq_true,↓reduceIte,pure_bind,List.all_cons,Bool.true_and]
      exact ih

private theorem zeroPrefix_iff (n : Nat) (row : List K) (bound : n ≤ row.length) :
    zeroPrefix n row = true ↔ ∀ i < n, row[i]! = 0 := by
  induction n generalizing row with
  | zero => simp [zeroPrefix]
  | succ n ih =>
    cases row with
    | nil => simp at bound
    | cons x xs =>
      have hn : n ≤ xs.length := by simpa using bound
      rw [zeroPrefix,Bool.and_eq_true,beq_iff_eq,ih xs hn]
      constructor
      · rintro ⟨hx,hs⟩ i hi
        cases i with
        | zero => simpa using hx
        | succ i => simpa using hs i (by omega)
      · intro h
        refine ⟨by simpa using h 0 (by omega),?_⟩
        intro i hi
        simpa using h (i+1) (by omega)

/-- The early-break imperative check is exactly the recursive source padding
check, not a supplied padding-validity certificate. -/
theorem padding_loop_eq_zeroPrefix (image : Array K) (padding : Nat)
    (bound : padding ≤ image.size) :
    (forIn [:padding] true (fun n valid =>
      if (image[n]! != 0) = true then pure (.done false) else pure (.yield valid)) : Id Bool) =
      zeroPrefix padding image.toList := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,← List.range_eq_range']
  change (forIn (List.range padding) true (fun n valid =>
    if (!(image[n]! == 0)) = true then pure (.done false) else pure (.yield valid)) : Id Bool) = _
  rw [scan_all]
  change (if (List.range padding).all (fun n => image[n]! == 0) then true else false) = _
  have boolIte (b : Bool) : (if b then true else false) = b := by cases b <;> rfl
  rw [boolIte]
  apply Bool.eq_iff_iff.mpr
  rw [List.all_eq_true,zeroPrefix_iff padding image.toList (by simpa using bound)]
  simp only [List.mem_range,beq_iff_eq]
  have same (i : Nat) (hi : i < padding) : image.toList[i]! = image[i]! := by
    rw [getElem!_pos image.toList i (by simp; omega),getElem!_pos image i (by omega)]
    rfl
  constructor
  · intro h i hi; rw [same i hi]; exact h i hi
  · intro h i hi; rw [← same i hi]; exact h i hi

private theorem cellValid_of_fields (s : Shape) (cell : ImageCell)
    (fits : s.occupied ≤ s.leafWords)
    (imageSize : cell.image.size = s.leafWords)
    (compactSize : cell.compact.size = s.occupied)
    (suffix : ∀ n < s.occupied, cell.compact[n]! = cell.image[s.leafWords-s.occupied+n]!)
    (available : cell.available = true →
      cell.paddingValid = zeroPrefix (s.leafWords-s.occupied) cell.image.toList)
    (missing : cell.available = false → cell.image.all (· == 0) = true ∧
      cell.paddingValid = false) : cellValid s cell = true := by
  unfold cellValid
  have guard : (decide (s.occupied > s.leafWords) || cell.image.size != s.leafWords ||
      cell.compact.size != s.occupied) = false := by simp [show ¬ s.occupied > s.leafWords by omega,imageSize,compactSize]
  rw [guard]
  simp only [Bool.false_eq_true,↓reduceIte]
  have loop : (forIn [:s.occupied] (none, ()) (fun n (_ : Option Bool × Unit) =>
      if (cell.compact[n]! != cell.image[s.leafWords-s.occupied+n]!) = true then
        pure (.done (some false, ())) else pure (.yield (none, ()))) : Id (Option Bool × Unit)) =
      pure (none, ()) := by
    simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
      Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,← List.range_eq_range']
    apply forIn_yields
    intro n hn
    have same := suffix n (List.mem_range.mp hn)
    simp [same]
  rw [loop]
  simp only [pure_bind]
  cases ha : cell.available with
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte]
    change Bool.and (cell.image.all (· == 0)) (Bool.not cell.paddingValid) = true
    simp only [(missing ha).1,(missing ha).2,Bool.not_false,Bool.and_self]
  | true =>
    rw [padding_loop_eq_zeroPrefix cell.image (s.leafWords-s.occupied) (by omega)]
    change (cell.paddingValid == zeroPrefix (s.leafWords-s.occupied) cell.image.toList) = true
    simp only [available ha,beq_self_eq_true]

/-- Defaults have rectangular zero storage but neither availability nor padding
authentication. In particular structural validity does not upgrade their status. -/
theorem defaultCell_valid (s : Shape) (fits : s.occupied ≤ s.leafWords) :
    cellValid s (defaultCell s.leafWords s.occupied) = true := by
  apply cellValid_of_fields s _ fits
  · simp [defaultCell]
  · simp only [defaultCell,Array.size_replicate]
    omega
  · intro n hn
    have compact : s.leafWords-(s.leafWords-s.occupied) = s.occupied := by omega
    simp [defaultCell,compact,getElem!_pos,hn,show s.leafWords-s.occupied+n < s.leafWords by omega]
  · simp [defaultCell]
  · intro _
    refine ⟨?_,rfl⟩
    change (Array.replicate s.leafWords (0 : K)).all (· == 0) = true
    rw [Array.all_eq_true]
    intro n hn
    simp

theorem leafCell_valid (s : Shape) (fits : s.occupied ≤ s.leafWords) (row : List K) :
    cellValid s (leafCell s.leafWords s.occupied row) = true := by
  unfold leafCell
  split
  next width =>
    apply cellValid_of_fields s _ fits
    · simpa using width
    · simp only [List.size_toArray,List.length_drop,width]
      omega
    · intro n hn
      have dropped : n < (row.drop (s.leafWords-s.occupied)).length := by
        simp only [List.length_drop,width]; omega
      have full : s.leafWords-s.occupied+n < row.length := by omega
      rw [getElem!_pos (row.drop (s.leafWords-s.occupied)).toArray n (by simpa using dropped),
        getElem!_pos row.toArray (s.leafWords-s.occupied+n) (by simpa using full)]
      simp only [List.getElem_toArray,List.getElem_drop]
    · simp [fits]
    · simp
  next => exact defaultCell_valid s fits

private theorem cellsSpec_valid (s : Shape) (fits : s.occupied ≤ s.leafWords)
    (height : Nat) (tree : MerkleQueryLogExtraction.Tree) :
    ∀ cell ∈ cellsSpec s.leafWords s.occupied height tree, cellValid s cell = true := by
  induction height generalizing tree with
  | zero =>
    cases tree with
    | absent => simpa [cellsSpec] using defaultCell_valid s fits
    | leaf row => simpa [cellsSpec] using leafCell_valid s fits row
    | branch l r => simpa [cellsSpec] using defaultCell_valid s fits
  | succ h ih =>
    cases tree with
    | absent => simpa [cellsSpec] using defaultCell_valid s fits
    | leaf row => simpa [cellsSpec] using defaultCell_valid s fits
    | branch l r =>
      intro cell member
      rcases List.mem_append.mp member with hl | hr
      · exact ih l cell hl
      · exact ih r cell hr

theorem sourceCells_valid (log : PublicLog) (root : Digest32) (s : Shape)
    (fits : s.occupied ≤ s.leafWords) :
    ∀ cell ∈ (sourceCells log root s.height s.leafWords s.occupied).toList,
      cellValid s cell = true := by
  rw [sourceCells_spec]
  exact cellsSpec_valid s fits s.height _

theorem freeze_raw (log : PublicLog) (root : Digest32) (s : Shape) :
    (freeze log root s).raw = compactTable (freeze log root s).cells := rfl

/-- No height bound, honest-root premise, all-leaf availability, or all-padding
validity is required by these Nat-indexed storage checks. -/
theorem freeze_structurallyValid (log : PublicLog) (ref : Reference)
    (fits : ref.shape.occupied ≤ ref.shape.leafWords) :
    structurallyValid ref (freeze log ref.root ref.shape) = true := by
  change structurallyValid ref
    ⟨ref.shape,log,sourceCells log ref.root ref.shape.height ref.shape.leafWords ref.shape.occupied,
      compactTable (sourceCells log ref.root ref.shape.height ref.shape.leafWords ref.shape.occupied)⟩ = true
  unfold structurallyValid
  dsimp +instances only [sameShape,compactTable]
  simp +instances only [beq_self_eq_true,Bool.true_and,decide_eq_true fits,sourceCells_size,Array.size_map]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,← List.range_eq_range']
  rw [forIn_yields]
  · rfl
  · intro n hn
    have inside : n < (sourceCells log ref.root ref.shape.height ref.shape.leafWords ref.shape.occupied).size := by
      simpa only [sourceCells_size,List.mem_range] using hn
    rw [Array.getElem?_eq_getElem inside]
    have valid := sourceCells_valid log ref.root ref.shape fits
      ((sourceCells log ref.root ref.shape.height ref.shape.leafWords ref.shape.occupied)[n])
      (Array.mem_toList_iff.mpr (Array.getElem_mem inside))
    simp [valid,Array.getElem?_map,Array.getElem?_eq_getElem inside]

theorem lookup_freeze (registry : Captures) (log : PublicLog) (ref : Reference)
    (fits : ref.shape.occupied ≤ ref.shape.leafWords)
    (captured : registry ref = some (freeze log ref.root ref.shape)) :
    lookup registry ref = some (freeze log ref.root ref.shape) := by
  simp [PCSBCSSourceFrozenAccessor.lookup,captured,freeze_structurallyValid log ref fits]

theorem freeze_shape_exact (log : PublicLog) (root : Digest32) (s : Shape)
    (fits : s.occupied ≤ s.leafWords) :
    (freeze log root s).cells.size = 2^s.height ∧
    (freeze log root s).raw.size = (freeze log root s).cells.size ∧
    ∀ row ∈ (freeze log root s).raw.toList, row.size = s.occupied := by
  have shape := PCSBCSMerkleRootCache.freeze_shape log root s fits
  exact ⟨sourceCells_size log root s.height s.leafWords s.occupied,
    by simpa only [freeze,sourceCells_size] using shape.1,shape.2⟩

theorem freeze_raw_eq_source_suffixes (log : PublicLog) (root : Digest32) (s : Shape) :
    (freeze log root s).raw =
      (PCSBCSMerkleQueryLog.rawRoot0 log root s.height s.leafWords).map
        (fun image => (image.toList.drop (s.leafWords-s.occupied)).toArray) :=
  compactTable_eq_drop log root s.height s.leafWords s.occupied

theorem freeze_unfitting_rejects (log : PublicLog) (ref : Reference)
    (unfitting : ¬ ref.shape.occupied ≤ ref.shape.leafWords) :
    structurallyValid ref (freeze log ref.root ref.shape) = false := by
  simp [structurallyValid,unfitting]

theorem defaultCell_status (leafWords occupied : Nat) :
    (defaultCell leafWords occupied).available = false ∧
    (defaultCell leafWords occupied).paddingValid = false := ⟨rfl,rfl⟩

private theorem cellsSpec_unavailable (s : Shape) (height : Nat)
    (tree : MerkleQueryLogExtraction.Tree) :
    ∀ cell ∈ cellsSpec s.leafWords s.occupied height tree,
      cell.available = false → cell = defaultCell s.leafWords s.occupied := by
  induction height generalizing tree with
  | zero =>
    cases tree with
    | absent => simp [cellsSpec]
    | branch l r => simp [cellsSpec]
    | leaf row =>
      intro cell member unavailable
      simp only [cellsSpec,List.mem_singleton] at member
      subst cell
      unfold leafCell at *
      split at unavailable
      · contradiction
      · rename_i wrongWidth
        simp only [ite_eq_right wrongWidth]
  | succ h ih =>
    cases tree with
    | absent => simp [cellsSpec]
    | leaf row => simp [cellsSpec]
    | branch l r =>
      intro cell member unavailable
      rcases List.mem_append.mp member with hl | hr
      · exact ih l cell hl unavailable
      · exact ih r cell hr unavailable

/-- An absent or malformed reconstructed leaf is the literal default, not an
available zero leaf or an authenticated padding image. -/
theorem freeze_unavailable_default (log : PublicLog) (root : Digest32) (s : Shape)
    (cell : ImageCell) (member : cell ∈ (freeze log root s).cells.toList)
    (unavailable : cell.available = false) :
    cell = defaultCell s.leafWords s.occupied := by
  change cell ∈ (sourceCells log root s.height s.leafWords s.occupied).toList at member
  rw [sourceCells_spec] at member
  exact cellsSpec_unavailable s s.height _ cell member unavailable

private theorem array_mapM_some {α β : Type} (xs : Array α)
    (f : α → Option β) (g : α → β) (same : ∀ x ∈ xs, f x = some (g x)) :
    xs.mapM f = some (xs.map g) := by
  rw [Array.mapM_eq_mapM_toList]
  have listSame : xs.toList.mapM f = some (xs.toList.map g) := by
    have general (ys : List α) (good : ∀ x ∈ ys, f x = some (g x)) :
        ys.mapM f = some (ys.map g) := by
      induction ys with
      | nil => rfl
      | cons x ys ih =>
        simp only [List.mapM_cons,good x (by simp),List.map_cons]
        rw [ih (fun y hy => good y (by simp [hy]))]
        rfl
    exact general xs.toList (fun x hx => same x (Array.mem_toList_iff.mp hx))
  rw [listSame]
  change some (xs.toList.map g).toArray = some (xs.map g)
  congr 1
  apply Array.toList_inj.mp
  simp

open Protocol CausalGame PCSBCSFrozenOracleRows

/-- The only phase codec condition is base phase or a multiple of three live
words for extension limbs. Neither availability nor padding is a codec premise. -/
theorem frozenOracle_freeze (log : PublicLog) (root : Digest32) (s : Shape)
    (fits : s.occupied ≤ s.leafWords) (phase : Nat)
    (codecShape : phase = 0 ∨ s.occupied % 3 = 0) :
    ∃ oracle, frozenOracle phase (freeze log root s) = some oracle ∧
      oracle.size = (freeze log root s).cells.size := by
  by_cases base : phase = 0
  · refine ⟨liftRoot (freeze log root s).raw,by simp [frozenOracle,base],?_⟩
    simpa only [liftRoot,Array.size_map] using (freeze_shape_exact log root s fits).2.1
  · have divisible : s.occupied % 3 = 0 := codecShape.resolve_left base
    let decode := fun words : Array K => Array.ofFn fun i : Fin (words.size/3) =>
      (⟨words[3*i.val]!,words[3*i.val+1]!,words[3*i.val+2]!⟩ : E)
    have decoded : (freeze log root s).raw.mapM extensionRow =
        some ((freeze log root s).raw.map decode) := by
      apply array_mapM_some
      intro row member
      have width := (freeze_shape_exact log root s fits).2.2 row (Array.mem_toList_iff.mpr member)
      simp only [extensionRow,width,divisible,↓reduceIte]
      rfl
    refine ⟨(freeze log root s).raw.map decode,?_,?_⟩
    · simp only [frozenOracle,base,↓reduceIte,extensionOracle,decoded]
    · simpa only [Array.size_map] using (freeze_shape_exact log root s fits).2.1

/-- Once the actual phase codec succeeds, checked selection rejects exactly a
queried available cell whose padding flag is false. Unavailable cells succeed
as ghost data. Bounds and representation are local source geometry, not root
honesty or transport authentication. -/
theorem selectPhase_flags (phase : Nat) (f : Frozen) (qs : Array Nat)
    (oracle : Oracle) (decoded : frozenOracle phase f = some oracle)
    (size : oracle.size = f.cells.size) (bounds : ∀ n ∈ qs, n < f.cells.size) :
    (selectPhase phase f qs).isSome =
      qs.all (fun n => !f.cells[n]!.available || f.cells[n]!.paddingValid) := by
  have rows : queryRows oracle qs = some (qs.map (fun n => oracle[n]!)) := by
    apply array_mapM_some
    intro n hn
    have inside : n < oracle.size := by rw [size]; exact bounds n hn
    simp [Array.getElem?_eq_getElem inside,getElem!_pos oracle n inside]
  have cells : qs.mapM (fun n => f.cells[n]?) = some (qs.map (fun n => f.cells[n]!)) := by
    apply array_mapM_some
    intro n hn
    simp [Array.getElem?_eq_getElem (bounds n hn),getElem!_pos f.cells n (bounds n hn)]
  unfold selectPhase
  rw [decoded]
  dsimp only [Bind.bind,Option.bind]
  rw [rows]
  dsimp only [Bind.bind,Option.bind]
  rw [cells]
  dsimp only [Bind.bind,Option.bind]
  have flags : (qs.map (fun n => f.cells[n]!)).all
      (fun cell => !cell.available || cell.paddingValid) =
      qs.all (fun n => !f.cells[n]!.available || f.cells[n]!.paddingValid) := by
    simp only [← Array.all_toList,Array.toList_map,List.all_map]
    rfl
  rw [flags]
  cases qs.all (fun n => !f.cells[n]!.available || f.cells[n]!.paddingValid) <;> rfl

theorem selectPhase_freeze_flags (log : PublicLog) (root : Digest32) (s : Shape)
    (fits : s.occupied ≤ s.leafWords) (phase : Nat) (codecShape : phase = 0 ∨ s.occupied % 3 = 0)
    (qs : Array Nat) (bounds : ∀ n ∈ qs, n < 2^s.height) :
    (selectPhase phase (freeze log root s) qs).isSome =
      qs.all (fun n => !(freeze log root s).cells[n]!.available ||
        (freeze log root s).cells[n]!.paddingValid) := by
  obtain ⟨oracle,decoded,size⟩ := frozenOracle_freeze log root s fits phase codecShape
  apply selectPhase_flags phase _ qs oracle decoded size
  simpa only [freeze,sourceCells_size] using bounds

theorem selectPhase_freeze_success_iff (log : PublicLog) (root : Digest32) (s : Shape)
    (fits : s.occupied ≤ s.leafWords) (phase : Nat) (codecShape : phase = 0 ∨ s.occupied % 3 = 0)
    (qs : Array Nat) (bounds : ∀ n ∈ qs, n < 2^s.height) :
    (selectPhase phase (freeze log root s) qs).isSome = true ↔
      ∀ n ∈ qs, (freeze log root s).cells[n]!.available = true →
        (freeze log root s).cells[n]!.paddingValid = true := by
  rw [selectPhase_freeze_flags log root s fits phase codecShape qs bounds,Array.all_eq_true']
  constructor
  · intro h n hn available
    have flag := h n hn
    simpa only [available,Bool.not_true,Bool.false_or] using flag
  · intro h n hn
    cases available : (freeze log root s).cells[n]!.available with
    | false => simp only [Bool.not_false,Bool.true_or]
    | true => simp only [Bool.not_true,Bool.false_or,h n hn available]

theorem selectPhase_freeze_reject_iff (log : PublicLog) (root : Digest32) (s : Shape)
    (fits : s.occupied ≤ s.leafWords) (phase : Nat) (codecShape : phase = 0 ∨ s.occupied % 3 = 0)
    (qs : Array Nat) (bounds : ∀ n ∈ qs, n < 2^s.height) :
    selectPhase phase (freeze log root s) qs = none ↔
      ∃ n ∈ qs, (freeze log root s).cells[n]!.available = true ∧
        (freeze log root s).cells[n]!.paddingValid = false := by
  rw [← Option.isNone_iff_eq_none,← Option.isSome_eq_false_iff,
    selectPhase_freeze_flags log root s fits phase codecShape qs bounds,
    Array.all_eq_false']
  simp

#print axioms padding_loop_eq_zeroPrefix
#print axioms defaultCell_valid
#print axioms leafCell_valid
#print axioms freeze_structurallyValid
#print axioms lookup_freeze
#print axioms freeze_unavailable_default
#print axioms frozenOracle_freeze
#print axioms selectPhase_freeze_success_iff
#print axioms selectPhase_freeze_reject_iff
end Whir.PCSBCSSourceFrozenAccessorStructural
