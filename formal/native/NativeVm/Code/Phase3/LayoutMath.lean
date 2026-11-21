module

public import NativeVm.Code.Phase3.LayoutCode
public import NativeVm.Equiv.InsertionSort

/-!
# Phase 3's placements: the arithmetic and the format

* The blocks of a side are, block by block, their owner's height and rows (`sideBlocks_rows`): the
  tables' pushes, pulls and count columns are fixed data (`tables_push`, `tables_pull`,
  `tables_count`), so the owners are `sideOwners side`, as the code's `sideShape` lays them.
* `busLayout fr bs` places the sizes `fr ++ bs.map logRows` one after another, each at the sum of
  `2^size` over the placements before it in `stackOffsets`'s order (`offF`, from the insertion sort's
  facts as phase 1's `stackOffsets_spec`), its depth the `log2Ceil` of the total (`totF`):
  `busLayout_all`.
* `SidesAt`: the format `layoutCode` writes and `selCode` reads.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript LeanVM.Protocol.Verifier
open NativeVm.Equiv (insertionSort_perm pairwise_insertionSort)

/-! ## The blocks -/

theorem tables_push : tables.map (fun t ↦ (t.opcode, t.flushes.push.length)) = shapePP := by
  decide +kernel

theorem tables_pull : tables.map (fun t ↦ (t.opcode, t.flushes.pull.length)) = shapePP := by
  decide +kernel

theorem tables_count : tables.map (fun t ↦ (t.opcode, t.countColumns.length)) = shapeC := by
  simp [Table.countColumns, tables, arithColumns, setColumns, derefColumns, jumpColumns,
    keccakColumns, laneNames, decimalNumeral, List.range_succ, shapeC, opXor, opMul, opSet,
    opDeref, opJump, opKeccak]

/-- A side's blocks' owners, in order. -/
def sideOwners (side : Nat) : List Nat := (sideShape side).flatMap fun p ↦ List.replicate p.2 p.1

theorem flatMap_tables {α : Type} (F : TableW → Array α) (mk : TableW → α → BusBlockW)
    (h r : Array Nat) (hmk : ∀ t c, ((mk t c).logRows, (mk t c).rows) =
      (h.getD t.opcode 0, r.getD t.opcode 0)) :
    (tablesW.flatMap fun t ↦ (F t).map (mk t)).toList.map (fun b ↦ (b.logRows, b.rows)) =
      (tablesW.toList.map fun t ↦ (t.opcode, (F t).size)).flatMap
        fun p ↦ List.replicate p.2 (h.getD p.1 0, r.getD p.1 0) := by
  rw [Array.toList_flatMap, List.map_flatMap, List.flatMap_map]
  congr 1
  funext t
  simp only [Array.toList_map, List.map_map, Function.comp_def, hmk, List.map_const',
    Array.length_toList]

theorem lay_tablesW_toList : tablesW.toList = tables.map TableW.ofTable := by simp [tablesW]

/-- **A side's blocks**: block `k` has its owner's height and rows. -/
theorem sideBlocks_rows {layout : LayoutW} {h r : Array Nat}
    (hb : Model.busBlocks h r = (layout.push, layout.pull, layout.count)) {side : Nat}
    (hs : side < 3) :
    (sideBlocks layout side).toList.map (fun b ↦ (b.logRows, b.rows)) =
      (sideOwners side).map fun t ↦ (h.getD t 0, r.getD t 0) := by
  have h1 : (Model.busBlocks h r).1 = layout.push := congrArg Prod.fst hb
  have h2 : (Model.busBlocks h r).2.1 = layout.pull := congrArg (·.2.1) hb
  have h3 : (Model.busBlocks h r).2.2 = layout.count := congrArg (·.2.2) hb
  unfold Model.busBlocks at h1 h2 h3
  dsimp only at h1 h2 h3
  simp only [sideOwners, List.map_flatMap, List.map_replicate]
  unfold sideBlocks sideShape
  by_cases s0 : side = 0
  · subst s0
    rw [ite_eq_left_of_eq_true _ _ (by decide), ← h1, flatMap_tables _ _ h r (fun _ _ ↦ rfl), lay_tablesW_toList, List.map_map]
    simp only [Function.comp_def, TableW.ofTable, Array.size_map, List.size_toArray]
    rw [tables_push]; rfl
  by_cases s1 : side = 1
  · subst s1
    rw [ite_eq_right_of_eq_false _ _ (by decide), ite_eq_left_of_eq_true _ _ (by decide), ← h2, flatMap_tables _ _ h r (fun _ _ ↦ rfl),
      lay_tablesW_toList, List.map_map]
    simp only [Function.comp_def, TableW.ofTable, Array.size_map, List.size_toArray]
    rw [tables_pull]; rfl
  · obtain rfl : side = 2 := by omega
    rw [ite_eq_right_of_eq_false _ _ (by decide), ite_eq_right_of_eq_false _ _ (by decide), ← h3, flatMap_tables _ _ h r (fun _ _ ↦ rfl), lay_tablesW_toList,
      List.map_map]
    simp only [Function.comp_def, TableW.ofTable, List.size_toArray]
    rw [tables_count]; rfl

theorem sideOwners_length (side : Nat) : (sideOwners side).length = sideNb side := by
  unfold sideOwners sideShape sideNb
  by_cases h : side = 2 <;> simp only [h, ↓reduceIte] <;> decide

theorem sideOwners_lt (side : Nat) : ∀ t ∈ sideOwners side, t < 6 := by
  unfold sideOwners sideShape
  by_cases h : side = 2 <;> simp only [h, ↓reduceIte] <;> decide

theorem sideBlocks_size {layout : LayoutW} {h r : Array Nat}
    (hb : Model.busBlocks h r = (layout.push, layout.pull, layout.count)) {side : Nat}
    (hs : side < 3) : (sideBlocks layout side).size = sideNb side := by
  have := congrArg List.length (sideBlocks_rows hb hs)
  rwa [List.length_map, List.length_map, Array.length_toList, sideOwners_length] at this

/-! ## `stackOffsets` as sums -/

/-- The order of `stackOffsets`: before, by size largest first, ties by index. -/
def ltS (size : Nat → Nat) (i j : Nat) : Bool :=
  decide (size j < size i) || (decide (size i = size j) && decide (i < j))

theorem getD_set! (A : Array Nat) (x v i : Nat) :
    (A.set! x v).getD i 0 = if i = x ∧ x < A.size then v else A.getD i 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds]
  by_cases h1 : i = x
  · subst h1
    by_cases h2 : i < A.size <;> simp [h2]
  · simp [h1, Ne.symm h1]

/-- The layout step of `stackOffsets`. -/
def placeStep (size : Nat → Nat) (acc : Array Nat × Nat) (i : Nat) : Array Nat × Nat :=
  (acc.1.set! i acc.2, acc.2 + 2 ^ size i)

/-- Blocks laid along a strict order: each at the sum of the sizes before it. -/
theorem foldl_place (size : Nat → Nat) (lt : Nat → Nat → Bool) (hirr : ∀ a, lt a a = false)
    (hasym : ∀ a b, lt a b = true → lt b a = false) :
    ∀ (L : List Nat) (A : Array Nat) (s : Nat), L.Pairwise (fun a b ↦ lt a b = true) →
      (∀ x ∈ L, x < A.size) →
      (L.foldl (placeStep size) (A, s)).2 = s + (L.map (2 ^ size ·)).sum ∧
      (L.foldl (placeStep size) (A, s)).1.size = A.size ∧
      ∀ i, (L.foldl (placeStep size) (A, s)).1.getD i 0 =
        if i ∈ L then s + ((L.filter (lt · i)).map (2 ^ size ·)).sum else A.getD i 0
  | [], A, s, _, _ => by simp
  | x :: L, A, s, hp, hlt => by
    rw [List.pairwise_cons] at hp
    have hx : x < A.size := hlt x (by simp)
    obtain ⟨h1, h2, h3⟩ := foldl_place size lt hirr hasym L (A.set! x s) (s + 2 ^ size x) hp.2
      (fun y hy ↦ by simpa using hlt y (by simp [hy]))
    simp only [List.foldl_cons]
    refine ⟨by rw [placeStep, h1]; simp; omega, by rw [placeStep, h2]; simp, fun i ↦ ?_⟩
    rw [placeStep, h3]
    by_cases hi : i ∈ L
    · have hxi := hp.1 i hi
      simp [hi, hxi]
      omega
    · rw [ite_eq_right_iff.mpr (fun h ↦ absurd h hi), getD_set!]
      by_cases hix : i = x
      · subst hix
        have : (L.filter (lt · i)) = [] :=
          List.filter_eq_nil_iff.mpr fun y hy ↦ by simp [hasym _ _ (hp.1 y hy)]
        simp [hx, this, hirr]
      · simp [hix, hi]

theorem ltS_total (size : Nat → Nat) {a b : Nat} (h : a ≠ b) (h' : ltS size b a = false) :
    ltS size a b = true := by
  simp only [ltS, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff,
    Bool.and_eq_false_iff, decide_eq_false_iff_not] at h' ⊢
  omega

/-- The offset of placement `i`: the sizes `2^size` of the placements before it. -/
def offF (S : Array Nat) (i : Nat) : Nat :=
  (((List.range S.size).filter (ltS (S.getD · 0) · i)).map (2 ^ S.getD · 0)).sum

/-- The total size. -/
def totF (S : Array Nat) : Nat := ((List.range S.size).map (2 ^ S.getD · 0)).sum

theorem stackOffsets_sums (sizes : Array Nat) :
    (Model.stackOffsets sizes).2 = log2Ceil (totF sizes) ∧
      (Model.stackOffsets sizes).1.size = sizes.size ∧
      ∀ i < sizes.size, (Model.stackOffsets sizes).1.getD i 0 = offF sizes i := by
  let size := fun i ↦ sizes.getD i 0
  let order := insertionSort (fun i j ↦
    decide (size j < size i) || (decide (size i = size j) && decide (i < j))) (Array.range sizes.size)
  have hperm : order.toList.Perm (List.range sizes.size) := by
    have := insertionSort_perm (fun i j ↦
      decide (size j < size i) || (decide (size i = size j) && decide (i < j))) (Array.range sizes.size)
    rwa [Array.toList_range] at this
  have hpw : order.toList.Pairwise (fun a b ↦ ltS size a b = true) := by
    have hs := pairwise_insertionSort (lt := fun i j ↦
        decide (size j < size i) || (decide (size i = size j) && decide (i < j)))
      (fun a b h ↦ by
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
        simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)
      (fun a b c h1 h2 ↦ by
        simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not] at h1 h2 ⊢
        omega) (Array.range sizes.size)
    have hnd : order.toList.Nodup := hperm.nodup_iff.mpr List.nodup_range
    exact (hs.and hnd).imp fun ⟨h1, h2⟩ ↦ ltS_total size h2 h1
  unfold Model.stackOffsets
  simp only []
  rw [← Array.foldl_toList]
  have hf := foldl_place (sizes.getD · 0) (ltS (sizes.getD · 0))
    (fun a ↦ by simp [ltS]) (fun a b h ↦ by
      simp only [ltS, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [ltS, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)
    _ (Array.replicate sizes.size 0) 0 hpw
    (fun x hx ↦ by simpa using List.mem_range.mp (hperm.mem_iff.mp hx))
  obtain ⟨h1, h2, h3⟩ := hf
  unfold placeStep at h1 h2 h3
  refine ⟨by rw [h1, Nat.zero_add, (hperm.map _).sum_eq]; rfl, by rw [h2, Array.size_replicate],
    fun i hi ↦ ?_⟩
  rw [h3, ite_eq_left_iff.mpr fun h ↦ absurd (hperm.mem_iff.mpr (List.mem_range.mpr hi)) h,
    Nat.zero_add, ((hperm.filter _).map _).sum_eq]
  rfl

/-! ## `busLayout` -/

/-- The sizes a side places: the framework's, then the blocks'. -/
abbrev sizesOf (fr : Array Nat) (bs : Array BusBlockW) : Array Nat := fr ++ bs.map (·.logRows)

/-- **A side's placements**: placement `i` (the framework's, then the tables') has size `S i` and
offset `offF S i`, `S` the framework's sizes then the blocks'; the depth is the `log2Ceil` of the
total. -/
theorem busLayout_all (fr : Array Nat) (bs : Array BusBlockW) :
    (Model.busLayout fr bs).framework.size = fr.size ∧
      (Model.busLayout fr bs).depth = log2Ceil (totF (sizesOf fr bs)) ∧
      (Model.busLayout fr bs).framework ++ (Model.busLayout fr bs).tables =
        (Array.range (sizesOf fr bs).size).map fun i ↦
          ⟨(sizesOf fr bs).getD i 0, offF (sizesOf fr bs) i⟩ := by
  have e : Model.busLayout fr bs =
      let P := Array.zipWith (fun size offset ↦ ({ variableCount := size, index := offset } :
        Placement)) (sizesOf fr bs) (Model.stackOffsets (sizesOf fr bs)).1
      ⟨(Model.stackOffsets (sizesOf fr bs)).2, P.extract 0 fr.size, P.extract fr.size P.size⟩ :=
    (rfl)
  obtain ⟨h1, h2, h3⟩ := stackOffsets_sums (sizesOf fr bs)
  have hfs : fr.size ≤ (sizesOf fr bs).size := by simp
  rw [e]
  generalize sizesOf fr bs = S at h1 h2 h3 hfs ⊢
  generalize Model.stackOffsets S = so at h1 h2 h3
  obtain ⟨offs, d⟩ := so
  simp only at h1 h2 h3 ⊢
  refine ⟨by simp [h2, hfs], h1, ?_⟩
  rw [Array.extract_append_extract]
  apply Array.ext
  · simp [h2]
  · intro i hi hi'
    simp only [Array.size_map, Array.size_range] at hi'
    simp only [Array.getElem_extract, Array.getElem_zipWith, Array.getElem_map, Array.getElem_range]
    rw [← h3 i hi', Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hi', Array.getElem?_eq_getElem (by omega)]
    simp

/-! ## The code's sums -/

/-- The code's key of placement `j`: larger first, ties by index. -/
def keyS (sz : Nat → Nat) (j : Nat) : Nat := sz j * 1024 + 1023 - 2 * j

/-- One step of the code's offset sum. -/
def cStep (sz : Nat → Nat) (kr acc j : Nat) : Nat := if kr < keyS sz j then acc + 2 ^ sz j else acc

/-- The sizes `2^size` of the first `n` placements whose key exceeds `kr`. -/
def cSum (sz : Nat → Nat) (kr n : Nat) : Nat := (List.range n).foldl (cStep sz kr) 0

/-- The sizes `2^size` of the first `n` placements. -/
def tSum (sz : Nat → Nat) (n : Nat) : Nat := (List.range n).foldl (fun acc j ↦ acc + 2 ^ sz j) 0

theorem cSum_succ (sz : Nat → Nat) (kr n : Nat) :
    cSum sz kr (n + 1) = cStep sz kr (cSum sz kr n) n := by
  rw [cSum, cSum, List.range_succ, List.foldl_append]; rfl

theorem tSum_succ (sz : Nat → Nat) (n : Nat) : tSum sz (n + 1) = tSum sz n + 2 ^ sz n := by
  rw [tSum, tSum, List.range_succ, List.foldl_append]; rfl

theorem cSum_le (sz : Nat → Nat) (kr : Nat) : ∀ n, cSum sz kr n ≤ tSum sz n
  | 0 => le_refl _
  | n + 1 => by
    rw [cSum_succ, tSum_succ, cStep]
    have := cSum_le sz kr n
    have := Nat.one_le_two_pow (n := sz n)
    split <;> omega

theorem tSum_le (sz : Nat → Nat) (b : Nat) (hb : ∀ j, sz j ≤ b) : ∀ n, tSum sz n ≤ n * 2 ^ b
  | 0 => by simp [tSum]
  | n + 1 => by
    rw [tSum_succ, Nat.succ_mul]
    have := tSum_le sz b hb n
    have := Nat.pow_le_pow_right (by omega : 0 < 2) (hb n)
    omega

theorem foldl_sum_filter {α : Type} (p : α → Bool) (w : α → Nat) (l : List α) (a : Nat) :
    l.foldl (fun acc x ↦ if p x then acc + w x else acc) a = a + ((l.filter p).map w).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, List.filter_cons]
    split <;> simp; omega

theorem foldl_sum (w : Nat → Nat) (l : List Nat) (a : Nat) :
    l.foldl (fun acc x ↦ acc + w x) a = a + (l.map w).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih]; simp; omega

/-- **The offsets as the code sums them.** -/
theorem offF_eq (S : Array Nat) (hn : S.size ≤ 512) {i : Nat} (hi : i < S.size) :
    offF S i = cSum (S.getD · 0) (keyS (S.getD · 0) i) S.size := by
  rw [cSum, show cStep (S.getD · 0) (keyS (S.getD · 0) i) =
    fun acc j ↦ if decide (keyS (S.getD · 0) i < keyS (S.getD · 0) j) then acc + 2 ^ S.getD j 0
      else acc from by funext acc j; simp [cStep], foldl_sum_filter, Nat.zero_add, offF]
  congr 2
  refine List.filter_congr fun j hj ↦ ?_
  have := List.mem_range.mp hj
  simp only [ltS]
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  unfold keyS
  beta_reduce
  omega

theorem totF_eq (S : Array Nat) : totF S = tSum (S.getD · 0) S.size := by
  rw [tSum, foldl_sum, Nat.zero_add, totF]

/-! ## The format -/

/-- **One side's placements at `p`** (`placeR side`): placement `i` (the framework's, then the
table blocks') its variable count at word `2 i` and its index at word `2 i + 1`, table block `k`'s
rows at word `128 + k`. -/
def SideAt (mem : UInt64 → Option UInt64) (p : UInt64) (L : BusLayoutW) (B : Array BusBlockW) :
    Prop :=
  (L.framework ++ L.tables).size ≤ 64 ∧ B.size ≤ 128 ∧
    (∀ i (h : i < (L.framework ++ L.tables).size),
      NatAt mem (wd p (2 * i)) (L.framework ++ L.tables)[i].variableCount ∧
        NatAt mem (wd p (2 * i + 1)) (L.framework ++ L.tables)[i].index) ∧
    ∀ k (h : k < B.size), NatAt mem (wd p (128 + k)) B[k].rows

/-- **The three sides' placements**, side `side` in `placeR side`. -/
def SidesAt (mem : UInt64 → Option UInt64) (work : UInt64) (layout : LayoutW) : Prop :=
  ∀ side < 3, SideAt mem ((placeR side).at work) (sideLayout layout side) (sideBlocks layout side)

theorem SideAt.congr {mem mem' : UInt64 → Option UInt64} {p : UInt64} {L : BusLayoutW}
    {B : Array BusBlockW} (h : Same mem mem' p 256) (hx : SideAt mem p L B) : SideAt mem' p L B :=
  ⟨hx.1, hx.2.1, fun i hi ↦ ⟨(hx.2.2.1 i hi).1.congr (h _ (by have := hx.1; omega)),
      (hx.2.2.1 i hi).2.congr (h _ (by have := hx.1; omega))⟩,
    fun k hk ↦ (hx.2.2.2 k hk).congr (h _ (by have := hx.2.1; omega))⟩

theorem SidesAt.congr {mem mem' : UInt64 → Option UInt64} {work : UInt64} {layout : LayoutW}
    (h : ∀ side < 3, Same mem mem' ((placeR side).at work) (placeR side).size)
    (hx : SidesAt mem work layout) : SidesAt mem' work layout :=
  fun side hs ↦ (hx side hs).congr (h side hs)

/-! ## A side's sizes -/

/-- A side's framework sizes. -/
def sideFr (layout : LayoutW) (side : Nat) : Array Nat :=
  if side = 2 then #[] else frameworkLogRows layout

theorem sideLayout_eq (layout : LayoutW) (side : Nat) :
    sideLayout layout side = Model.busLayout (sideFr layout side) (sideBlocks layout side) := by
  unfold sideLayout sideFr sideBlocks
  by_cases h : side = 2
  · subst h; rfl
  · simp only [h, ↓reduceIte]

theorem sideFr_size (layout : LayoutW) (side : Nat) : (sideFr layout side).size = sideFw side := by
  unfold sideFr sideFw
  by_cases h : side = 2 <;> simp [h, frameworkLogRows]

/-- **The sizes of a side's selectors.** -/
theorem sideLayout_sizes (layout : LayoutW) (side : Nat) :
    (sideLayout layout side).tables.size = (sideBlocks layout side).size ∧
      (sideLayout layout side).framework.size = (if side = 2 then 0 else 3) := by
  obtain ⟨h1, -, h3⟩ := busLayout_all (sideFr layout side) (sideBlocks layout side)
  have h4 := congrArg Array.size h3
  rw [Array.size_append, Array.size_map, Array.size_range, Array.size_append, Array.size_map,
    h1] at h4
  rw [sideLayout_eq]
  refine ⟨by omega, ?_⟩
  rw [h1, sideFr_size]
  rfl

end NativeVm.Code.P3
