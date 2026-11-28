module

public import NativeVm.Equiv.LayoutBuild

/-!
# Phase 1's arithmetic: the layout as the code computes it

The code computes `buildLayout`'s placements column by column, without sorting: a block's offset
in the stack is the total size of the blocks `stackOffsets` puts before it. This module proves the
model's `placementsOf` equal to that (`placementsOf_getD`, `placementsOf_snd`):

* `stackOffsets` lays the blocks along a strict order (largest first, ties by index), so a block's
  offset is the sum of `2^size` over the blocks before it in that order (`stackOffsets_getD`), and
  the total the sum over all (`stackOffsets_snd`);
* the stacked blocks are the global columns `isBlockF` says (`blockCols_toList`, the tabulated
  `keccakSlot` and output lanes read as `slotF`, `outF`), and the order on them compares the key
  `κ · 256 + (255 - c)`, larger first (`keyF`), so the offset of column `c` is `sumF κ (keyF κ c)`,
  the sum of `2^κ` over the block columns of larger key, and the total `sumF κ 0`;
* each column's log-size is `kapF` of the announced sizes (`columnKappas_getD`).

`tailP` is `readAnnouncedSizes` after its scalars are read, as one `Option` (`readAnnouncedSizes_run`).
-/

@[expose] public section

namespace NativeVm.Math.Layout

open NativeVm.Model NativeVm.Equiv LeanVM.Parameters LeanVM.Protocol.Verifier

/-! ## The columns -/

/-- A stacked global column: not a `q_keccak` slot, not a `KECCAK` output lane. -/
def isBlockF (c : Nat) : Bool := decide (c < 66) || decide (c = 80) || decide (131 ≤ c)

/-- A global column's `q_keccak` slot. -/
def slotF (c : Nat) : Option Nat :=
  if 66 ≤ c ∧ c < 80 then some (c - 16) else if 81 ≤ c ∧ c < 106 then some (c - 81) else none

/-- A `KECCAK` output lane's column. -/
def outF (c : Nat) : Bool := decide (106 ≤ c ∧ c < 131)

theorem keccakSlot_eq : ∀ c < 158, keccakSlot c = slotF c := by decide +kernel

theorem keccakOutput_eq : ∀ c < 158, decide (c ∈ keccakOutputColumns) = outF c := by
  decide +kernel

theorem isBlockF_eq : ∀ c < 158, isBlockF c = ((slotF c).isNone && !outF c) := by decide

/-! ## Sums -/

/-- The sort key: larger first. -/
def keyF (κ : Nat → Nat) (c : Nat) : Nat := κ c * 256 + (255 - c)

/-- One column of `sumF`. -/
def sumStep (κ : Nat → Nat) (kr acc c : Nat) : Nat :=
  if isBlockF c && decide (kr < keyF κ c) then acc + 2 ^ κ c else acc

/-- The sizes `2^κ` of the block columns whose key exceeds `kr`. -/
def sumF (κ : Nat → Nat) (kr : Nat) : Nat := (List.range 158).foldl (sumStep κ kr) 0

theorem foldl_sum_filter {α : Type} (p : α → Bool) (w : α → Nat) (l : List α) (a : Nat) :
    l.foldl (fun acc x ↦ if p x then acc + w x else acc) a = a + ((l.filter p).map w).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, List.filter_cons]
    split <;> simp; omega

theorem sumF_eq (κ : Nat → Nat) (kr : Nat) :
    sumF κ kr = ((((List.range 158).filter isBlockF).filter (fun c ↦ decide (kr < keyF κ c))).map
      (fun c ↦ 2 ^ κ c)).sum := by
  rw [sumF, List.filter_filter]
  have := foldl_sum_filter (fun c ↦ decide (kr < keyF κ c) && isBlockF c) (fun c ↦ 2 ^ κ c)
    (List.range 158) 0
  rw [Nat.zero_add] at this
  rw [← this]
  congr 1
  funext acc c
  simp only [sumStep, Bool.and_comm]

/-! ## `stackOffsets` as sums -/

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

/-- **Blocks laid along a strict order**: each at the sum of the sizes before it. -/
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

/-- The order of `stackOffsets`: before, by size largest first, ties by index. -/
def ltS (size : Nat → Nat) (i j : Nat) : Bool :=
  decide (size j < size i) || (decide (size i = size j) && decide (i < j))

theorem ltS_total (size : Nat → Nat) {a b : Nat} (h : a ≠ b) (h' : ltS size b a = false) :
    ltS size a b = true := by
  simp only [ltS, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_false_iff,
    Bool.and_eq_false_iff, decide_eq_false_iff_not] at h' ⊢
  omega

/-- The order `stackOffsets` lays the blocks along, and what it is. -/
theorem stackOffsets_order (sizes : Array Nat) :
    let size := fun i ↦ sizes.getD i 0
    let order := insertionSort (fun i j ↦
      decide (size j < size i) || (decide (size i = size j) && decide (i < j))) (Array.range sizes.size)
    order.toList.Perm (List.range sizes.size) ∧
      order.toList.Pairwise (fun a b ↦ ltS size a b = true) := by
  intro size order
  have hperm : order.toList.Perm (List.range sizes.size) := by
    have := insertionSort_perm (fun i j ↦
      decide (size j < size i) || (decide (size i = size j) && decide (i < j))) (Array.range sizes.size)
    rwa [Array.toList_range] at this
  refine ⟨hperm, ?_⟩
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

theorem stackOffsets_spec (sizes : Array Nat) :
    (Model.stackOffsets sizes).2 = log2Ceil ((List.range sizes.size).map (2 ^ sizes.getD · 0)).sum ∧
      (Model.stackOffsets sizes).1.size = sizes.size ∧
      ∀ i < sizes.size, (Model.stackOffsets sizes).1.getD i 0 =
        (((List.range sizes.size).filter (ltS (sizes.getD · 0) · i)).map
          (2 ^ sizes.getD · 0)).sum := by
  obtain ⟨hperm, hpw⟩ := stackOffsets_order sizes
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
  refine ⟨by rw [h1, Nat.zero_add, (hperm.map _).sum_eq], by rw [h2, Array.size_replicate],
    fun i hi ↦ ?_⟩
  rw [h3, ite_eq_left_iff.mpr fun h ↦ absurd (hperm.mem_iff.mpr (List.mem_range.mpr hi)) h,
    Nat.zero_add, ((hperm.filter _).map _).sum_eq]

/-! ## `placementsOf` column by column -/

theorem columnCount_158 : columnCount = 158 := by decide

/-- The block columns, in order. -/
def blockList : List Nat := (List.range 158).filter isBlockF

theorem blockList_pairwise : blockList.Pairwise (· < ·) := List.pairwise_lt_range.filter _

theorem lt_of_mem_blockList {c : Nat} (h : c ∈ blockList) : c < 158 :=
  List.mem_range.mp (List.mem_filter.mp h).1

/-- The model's block columns are `blockList`. -/
theorem blockCols_toList (n : Nat) (hn : n = 158) :
    ((Array.range n).filter fun c ↦ ((keccakSlotTable[c]?).getD none).isNone &&
      !((keccakOutputTable[c]?).getD false)).toList = blockList := by
  subst hn
  rw [Array.toList_filter, Array.toList_range, blockList]
  refine List.filter_congr fun c hc ↦ ?_
  have hc' : c < 158 := List.mem_range.mp hc
  have hcc : c < columnCount := by rw [columnCount_158]; exact hc'
  rw [keccakSlotTable_get hcc, keccakOutputTable_get hcc, keccakSlot_eq c hc',
    keccakOutput_eq c hc', isBlockF_eq c hc']

theorem list_eq_map_range (l : List Nat) : l = (List.range l.length).map (l.getD · 0) := by
  refine List.ext_getElem (by simp) fun i h1 h2 ↦ ?_
  simp [List.getD_eq_getElem?_getD, h1]

/-- The sums over the blocks before block `p`, by position, are the sums over the block columns of
larger key. -/
theorem sum_before (κ : Nat → Nat) (sizes : Array Nat) (hsz : sizes.size = blockList.length)
    (hs : ∀ q < blockList.length, sizes.getD q 0 = κ (blockList.getD q 0)) {p : Nat}
    (hp : p < blockList.length) :
    (((List.range sizes.size).filter (ltS (sizes.getD · 0) · p)).map (2 ^ sizes.getD · 0)).sum =
      sumF κ (keyF κ (blockList.getD p 0)) := by
  have hpw := List.pairwise_iff_getElem.mp blockList_pairwise
  have hbd : ∀ q < blockList.length, blockList.getD q 0 < 158 := fun q hq ↦ by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, Option.getD_some]
    exact lt_of_mem_blockList (List.getElem_mem hq)
  have hmono : ∀ q < blockList.length, (q < p ↔ blockList.getD q 0 < blockList.getD p 0) := by
    intro q hq
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq,
      List.getElem?_eq_getElem hp, Option.getD_some]
    constructor
    · exact hpw q p hq hp
    · intro h
      rcases Nat.lt_trichotomy q p with h' | rfl | h'
      · exact h'
      · omega
      · have := hpw p q hp hq h'; omega
  rw [sumF_eq, ← blockList]
  generalize hkr : keyF κ (blockList.getD p 0) = kr
  rw [list_eq_map_range blockList, List.filter_map, List.map_map, hsz]
  subst hkr
  have hq := fun q (h : q ∈ List.range blockList.length) ↦ List.mem_range.mp h
  rw [List.filter_congr (fun q h ↦ ?_)]
  · refine congrArg List.sum (List.map_congr_left fun q h ↦ ?_)
    simp only [Function.comp_apply]
    rw [hs q (hq q (List.mem_filter.mp h).1)]
  · have h1 := hq q h
    have h2 := hmono q h1
    have h3 := hbd q h1
    have h4 := hbd p hp
    have h5 := h2.1
    have h6 := h2.2
    simp only [Function.comp_apply, ltS, hs q h1, hs p hp, keyF]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨fun h ↦ decide_eq_true (by omega), fun h ↦ by have := of_decide_eq_true h; omega⟩

theorem sum_all (κ : Nat → Nat) (sizes : Array Nat) (hsz : sizes.size = blockList.length)
    (hs : ∀ q < blockList.length, sizes.getD q 0 = κ (blockList.getD q 0)) :
    ((List.range sizes.size).map (2 ^ sizes.getD · 0)).sum = sumF κ 0 := by
  rw [sumF_eq, ← blockList, List.filter_eq_self.mpr fun c hc ↦ by
    have := lt_of_mem_blockList hc; simp [keyF]; omega]
  conv_rhs => rw [list_eq_map_range blockList]
  rw [List.map_map, hsz]
  exact congrArg List.sum (List.map_congr_left fun q h ↦ by
    simp only [Function.comp_apply]; rw [hs q (List.mem_range.mp h)])

/-- A column's placement, as the code lays it: a `q_keccak` slot inside `q_keccak`'s block, an
output lane nowhere, a block column at the sizes of the blocks of larger key. -/
def plF (κ : Nat → Nat) (c : Nat) : Option Placement :=
  match slotF c with
  | some s => some ⟨κ c, sumF κ (keyF κ 4) + s * 2 ^ κ c⟩
  | none => if outF c then none else some ⟨κ c, sumF κ (keyF κ c)⟩

theorem mem_blockList {c : Nat} (hc : c < 158) (h : (slotF c).isNone = true) (h' : outF c = false) :
    c ∈ blockList :=
  List.mem_filter.mpr ⟨List.mem_range.mpr hc, by rw [isBlockF_eq c hc, h, h']; rfl⟩

/-- **`placementsOf`, column by column.** -/
theorem placementsOf_spec (kappas : Array Nat) (hk : kappas.size = 158) :
    (Model.placementsOf kappas).2 = max Whir.minLogStack (log2Ceil (sumF (kappas.getD · 0) 0)) ∧
      (Model.placementsOf kappas).1.size = 158 ∧
      ∀ c < 158, (Model.placementsOf kappas).1.getD c none = plF (kappas.getD · 0) c := by
  have hb := blockCols_toList kappas.size hk
  unfold Model.placementsOf
  simp only []
  generalize Array.filter (fun c ↦ (keccakSlotTable[c]?.getD none).isNone &&
        !keccakOutputTable[c]?.getD false) (Array.range kappas.size) = bw at hb ⊢
  have hbsz : bw.size = blockList.length := by rw [← Array.length_toList, hb]
  have hsizes : ∀ q < blockList.length,
      (bw.map fun x ↦ kappas.getD x 0).getD q 0 = kappas.getD (blockList.getD q 0) 0 := by
    intro q hq
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, ← Array.getElem?_toList, hb,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
    rfl
  have hmsz : (bw.map fun x ↦ kappas.getD x 0).size = blockList.length := by simp [hbsz]
  obtain ⟨h2, h1sz, h1⟩ := stackOffsets_spec (bw.map fun x ↦ kappas.getD x 0)
  generalize Model.stackOffsets (bw.map fun x ↦ kappas.getD x 0) = sw at h2 h1sz h1 ⊢
  obtain ⟨ow, tw⟩ := sw
  simp only at h2 h1sz h1 ⊢
  have hnd : bw.toList.Nodup := by rw [hb]; exact List.nodup_range.filter _
  have hlt : ∀ c ∈ bw.toList, c < kappas.size := by
    rw [hb, hk]; exact fun c hc ↦ lt_of_mem_blockList hc
  have hoff : ∀ c ∈ blockList, (Array.foldl (fun acc (x : ℕ × ℕ) ↦ acc.set! x.1 x.2)
      (Array.replicate kappas.size 0) (bw.zip ow)).getD c 0 =
      sumF (kappas.getD · 0) (keyF (kappas.getD · 0) c) := by
    intro c hc
    rw [offsets_getD kappas.size bw ow ow.toList rfl hnd hlt (by rw [Array.length_toList, h1sz,
      hmsz, hbsz]), hb]
    have hp : blockList.idxOf c < blockList.length := List.idxOf_lt_length_of_mem hc
    have hpc : blockList.getD (blockList.idxOf c) 0 = c := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some,
        List.getElem_idxOf]
    have hl : ow.toList.getD (blockList.idxOf c) 0 = ow.getD (blockList.idxOf c) 0 := by
      simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]
    rw [hl, h1 _ (by rw [hmsz]; exact hp), sum_before (fun x ↦ kappas.getD x 0) _ hmsz hsizes hp, hpc]
  refine ⟨by rw [h2, sum_all (fun x ↦ kappas.getD x 0) _ hmsz hsizes], by simp [hk], fun c hc ↦ ?_⟩
  have hck : c < kappas.size := by omega
  have hcc : c < columnCount := by rw [columnCount_158]; exact hc
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_zipIdx,
    Array.getElem?_eq_getElem hck]
  simp only [Option.map_some, Option.getD_some, Nat.zero_add]
  rw [keccakSlotTable_get hcc, keccakOutputTable_get hcc, keccakSlot_eq c hc, keccakOutput_eq c hc]
  have hκ : kappas[c] = kappas.getD c 0 := by simp [Array.getD_eq_getD_getElem?, hck]
  unfold plF
  rcases hs : slotF c with _ | sl
  · by_cases ho : outF c = true
    · simp [ho]
    · rw [Bool.not_eq_true] at ho
      simp only [ho, Bool.false_eq_true, ↓reduceIte]
      rw [hoff c (mem_blockList hc (by simp [hs]) ho), hκ]
  · simp only []
    rw [show qkeccak = 4 from rfl, hoff 4 (by decide), hκ]

/-! ## The columns' log-sizes -/

/-- A global column's log-size, from the memory's and the bytecode's log-sizes and the heights. -/
def kapF (lm lb : Nat) (hs : Array Nat) (c : Nat) : Nat :=
  if c < 3 then lm else if c = 3 then lb else if c = 4 then hs.getD 5 0 + 6
  else if c < 18 then hs.getD 0 0 else if c < 31 then hs.getD 1 0 else if c < 38 then hs.getD 2 0
  else if c < 52 then hs.getD 3 0 else if c < 66 then hs.getD 4 0 else hs.getD 5 0

theorem tablesW_shape : tablesW.map (fun t ↦ (t.opcode, t.width)) =
    #[(0, 13), (1, 13), (2, 7), (3, 14), (4, 14), (5, 92)] := by decide +kernel

theorem columnKappas_eq (lm lb : Nat) (hs : Array Nat) :
    (Model.columnKappas lm lb hs).toList = [lm, lm, lm, lb, hs.getD 5 0 + 6] ++
      (List.replicate 13 (hs.getD 0 0) ++ List.replicate 13 (hs.getD 1 0) ++
        List.replicate 7 (hs.getD 2 0) ++ List.replicate 14 (hs.getD 3 0) ++
        List.replicate 14 (hs.getD 4 0) ++ List.replicate 92 (hs.getD 5 0)) := by
  have h : tablesW.flatMap (fun t ↦ Array.replicate t.width (hs.getD t.opcode 0)) =
      (tablesW.map (fun t ↦ (t.opcode, t.width))).flatMap
        (fun p ↦ Array.replicate p.2 (hs.getD p.1 0)) := by
    rw [Array.flatMap_map]
  rw [Model.columnKappas, h, tablesW_shape]
  have hq : qkeccakSlotBits = 6 := by decide
  simp [Array.flatMap, hq]
  exact ⟨rfl, rfl⟩

theorem columnKappas_getD (lm lb : Nat) (hs : Array Nat) {c : Nat} (hc : c < 158) :
    (Model.columnKappas lm lb hs).getD c 0 = kapF lm lb hs c := by
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, columnKappas_eq]
  unfold kapF
  split_ifs <;>
    simp (disch := (try simp only [List.length_append, List.length_replicate, List.length_cons,
      List.length_nil]); omega) only [List.getElem?_append_left, List.getElem?_append_right,
      List.getElem?_replicate_of_lt, List.length_append, List.length_replicate, List.length_cons,
      List.length_nil, Option.getD_some]
  all_goals first
    | (interval_cases c <;> rfl)
    | (subst_vars; rfl)

theorem columnKappas_size' (lm lb : Nat) (hs : Array Nat) : (Model.columnKappas lm lb hs).size = 158 := by
  rw [← Array.length_toList, columnKappas_eq]; simp

/-! ## `buildLayout` and the rest of phase 1 -/

/-- `buildLayout`'s layout, its checks passed. -/
def layoutF (bc : Array UInt64) (logMemory logBytecode : Nat) (tableRows : Array Nat) : LayoutW :=
  let heights := Array.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) tableRows
    tableLogFloors.toArray
  let (push, pull, count) := busBlocks heights tableRows
  let (placements, stackLog) := Model.placementsOf (Model.columnKappas logMemory logBytecode heights)
  ⟨logMemory, logBytecode, bc, push, pull, count, placements, stackLog, heights⟩

theorem buildLayout_eq (bc : Array UInt64) (lm : Nat) (rows : Array Nat) :
    Model.buildLayout bc lm rows =
      if (0 < bc.size ∧ bc.size &&& (bc.size - 1) = 0) ∧ busBits ≤ bitLength bc.size - 1 ∧
          1 ≤ lm ∧ lm ≤ 30 ∧ rows.all (· ≤ 2 ^ 30) ∧ bitLength bc.size - 1 - busBits ≤ 30 ∧
          rows.size = nTables then
        some (layoutF bc lm (bitLength bc.size - 1 - busBits) rows)
      else none := by
  unfold Model.buildLayout log2Strict
  by_cases h : 0 < bc.size ∧ bc.size &&& (bc.size - 1) = 0
  · simp only [h, and_self, ↓reduceIte, true_and]
    rfl
  · simp only [h, ↓reduceIte, false_and]

/-- `readAnnouncedSizes` after its scalars: the checks, the layout, the rate exponent. -/
def tailP (bc : Array UInt64) (announced : Array EW) : Option (LayoutW × Nat) :=
  if announced.all (·.c1 == 0) then
    let logMemory := (announced.getD 0 0).c0.toNat
    let tableRows := (announced.extract 1 (1 + nTables)).map (·.c0.toNat)
    let logInverseRate := (announced.back?.getD 0).c0.toNat
    if 1 ≤ logInverseRate && logInverseRate ≤ 4 then
      match Model.buildLayout bc logMemory tableRows with
      | none => none
      | some layout =>
        if Whir.minLogStack ≤ layout.stackLog && layout.stackLog ≤ Whir.maxLogStack then
          some (layout, logInverseRate)
        else none
    else none
  else none

theorem readAnnouncedSizes_run (bc : Array UInt64) (t : TState) :
    (Model.readAnnouncedSizes bc).run t = ((readScalars (2 + nTables)).run t).bind
      fun p ↦ (tailP bc p.1).map (·, p.2) := by
  unfold Model.readAnnouncedSizes
  rw [StateT.run_bind]
  rcases (readScalars (2 + nTables)).run t with _ | ⟨a, t1⟩
  · rfl
  · show (_ : Option _) = (tailP bc a).map (·, t1)
    unfold tailP
    have hr : ∀ (b : Bool) (s : TState), (Model.require b).run s = if b then some ((), s) else none :=
      fun b s ↦ by cases b <;> rfl
    simp only [Option.bind_eq_bind, Option.bind_some, StateT.run_bind, hr]
    cases h1 : a.all fun x ↦ x.c1 == 0
    · rfl
    cases h2 : (decide (1 ≤ (a.back?.getD 0).c0.toNat) && decide ((a.back?.getD 0).c0.toNat ≤ 4))
    · rfl
    cases hb : Model.buildLayout bc (a.getD 0 0).c0.toNat
        (Array.map (fun x ↦ x.c0.toNat) (a.extract 1 (1 + nTables))) with
    | none => rfl
    | some layout =>
      simp only [↓reduceIte, Option.bind_some, Model.liftOpt, StateT.run_pure, Option.pure_def]
      by_cases h3 : (decide (Whir.minLogStack ≤ layout.stackLog) &&
        decide (layout.stackLog ≤ Whir.maxLogStack)) = true <;> simp only [h3] <;> rfl

/-! ## Columns' sizes by any function agreeing on the global columns -/

theorem sumF_congr {κ κ' : Nat → Nat} (h : ∀ c < 158, κ c = κ' c) (kr : Nat) :
    sumF κ kr = sumF κ' kr := by
  unfold sumF
  refine List.foldl_ext _ _ _ fun acc c hc ↦ ?_
  have := h c (List.mem_range.mp hc)
  rw [sumStep, sumStep, keyF, keyF, this]

theorem plF_congr {κ κ' : Nat → Nat} (h : ∀ c < 158, κ c = κ' c) {c : Nat} (hc : c < 158) :
    plF κ c = plF κ' c := by
  unfold plF
  simp only [keyF, h c hc, h 4 (by omega), sumF_congr h]

/-! ## Bit lengths -/

theorem bitLength_succ_div (n : Nat) (hn : n ≠ 0) : bitLength n = bitLength (n / 2) + 1 := by
  unfold bitLength
  by_cases h2 : n / 2 = 0
  · have : ¬ 2 ≤ n := by omega
    simp only [hn, h2, ↓reduceIte, Nat.log2_def n, this]
  · have : 2 ≤ n := by omega
    simp only [hn, h2, ↓reduceIte, Nat.log2_def n, this]

theorem bitLength_le {n k : Nat} (h : n < 2 ^ k) : bitLength n ≤ k := by
  unfold bitLength
  split
  · omega
  · have := (Nat.log2_lt (by omega)).mpr h
    omega

theorem log2Ceil_le {r : Nat} (h : r ≤ 2 ^ 30) : log2Ceil r ≤ 30 :=
  bitLength_le (by omega)

/-! ## The heights -/

/-- A table's least log-height. -/
def floorF (i : Nat) : Nat := if i = 5 then 9 else 0

/-- The tables' log-heights, from their row counts. -/
def heightsF (rows : Array Nat) : Array Nat :=
  Array.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) rows tableLogFloors.toArray

theorem heightsF_size {rows : Array Nat} (h : rows.size = 6) : (heightsF rows).size = 6 := by
  simp [heightsF, h, tableLogFloors]

theorem heightsF_getD {rows : Array Nat} (h : rows.size = 6) {i : Nat} (hi : i < 6) :
    (heightsF rows).getD i 0 = max (log2Ceil (rows.getD i 0)) (floorF i) := by
  have hf : tableLogFloors.toArray.getD i 0 = floorF i := by
    simp only [tableLogFloors, keccakMinStepsLog, floorF]
    interval_cases i <;> rfl
  rw [← hf]
  simp [heightsF, Array.getD_eq_getD_getElem?, h, hi, tableLogFloors]

/-! ## `tailP` as one condition -/

/-- The announced memory log-size. -/
def lmA (a : Array EW) : Nat := (a.getD 0 0).c0.toNat

/-- The announced row counts. -/
def rowsA (a : Array EW) : Array Nat := (a.extract 1 (1 + nTables)).map (·.c0.toNat)

/-- The announced rate exponent. -/
def rateA (a : Array EW) : Nat := (a.back?.getD 0).c0.toNat

theorem rateA_eq {a : Array EW} (ha : a.size = 8) : rateA a = (a.getD 7 0).c0.toNat := by
  simp [rateA, Array.back?, ha, Array.getD_eq_getD_getElem?]

theorem rowsA_size {a : Array EW} (ha : a.size = 8) : (rowsA a).size = 6 := by
  simp [rowsA, ha, nTables]

theorem rowsA_getD {a : Array EW} (ha : a.size = 8) {i : Nat} (hi : i < 6) :
    (rowsA a).getD i 0 = (a.getD (1 + i) 0).c0.toNat := by
  simp [rowsA, Array.getD_eq_getD_getElem?, ha, nTables, hi,
    Array.getElem?_eq_getElem (show 1 + i < a.size by omega)]

/-- The layout phase 1 builds, from the bytecode and the scalars. -/
def layoutA (bc : Array UInt64) (a : Array EW) : LayoutW :=
  layoutF bc (lmA a) (bitLength bc.size - 5) (rowsA a)

/-- Every check of phase 1. -/
def TailOk (bc : Array UInt64) (a : Array EW) : Prop :=
  (a.all (·.c1 == 0)) = true ∧ (1 ≤ rateA a ∧ rateA a ≤ 4) ∧
    (0 < bc.size ∧ bc.size &&& (bc.size - 1) = 0) ∧ (5 ≤ bitLength bc.size ∧ bitLength bc.size ≤ 35) ∧
    (1 ≤ lmA a ∧ lmA a ≤ 30) ∧ (∀ i < 6, (rowsA a).getD i 0 ≤ 2 ^ 30) ∧
    (layoutA bc a).stackLog ≤ 30

theorem layoutF_stackLog_ge (bc : Array UInt64) (lm lb : Nat) (rows : Array Nat) :
    16 ≤ (layoutF bc lm lb rows).stackLog := by
  have := (placementsOf_spec _ (columnKappas_size' lm lb (heightsF rows))).1
  simp only [layoutF]
  rw [show Array.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) rows
    tableLogFloors.toArray = heightsF rows from rfl, this]
  exact Nat.le_max_left _ _

theorem ite_true_of {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem ite_false_of {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

open Classical in
theorem tailP_eq (bc : Array UInt64) (a : Array EW) (ha : a.size = 8) :
    tailP bc a = if TailOk bc a then some (layoutA bc a, rateA a) else none := by
  have e1 : (a.getD 0 0).c0.toNat = lmA a := rfl
  have e2 : (a.extract 1 (1 + nTables)).map (·.c0.toNat) = rowsA a := rfl
  have e3 : (a.back?.getD 0).c0.toNat = rateA a := rfl
  have hrs := rowsA_size ha
  have hall : ((rowsA a).all (· ≤ 2 ^ 30)) = true ↔ ∀ i < 6, (rowsA a).getD i 0 ≤ 2 ^ 30 := by
    rw [Array.all_eq_true]
    constructor
    · intro h i hi
      have := h i (by omega)
      simpa [Array.getD_eq_getD_getElem?, hrs, hi] using this
    · intro h i hi
      have := h i (by omega)
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some] at this
      simpa using this
  have hb : bitLength bc.size - 1 - busBits = bitLength bc.size - 5 := by
    simp only [busBits]; omega
  have hsl := layoutF_stackLog_ge bc (lmA a) (bitLength bc.size - 5) (rowsA a)
  unfold tailP
  simp only [e1, e2, e3]
  rw [buildLayout_eq, hb]
  by_cases h1 : (a.all fun x ↦ x.c1 == 0) = true
  swap
  · simp only [h1, Bool.false_eq_true, ↓reduceIte, show ¬ TailOk bc a from fun h ↦ h1 h.1]
  by_cases h2 : 1 ≤ rateA a ∧ rateA a ≤ 4
  swap
  · simp only [h1, ↓reduceIte, show ¬ TailOk bc a from fun h ↦ h2 h.2.1]
    have : (decide (1 ≤ rateA a) && decide (rateA a ≤ 4)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    simp only [this, Bool.false_eq_true, ↓reduceIte]
  have h2' : (decide (1 ≤ rateA a) && decide (rateA a ≤ 4)) = true := by simp [h2]
  simp only [h1, h2', ↓reduceIte]
  by_cases hc : (0 < bc.size ∧ bc.size &&& (bc.size - 1) = 0) ∧ busBits ≤ bitLength bc.size - 1 ∧
      1 ≤ lmA a ∧ lmA a ≤ 30 ∧ ((rowsA a).all (· ≤ 2 ^ 30)) = true ∧
      bitLength bc.size - 5 ≤ 30 ∧ (rowsA a).size = nTables
  · rw [ite_true_of hc]
    obtain ⟨c3, c4, c5, c6, c7, c8, -⟩ := hc
    simp only [busBits] at c4
    by_cases h7 : (layoutF bc (lmA a) (bitLength bc.size - 5) (rowsA a)).stackLog ≤ 30
    · have hok : TailOk bc a := ⟨h1, h2, c3, ⟨by omega, by omega⟩, ⟨c5, c6⟩, hall.mp c7, h7⟩
      have : (decide (Whir.minLogStack ≤ (layoutF bc (lmA a) (bitLength bc.size - 5)
          (rowsA a)).stackLog) && decide ((layoutF bc (lmA a) (bitLength bc.size - 5)
          (rowsA a)).stackLog ≤ Whir.maxLogStack)) = true := by
        rw [show Whir.minLogStack = 16 from rfl, show Whir.maxLogStack = 30 from rfl]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        omega
      simp only [this, hok, ↓reduceIte, layoutA]
    · have hok : ¬ TailOk bc a := fun h ↦ h7 h.2.2.2.2.2.2
      have : (decide (Whir.minLogStack ≤ (layoutF bc (lmA a) (bitLength bc.size - 5)
          (rowsA a)).stackLog) && decide ((layoutF bc (lmA a) (bitLength bc.size - 5)
          (rowsA a)).stackLog ≤ Whir.maxLogStack)) = false := by
        rw [show Whir.minLogStack = 16 from rfl, show Whir.maxLogStack = 30 from rfl]
        simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
        omega
      simp only [this, hok, Bool.false_eq_true, ↓reduceIte]
  · rw [ite_false_of hc]
    have hok : ¬ TailOk bc a := fun ⟨_, _, c3, c4, c5, c6, _⟩ ↦
      hc ⟨c3, by simp only [busBits]; omega, c5.1, c5.2, hall.mpr c6, by omega, by
        rw [hrs]; rfl⟩
    simp only [hok, ↓reduceIte]

/-- **The layout's fields** as the code computes them. -/
theorem layoutF_facts (bc : Array UInt64) (lm lb : Nat) (rows : Array Nat) :
    (layoutF bc lm lb rows).logMemory = lm ∧ (layoutF bc lm lb rows).logBytecode = lb ∧
      (layoutF bc lm lb rows).bytecode = bc ∧
      (layoutF bc lm lb rows).tableLogHeights = heightsF rows ∧
      busBlocks (heightsF rows) rows = ((layoutF bc lm lb rows).push,
        (layoutF bc lm lb rows).pull, (layoutF bc lm lb rows).count) ∧
      (layoutF bc lm lb rows).placements.size = 158 ∧
      (∀ c < 158, (layoutF bc lm lb rows).placements.getD c none =
        plF (kapF lm lb (heightsF rows)) c) ∧
      (layoutF bc lm lb rows).stackLog =
        max Whir.minLogStack (log2Ceil (sumF (kapF lm lb (heightsF rows)) 0)) := by
  have hk := columnKappas_size' lm lb (heightsF rows)
  obtain ⟨h1, h2, h3⟩ := placementsOf_spec _ hk
  have hκ : ∀ c < 158, (Model.columnKappas lm lb (heightsF rows)).getD c 0 =
      kapF lm lb (heightsF rows) c := fun c hc ↦ columnKappas_getD _ _ _ hc
  simp only [layoutF]
  rw [show Array.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) rows
    tableLogFloors.toArray = heightsF rows from rfl]
  refine ⟨trivial, trivial, trivial, rfl, rfl, h2, fun c hc ↦ ?_, ?_⟩
  · rw [h3 c hc]; exact plF_congr hκ hc
  · rw [h1, sumF_congr hκ]

theorem kapF_le {lm lb : Nat} {hs : Array Nat} (hlm : lm ≤ 30) (hlb : lb ≤ 30)
    (hhs : ∀ i < 6, hs.getD i 0 ≤ 30) (c : Nat) : kapF lm lb hs c ≤ 36 := by
  have := hhs 0 (by omega); have := hhs 1 (by omega); have := hhs 2 (by omega)
  have := hhs 3 (by omega); have := hhs 4 (by omega); have := hhs 5 (by omega)
  unfold kapF
  split_ifs <;> omega

end NativeVm.Math.Layout
