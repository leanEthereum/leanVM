module

public import LeanVM.Cost.Bounds.Decoder.EntryTable
import all LeanVM.Protocol.Extraction.Fast.SortedMap

/-!
# Bound: the pc table, compiled

`pcTableT` (`Cost/Decoder/EntryTable.lean`): the guest's `1753` functions filed at the code of
their entry pc, built once by the decoder's top. Its shape and prices:

* `pcTableT_good`: a good map of word-sized keys, `1753` insertions (below `2^11`);
* **`pcTableT_cost`**: built at most `16430885` (each insertion amortized: a power `g^e`, `e < 2^19`,
  a lookup and the carry);
* **`pcTableT_get_cost`**: a lookup at most `7093` (`11` levels, a binary search each), the `Gpc` of
  `entryArrayT_cost` (`EntryArray.lean`);
* **`pcTableT_getD_length`**: at most two functions at one pc (the entry pcs repeat at most twice,
  `GuestTablesBounds.lean`; `gpow` is injective below the order of `g`), the `M` of
  `entryArrayT_cost`; **`pcTableT_getD_lt`**: every function filed is below `1753`.
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Decoder LeanVM.Cost.Library LeanVM.Parameters LeanVM.Semantics
open LeanVM.Extraction LeanVM.Extraction.Fast LeanVM.Guest.Located LeanVM.Guest

public section

variable (P : MachineProgram)

/-- The code of function `j`'s entry pc. -/
@[expose] def pcCode (j : ℕ) : ℕ := laneCode (addressOfIndex (guestEntries.getD j 0))

theorem pcCode_key (j : ℕ) : NatKey (pcCode j) := UInt64.toNat_lt _

theorem addEntry_eq (m : SortedMap ℕ (List ℕ)) (j : ℕ) :
    addEntry m j = m.insert (pcCode j) (j :: m.getD (pcCode j) []) := rfl

theorem entry_lt (j : ℕ) : guestEntries.getD j 0 < 2 ^ 19 := by
  have h := guestEntriesList_lt
  rw [List.all_eq_true] at h
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray]
  cases hj : guestEntriesList[j]? with
  | none => simp
  | some x =>
    simp only [Option.getD_some]
    exact of_decide_eq_true (h x (List.mem_of_getElem? hj))

/-- The pc table's fold keeps a good map of word-sized keys, one insertion per function. -/
theorem pcFold_good : ∀ (l : List ℕ) (m : SortedMap ℕ (List ℕ)), smGood m →
    KeysIn NatKey m.levels →
      smGood (l.foldl addEntry m) ∧ KeysIn NatKey (l.foldl addEntry m).levels ∧
        smWeightSum (l.foldl addEntry m) = smWeightSum m + l.length
  | [], m, hg, hQ => ⟨hg, hQ, by simp⟩
  | j :: l, m, hg, hQ => by
    rw [List.foldl_cons, addEntry_eq]
    obtain ⟨h1, h2⟩ := smGood_insert hg (pcCode j) (j :: m.getD (pcCode j) [])
    obtain ⟨h3, h4, h5⟩ := pcFold_good l _ h1 (keysIn_insert hQ (pcCode_key j) _)
    refine ⟨h3, h4, ?_⟩
    rw [h5, h2]
    simp only [List.length_cons]
    omega

/-- **The pc table is good**: word-sized keys, `1753` insertions. -/
theorem pcTableT_good :
    smGood pcTableT ∧ KeysIn NatKey pcTableT.levels ∧ smWeightSum pcTableT = 1753 := by
  have := pcFold_good (List.range nFns) SortedMap.empty smGood_empty
    (fun _ h ↦ by simp [SortedMap.empty] at h)
  rw [smWeightSum_empty, List.length_range] at this
  exact this

/-- The pc table's positions and weights are words. -/
theorem wl_eleven : wl 11 = 1 := rfl

/-- **A lookup in the pc table** (`getPcC`): at most `7093`. -/
theorem pcTableT_get_cost (hP : Includes P getPcC.costDeps) (k : ℕ) (hk : NatKey k) :
    machineCost P getPcC.costIdx [encodeValue pcTableT, encodeValue k] ≤ 7093 := by
  obtain ⟨hg, hQ, hw⟩ := pcTableT_good
  obtain ⟨hlev, hsz⟩ := smGood_levels_le hg (D := 11) (by rw [hw]; norm_num)
  have := getPc_cost P hP 11 pcTableT hQ hlev
    (fun l hl ↦ (hsz l hl).1.trans (hsz l hl).2) k hk
  rw [wl_eleven] at this
  omega

/-! ## The functions at one pc -/

theorem pcFold_getD : ∀ (l : List ℕ) (m : SortedMap ℕ (List ℕ)) (k : ℕ),
    (l.foldl addEntry m).getD k [] =
      (l.filter fun j ↦ decide (pcCode j = k)).reverse ++ m.getD k []
  | [], m, k => by simp
  | j :: l, m, k => by
    rw [List.foldl_cons, pcFold_getD l _ k, addEntry_eq, SortedMap.getD_insert]
    by_cases h : pcCode j = k
    · subst h
      simp
    · simp [h]

/-- The functions at pc code `k`: those whose entry has that code, below `1753`. -/
theorem pcTableT_getD (k : ℕ) :
    pcTableT.getD k [] = ((List.range nFns).filter fun j ↦ decide (pcCode j = k)).reverse := by
  have := pcFold_getD (List.range nFns) SortedMap.empty k
  rw [SortedMap.getD_empty, List.append_nil] at this
  exact this

/-- **Every function filed is below `1753`.** -/
theorem pcTableT_getD_lt (k : ℕ) : ∀ j ∈ pcTableT.getD k [], j < 2 ^ 64 := by
  intro j hj
  rw [pcTableT_getD, List.mem_reverse, List.mem_filter, List.mem_range] at hj
  have : nFns = 1753 := rfl
  omega

theorem range_countP_getD (e : ℕ) : ∀ l : List ℕ,
    (List.range l.length).countP (fun j ↦ decide (l.getD j 0 = e)) = l.count e
  | [] => by simp
  | a :: l => by
    rw [List.length_cons, List.range_succ_eq_map, List.countP_cons, List.countP_map,
      List.count_cons]
    have := range_countP_getD e l
    simp only [Function.comp_def, List.getD_cons_succ, List.getD_cons_zero] at this ⊢
    rw [this]
    by_cases h : a = e <;> simp [h]

theorem guestEntries_getD (j : ℕ) : guestEntries.getD j 0 = guestEntriesList.getD j 0 := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

set_option maxRecDepth 100000 in
/-- **At most two functions at one pc.** -/
theorem pcTableT_getD_length (k : ℕ) : (pcTableT.getD k []).length ≤ 2 := by
  rw [pcTableT_getD, List.length_reverse, ← List.countP_eq_length_filter]
  have hlen : guestEntriesList.length = nFns := rfl
  by_cases h0 : ∃ j0 ∈ List.range nFns, pcCode j0 = k
  · obtain ⟨j0, hj0, hk⟩ := h0
    have hj0' := List.mem_range.mp hj0
    have hmono : (List.range nFns).countP (fun j ↦ decide (pcCode j = k)) ≤
        (List.range nFns).countP (fun j ↦ decide (guestEntriesList.getD j 0 =
          guestEntriesList.getD j0 0)) := by
      refine List.countP_mono_left fun j _ hj ↦ ?_
      rw [decide_eq_true_iff] at hj ⊢
      have hc : pcCode j = pcCode j0 := hj.trans hk.symm
      unfold pcCode at hc
      have hg : addressOfIndex (guestEntries.getD j 0) = addressOfIndex (guestEntries.getD j0 0) :=
        laneCode_injective hc
      have := gpow_injOn (show guestEntries.getD j 0 ∈ Set.Iio (2 ^ 64 - 1) by
          have := entry_lt j; simp only [Set.mem_Iio]; omega)
        (show guestEntries.getD j0 0 ∈ Set.Iio (2 ^ 64 - 1) by
          have := entry_lt j0; simp only [Set.mem_Iio]; omega) hg
      rwa [guestEntries_getD, guestEntries_getD] at this
    have hcnt : (List.range nFns).countP (fun j ↦ decide (guestEntriesList.getD j 0 =
        guestEntriesList.getD j0 0)) = guestEntriesList.count (guestEntriesList.getD j0 0) := by
      rw [← hlen]; exact range_countP_getD _ _
    have hc := guestEntriesList_count
    rw [List.all_eq_true] at hc
    have hmem : guestEntriesList.getD j0 0 ∈ guestEntriesList := by
      rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hj0')]
      exact List.getElem_mem _
    have := of_decide_eq_true (hc _ hmem)
    omega
  · simp only [not_exists, not_and] at h0
    have : (List.range nFns).countP (fun j ↦ decide (pcCode j = k)) = 0 :=
      List.countP_eq_zero.2 fun j hj ↦ by simpa using h0 j hj
    omega

/-! ## Building it -/

/-- The pc table's invariant, `r` insertions left: below `2^11`. -/
@[expose] def PcInv (m : SortedMap ℕ (List ℕ)) (r : ℕ) : Prop :=
  smGood m ∧ KeysIn NatKey m.levels ∧ smWeightSum m + r ≤ 2 ^ 11

set_option maxRecDepth 100000 in
/-- One function filed (`addEntryC`), amortized: at most `9344`. -/
theorem addEntry_amortized (hP : Includes P addEntryC.costDeps) (m : SortedMap ℕ (List ℕ)) (r : ℕ)
    (hm : PcInv m (r + 1)) (j : ℕ) :
    PcInv (addEntry m j) r ∧
      machineCost P addEntryC.costIdx [encodeValue m, encodeValue j] +
          37 * potential 11 (addEntry m j).levels ≤ 37 * potential 11 m.levels + 9344 := by
  obtain ⟨hg, hQ, hw⟩ := hm
  have hN : smWeightSum m < 2 ^ 11 := by omega
  obtain ⟨hlev, hsz⟩ := smGood_levels_le hg hN
  obtain ⟨h1, h2⟩ := smGood_insert hg (pcCode j) (j :: m.getD (pcCode j) [])
  refine ⟨by rw [addEntry_eq]; exact ⟨h1, keysIn_insert hQ (pcCode_key j) _, by omega⟩, ?_⟩
  rw [addEntryC.costEq P hP, addAtC.costEq P (by includes), insertPcC.costEq P (by includes)]
  have hp := powSqW_cost P (by includes) (W := 19) (by norm_num) (by norm_num) (entry_lt j)
  have hget := getPc_cost P (by includes) 11 m hQ hlev
    (fun l hl ↦ (hsz l hl).1.trans (hsz l hl).2) _ (pcCode_key j)
  have hcarry := carryPc_amortized P (by includes) 11 m hg hQ hN
    ⟨1, #[(pcCode j, j :: m.getD (pcCode j) [])], by simp [Ascending]⟩ rfl rfl
    (fun e he ↦ by simp at he; rw [he]; exact pcCode_key j)
  have hins : (addEntry m j).levels =
      carry ⟨1, #[(pcCode j, j :: m.getD (pcCode j) [])], by simp [Ascending]⟩ m.levels := rfl
  rw [hins]
  unfold psAt at hp
  rw [wl_eleven] at hget hcarry
  change machineCost P getPcC.costIdx [encodeValue m, encodeValue (pcCode j)] ≤ _ at hget
  generalize m.get? (laneCode (addressOfIndex (guestEntries.getD j 0))) = o
  cases o <;> dsimp only <;> unfold pcCode at hget hcarry ⊢ <;> omega

set_option maxRecDepth 100000 in
/-- **The pc table** (`pcTableTC`), built once: at most `16430885`. -/
theorem pcTableT_cost (hP : Includes P pcTableTC.costDeps) :
    machineCost P pcTableTC.costIdx [] ≤ 16430885 := by
  rw [pcTableTC.costEq P hP]
  have hn : nFns = 1753 := rfl
  have hr := rangeLoop_cost P (by includes) nFns [] (by rw [hn]; norm_num)
  obtain ⟨-, hF⟩ := listFoldl_amortized' P (by includes) _ (.closure pcTableTC.lam0.costIdx [])
    (fun m j ↦ RunsApp.of_spec (pcTableTC.lam0.costSpec P (by includes) m j))
    9347 (fun m ↦ 37 * potential 11 m.levels) PcInv (List.range nFns) SortedMap.empty
    ⟨smGood_empty, fun _ h ↦ by simp [SortedMap.empty] at h, by
      simp [smWeightSum_empty, hn]⟩
    (fun acc r hacc j _ ↦ by
      obtain ⟨h1, h2⟩ := addEntry_amortized P (by includes) acc r hacc j
      refine ⟨h1, ?_⟩
      rw [appCost_fn, List.nil_append, pcTableTC.lam0.costEq P (by includes), List.length_nil]
      omega)
  have h0 : potential 11 (SortedMap.empty : SortedMap ℕ (List ℕ)).levels = 0 := rfl
  rw [h0, Nat.mul_zero, Nat.zero_add, List.length_range] at hF
  rw [hn] at hr hF ⊢
  omega

end

end LeanVM.Cost.Bounds
