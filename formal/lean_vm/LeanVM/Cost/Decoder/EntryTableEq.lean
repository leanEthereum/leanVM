module

public import LeanVM.Cost.Decoder.EntryTable
public import LeanVM.Cost.Decoder.GuestTablesCheck
import all LeanVM.Protocol.Extraction.Fast.SortedMap

/-!
# The replayed frame map, restated, is the deployed one

At the guest's tables (`GuestTablesCheck.lean`): `pcTableT = pcTable`, `entryTableT pcTable =
entryTable`, and **`frameAt_eq`**: the closure `frameAt (entryTableT pcTableT pre states rd) rd`
is `Guest.Fast.frameVFastN pre states rd`, the frame map of the deployed decoder keyed by index
(`decode_eq_numbered`).

The entry table as one sorted array (`entryArrayT`): **`searchIn_entryArrayT`**, its binary search
of every key is `entryTableT`'s `get?` (the first pair filed for the key: `entryTableT_get?`; the
stable sort keeps each key's pairs in filing order, `lookup_mergeSort`; the first of each run is
kept, `lookup_dedupFirst`, the result strictly ascending, `ascending_dedupFirst`), so
**`frameAtA_entryArrayT`**: `frameAtA (entryArrayT …) rd = frameAt (entryTableT …) rd`, and
**`frameAtA_eq`**.
-/

namespace LeanVM.Cost.Decoder

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Located
open LeanVM.Guest.Fast LeanVM.Extraction.Fast

attribute [local instance] lexOrd

@[expose] public section

theorem foldl_congr_mem {α β : Type} {f g : α → β → α} :
    ∀ (l : List β) (a : α), (∀ a, ∀ b ∈ l, f a b = g a b) → l.foldl f a = l.foldl g a
  | [], _, _ => rfl
  | b :: l, a, h => by
    rw [List.foldl_cons, List.foldl_cons, h a b List.mem_cons_self]
    exact foldl_congr_mem l _ fun a b hb ↦ h a b (List.mem_cons_of_mem _ hb)

/-- **The table of entries is the guest's.** -/
theorem pcTableT_eq : pcTableT = pcTable := by
  unfold pcTableT pcTable
  refine foldl_congr_mem _ _ fun m j hj ↦ ?_
  rw [addEntry, guestEntries_eq j (List.mem_range.mp hj)]

theorem entryKeyT_eq (rd : Reader) (r : Registers K) {j : ℕ} (hj : j < nFns) :
    entryKeyT rd r j = entryKey rd r j := by
  rw [entryKeyT, entryKey, guestArgCounts_eq j hj, guestRetCounts_eq j hj]

theorem fileStateT_eq (pre : ℕ → K → Bool) (rd : Reader) (m : SortedMap CallKey K)
    (r : Registers K) : fileStateT pcTableT pre rd m r = fileState pre rd m r := by
  rw [fileStateT, fileState, pcTableT_eq]
  refine foldl_congr_mem _ _ fun m j hj ↦ ?_
  rw [fileOne, entryKeyT_eq rd r (mem_pcTable.mp hj).1]

/-- **The entry table is the guest's.** -/
theorem entryTableT_eq (pre : ℕ → K → Bool) (states : List (Registers K)) (rd : Reader) :
    entryTableT pcTableT pre states rd = entryTable pre states rd := by
  have h : fileStateT pcTableT pre rd = fileState pre rd := by
    funext m r
    exact fileStateT_eq pre rd m r
  rw [entryTableT, entryTable, h]

theorem canonIndex_lt (j : ℕ) : canonIndex j < nFns := by
  unfold canonIndex isFunctionIndex nFns
  split
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    omega
  · omega

/-- **The frame map, restated, is the deployed one** (keyed by index). -/
theorem frameAt_eq (pre : ℕ → K → Bool) (states : List (Registers K)) (rd : Reader) :
    frameAt (entryTableT pcTableT pre states rd) rd = frameVFastN pre states rd := by
  funext j args rets v
  rw [entryTableT_eq]
  unfold frameAt frameVFastN
  cases (entryTable pre states rd).get? (callKey (canonIndex j) args rets) with
  | none => rfl
  | some fp =>
    show wordWith rd fp ((guestLocs.getD (canonIndex j) #[]).getD v.idx 0) = _
    have h (a : Array ℕ) (i : ℕ) : a.getD i 0 = a.toList.getD i 0 := by
      simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
    rw [h, guestLocs_eq (canonIndex_lt j)]

/-! ## The entry table as one sorted array -/

theorem keyCmp_eq (a b : CallKey) : keyCmp a b = compare a b := rfl

theorem keyLe_iff (a b : CallKey × K) : keyLe a b = (compare a.1 b.1).isLE := by
  unfold keyLe keyCmp
  cases compare a.1 b.1 <;> rfl

theorem keyLe_trans (a b c : CallKey × K) (h1 : keyLe a b) (h2 : keyLe b c) : keyLe a c := by
  rw [keyLe_iff] at *
  exact Std.TransCmp.isLE_trans h1 h2

theorem keyLe_total (a b : CallKey × K) : keyLe a b || keyLe b a := by
  rw [keyLe_iff, keyLe_iff]
  cases h : compare a.1 b.1
  · rfl
  · rfl
  · rw [Std.OrientedCmp.gt_iff_lt.1 h]; rfl

/-- **The stable sort keeps the first pair of each key.** -/
theorem lookup_mergeSort (l : List (CallKey × K)) (k : CallKey) :
    Extraction.Fast.lookup (l.mergeSort keyLe) k = Extraction.Fast.lookup l k := by
  let p : CallKey × K → Bool := fun e ↦ compare e.1 k == .eq
  have hpw : (l.filter p).Pairwise (fun a b ↦ keyLe a b) := by
    refine List.pairwise_of_forall_mem_list fun a ha b hb ↦ ?_
    have ha' : compare a.1 k = .eq := by simpa [p] using (List.mem_filter.1 ha).2
    have hb' : compare b.1 k = .eq := by simpa [p] using (List.mem_filter.1 hb).2
    rw [Std.LawfulEqCmp.compare_eq_iff_eq] at ha' hb'
    rw [keyLe_iff, ha', hb', Std.ReflOrd.compare_self]
    rfl
  have hs := List.sublist_mergeSort keyLe_trans keyLe_total hpw (List.filter_sublist (p := p) (l := l))
  have hs' : List.Sublist (l.filter p) ((l.mergeSort keyLe).filter p) := by
    have := hs.filter p
    rwa [List.filter_filter, show (fun e ↦ p e && p e) = p from funext fun e ↦ Bool.and_self _] at this
  have hlen : ((l.mergeSort keyLe).filter p).length = (l.filter p).length :=
    ((List.mergeSort_perm l keyLe).filter p).length_eq
  have heq := (hs'.eq_of_length hlen.symm).symm
  unfold Extraction.Fast.lookup
  rw [← List.head?_filter, ← List.head?_filter]
  exact congrArg (fun l ↦ (List.head? l).map (·.2)) heq

/-- **Of each run, the first: the lookups are kept.** -/
theorem lookup_dedupFirst (k : CallKey) : ∀ l : List (CallKey × K),
    Extraction.Fast.lookup (dedupFirst l) k = Extraction.Fast.lookup l k
  | [] => by unfold dedupFirst; rfl
  | [_] => by unfold dedupFirst; rfl
  | a :: b :: l => by
    rw [dedupFirst]
    cases h : keyCmp a.1 b.1 with
    | eq =>
      dsimp only
      rw [lookup_dedupFirst k (a :: l), lookup_cons, lookup_cons, lookup_cons]
      rw [keyCmp_eq] at h
      have hab : a.1 = b.1 := Std.LawfulEqCmp.compare_eq_iff_eq.1 h
      by_cases ha : a.1 = k
      · simp [ha]
      · have hb : b.1 ≠ k := hab ▸ ha
        simp [ha, hb]
    | lt =>
      dsimp only
      rw [lookup_cons, lookup_cons, lookup_dedupFirst k (b :: l)]
    | gt =>
      dsimp only
      rw [lookup_cons, lookup_cons, lookup_dedupFirst k (b :: l)]
termination_by l => l.length

theorem mem_dedupFirst : ∀ (l : List (CallKey × K)) (x : CallKey × K), x ∈ dedupFirst l → x ∈ l
  | [], _, h => by unfold dedupFirst at h; exact h
  | [_], _, h => by unfold dedupFirst at h; exact h
  | a :: b :: l, x, h => by
    rw [dedupFirst] at h
    cases hc : keyCmp a.1 b.1 with
    | eq =>
      rw [hc] at h
      rcases List.mem_cons.1 (mem_dedupFirst (a :: l) x h) with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
    | lt =>
      rw [hc] at h
      rcases List.mem_cons.1 h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_dedupFirst (b :: l) x h)
    | gt =>
      rw [hc] at h
      rcases List.mem_cons.1 h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_dedupFirst (b :: l) x h)
termination_by l => l.length

/-- **A sorted list, each run's first kept, is strictly ascending.** -/
theorem ascending_dedupFirst : ∀ l : List (CallKey × K), l.Pairwise (fun a b ↦ keyLe a b) →
    Ascending (dedupFirst l)
  | [], _ => by unfold dedupFirst; exact List.Pairwise.nil
  | [_], _ => by unfold dedupFirst; exact List.pairwise_singleton _ _
  | a :: b :: l, hl => by
    rw [dedupFirst]
    cases hc : keyCmp a.1 b.1 with
    | eq =>
      dsimp only
      exact ascending_dedupFirst (a :: l)
        (hl.sublist (List.Sublist.cons_cons a (List.sublist_cons_self b l)))
    | lt =>
      dsimp only
      have hbl : (b :: l).Pairwise (fun a b ↦ keyLe a b) := hl.of_cons
      refine List.pairwise_cons.2 ⟨fun y hy ↦ ?_, ascending_dedupFirst (b :: l) hbl⟩
      have hab : compare a.1 b.1 = .lt := hc
      rcases List.mem_cons.1 (mem_dedupFirst (b :: l) y hy) with rfl | hy'
      · exact hab
      · have hby := List.rel_of_pairwise_cons hbl hy'
        rw [keyLe_iff] at hby
        exact Std.TransCmp.lt_of_lt_of_isLE hab hby
    | gt =>
      have hab := List.rel_of_pairwise_cons hl List.mem_cons_self
      rw [keyLe_iff, ← keyCmp_eq, hc] at hab
      cases hab
termination_by l => l.length

/-- The sorted array's binary search is the first pair filed for the key. -/
theorem searchIn_entryArrayT (pcT : SortedMap ℕ (List ℕ)) (pre : ℕ → K → Bool)
    (states : List (Registers K)) (rd : Reader) (k : CallKey) :
    searchIn (entryArrayT pcT pre states rd) k 0 (entryArrayT pcT pre states rd).size =
      Extraction.Fast.lookup (entryPairs pcT pre rd states) k := by
  unfold entryArrayT
  have hs := List.pairwise_mergeSort keyLe_trans keyLe_total (entryPairs pcT pre rd states)
  rw [searchIn_eq _ (by rw [List.toList_toArray]; exact ascending_dedupFirst _ hs),
    List.toList_toArray, lookup_dedupFirst, lookup_mergeSort]

/-- Insertions if new, in order: the map's answer, else the first pair filed. -/
theorem get?_foldl_insertIfNew (k : CallKey) : ∀ (ps : List (CallKey × K)) (m : SortedMap CallKey K),
    (ps.foldl (fun m p ↦ insertIfNew m p.1 p.2) m).get? k =
      (m.get? k).or (Extraction.Fast.lookup ps k)
  | [], m => by simp [lookup_nil]
  | p :: ps, m => by
    rw [List.foldl_cons, get?_foldl_insertIfNew k ps, get?_insertIfNew, lookup_cons,
      Option.or_assoc]
    congr 1
    by_cases h : p.1 = k <;> simp [h]

theorem fileStateT_eq_foldl (pcT : SortedMap ℕ (List ℕ)) (pre : ℕ → K → Bool) (rd : Reader)
    (m : SortedMap CallKey K) (s : Registers K) :
    fileStateT pcT pre rd m s = (statePairs pcT pre rd s).foldl (fun m p ↦ insertIfNew m p.1 p.2) m := by
  unfold fileStateT statePairs
  generalize pcT.getD (laneCode s.pc) [] = js
  induction js generalizing m with
  | nil => rfl
  | cons j js ih =>
    rw [List.foldl_cons, List.filterMap_cons, ih]
    unfold fileOne pairOf
    by_cases h : pre j s.fp = true
    · simp only [h, ↓reduceIte, List.foldl_cons]
    · simp only [h, Bool.false_eq_true, ↓reduceIte]

theorem entryTableT_eq_foldl (pcT : SortedMap ℕ (List ℕ)) (pre : ℕ → K → Bool)
    (states : List (Registers K)) (rd : Reader) :
    entryTableT pcT pre states rd =
      (entryPairs pcT pre rd states).foldl (fun m p ↦ insertIfNew m p.1 p.2) .empty := by
  unfold entryTableT
  generalize (SortedMap.empty : SortedMap CallKey K) = m
  induction states generalizing m with
  | nil => rfl
  | cons s ss ih =>
    rw [List.foldl_cons, ih, fileStateT_eq_foldl, entryPairs, List.foldl_append]

/-- **The entry table answers the first pair filed for each key.** -/
theorem entryTableT_get? (pcT : SortedMap ℕ (List ℕ)) (pre : ℕ → K → Bool)
    (states : List (Registers K)) (rd : Reader) (k : CallKey) :
    (entryTableT pcT pre states rd).get? k =
      Extraction.Fast.lookup (entryPairs pcT pre rd states) k := by
  rw [entryTableT_eq_foldl, get?_foldl_insertIfNew, SortedMap.get?_empty, Option.none_or]

/-- **The frame map on the sorted array is the frame map on the entry table**, on every input. -/
theorem frameAtA_entryArrayT (pcT : SortedMap ℕ (List ℕ)) (pre : ℕ → K → Bool)
    (states : List (Registers K)) (rd : Reader) :
    frameAtA (entryArrayT pcT pre states rd) rd = frameAt (entryTableT pcT pre states rd) rd := by
  funext j args rets v
  unfold frameAtA frameAt
  rw [searchIn_entryArrayT, entryTableT_get?]

/-- **The frame map on the sorted array is the deployed one** (keyed by index). -/
theorem frameAtA_eq (pre : ℕ → K → Bool) (states : List (Registers K)) (rd : Reader) :
    frameAtA (entryArrayT pcTableT pre states rd) rd = frameVFastN pre states rd := by
  rw [frameAtA_entryArrayT, frameAt_eq]

end

end LeanVM.Cost.Decoder
