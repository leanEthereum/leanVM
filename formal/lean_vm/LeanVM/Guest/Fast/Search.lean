module

public import LeanVM.Protocol.Extraction.Fast.SortedMap
public import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Set
import Mathlib.Tactic.ByContra
import Mathlib.Data.List.Nodup
import all LeanVM.Protocol.Extraction.Fast.SortedMap

/-!
# The decoder's count-driven searches, by sorting and binary search

The guest decoder reads a child's claims and the raw signatures off the coverage table by scans
(`B1.Main.slotOf`, `segCount`): a `find?` or a `filter` over a whole region per query, quadratic in
the counts. Here the same answers, on every input (no monotonicity of the memory assumed), from tables
built once:

* `lowerBound t e lo hi`: binary search in a sorted array, the number of its entries below `e`
  (`countP_lt_lowerBound`);
* `coverTable ps`: the pairs `(mark, slot)` of a region sorted (a `SortedMap` keyed by the pair,
  its levels merged), as two arrays: the marks in order and their slots;
  * **`slotIn_coverTable`**: `slotIn` (one binary search) is the first slot holding a mark, the
    `find?` of `slotOf`;
  * **`countIn_coverTable`**: `countIn` (two binary searches) is the number of slots whose marks
    lie in `[a, b)`, the `filter` of `segCount`.
-/

namespace LeanVM.Guest.Fast

open LeanVM.Extraction.Fast

@[expose] public section

/-! ## Binary search -/

/-- **Binary search**: in an array sorted ascending, the first index in `[lo, hi)` whose entry is
at least `e` (`hi` if none). -/
def lowerBound (t : Array ℕ) (e lo hi : ℕ) : ℕ :=
  if lo < hi then
    if t.getD ((lo + hi) / 2) 0 < e then lowerBound t e ((lo + hi) / 2 + 1) hi
    else lowerBound t e lo ((lo + hi) / 2)
  else lo
termination_by hi - lo

/-- An array sorted ascending. -/
def Ascends (t : Array ℕ) : Prop := ∀ i j (hi : i < t.size) (hj : j < t.size), i ≤ j → t[i] ≤ t[j]

theorem lowerBound_spec (t : Array ℕ) (ht : Ascends t) (e : ℕ) :
    ∀ n lo hi, hi - lo = n → lo ≤ hi → hi ≤ t.size →
      (∀ i (h : i < t.size), i < lo → t[i] < e) → (∀ i (h : i < t.size), hi ≤ i → e ≤ t[i]) →
      lowerBound t e lo hi ≤ t.size ∧
        (∀ i (h : i < t.size), i < lowerBound t e lo hi → t[i] < e) ∧
        (∀ i (h : i < t.size), lowerBound t e lo hi ≤ i → e ≤ t[i]) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro lo hi hn hlh hhi hlo hhi'
  rw [lowerBound]
  by_cases hlt : lo < hi
  · simp only [hlt, ↓reduceIte]
    have hmid : (lo + hi) / 2 < t.size := by omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hmid, Option.getD_some]
    split
    · rename_i hc
      refine ih (hi - ((lo + hi) / 2 + 1)) (by omega) _ _ rfl (by omega) hhi (fun i hi' hil ↦ ?_)
        hhi'
      by_cases hil' : i < lo
      · exact hlo i hi' hil'
      · exact Nat.lt_of_le_of_lt (ht i _ hi' hmid (by omega)) hc
    · rename_i hc
      refine ih ((lo + hi) / 2 - lo) (by omega) _ _ rfl (by omega) (by omega) hlo
        (fun i hi' hil ↦ ?_)
      by_cases hil' : hi ≤ i
      · exact hhi' i hi' hil'
      · exact Nat.le_trans (by omega) (ht _ i hmid hi' hil)
  · simp only [hlt, ↓reduceIte]
    have : lo = hi := by omega
    subst this
    exact ⟨hhi, hlo, hhi'⟩

/-- The binary search over the whole array: the first index whose entry is at least `e`. -/
theorem lowerBound_full (t : Array ℕ) (ht : Ascends t) (e : ℕ) :
    lowerBound t e 0 t.size ≤ t.size ∧
      (∀ i (h : i < t.size), i < lowerBound t e 0 t.size → t[i] < e) ∧
      (∀ i (h : i < t.size), lowerBound t e 0 t.size ≤ i → e ≤ t[i]) :=
  lowerBound_spec t ht e _ 0 t.size rfl (Nat.zero_le _) (Nat.le_refl _)
    (fun _ _ h ↦ absurd h (Nat.not_lt_zero _)) (fun _ h h' ↦ absurd h (by omega))

/-- **The binary search counts the entries below `e`.** -/
theorem countP_lt_lowerBound (t : Array ℕ) (ht : Ascends t) (e : ℕ) :
    t.toList.countP (fun x ↦ decide (x < e)) = lowerBound t e 0 t.size := by
  obtain ⟨hr, hlt, hge⟩ := lowerBound_full t ht e
  set r := lowerBound t e 0 t.size
  rw [← List.take_append_drop r t.toList, List.countP_append,
    List.countP_eq_length.2 (fun x hx ↦ ?_), List.countP_eq_zero.2 (fun x hx ↦ ?_)]
  · simp only [List.length_take, Array.length_toList]; omega
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp only [List.getElem_drop, Array.getElem_toList, decide_eq_true_eq, Nat.not_lt]
    exact hge _ (by simp at hi; omega) (by omega)
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp only [List.getElem_take, Array.getElem_toList, decide_eq_true_eq]
    exact hlt _ _ (by simp at hi; omega)

/-- A list sorted ascending, as an array. -/
theorem monotone_toArray {l : List ℕ} (hl : l.Pairwise (· ≤ ·)) : Ascends l.toArray := by
  intro i j hi hj hij
  rcases Nat.eq_or_lt_of_le hij with rfl | hlt
  · exact Nat.le_refl _
  · simpa using List.pairwise_iff_getElem.1 hl i j (by simpa using hi) (by simpa using hj) hlt

/-- **Counting by two binary searches**: the entries in `[a, b)` are those below `b` less those
below `a`, on any list. -/
theorem countP_Ico (l : List ℕ) (a b : ℕ) :
    l.countP (fun x ↦ decide (a ≤ x ∧ x < b)) =
      l.countP (fun x ↦ decide (x < b)) - l.countP (fun x ↦ decide (x < a)) := by
  by_cases hab : a ≤ b
  · have : l.countP (fun x ↦ decide (x < b)) =
        l.countP (fun x ↦ decide (x < a)) + l.countP (fun x ↦ decide (a ≤ x ∧ x < b)) := by
      induction l with
      | nil => rfl
      | cons x l ih =>
        simp only [List.countP_cons, decide_eq_true_eq]
        split_ifs <;> omega
    omega
  · rw [List.countP_eq_zero.2 (fun x _ ↦ by simp; omega)]
    have := List.countP_mono_left (l := l) (p := fun x ↦ decide (x < b))
      (q := fun x ↦ decide (x < a)) (fun x _ h ↦ by simp at h ⊢; omega)
    omega

/-! ## The coverage table: the pairs `(mark, slot)` sorted -/

section Cover

attribute [local instance] lexOrd

theorem compare_pair_lt {a b : ℕ × ℕ} (h : compare a b = .lt) : a.1 ≤ b.1 ∧ (a.1 = b.1 → a.2 < b.2) := by
  rw [show compare a b = (compare a.1 b.1).then (compare a.2 b.2) from rfl,
    Ordering.then_eq_lt, Nat.compare_eq_lt, Nat.compare_eq_eq, Nat.compare_eq_lt] at h
  omega

/-- A key added with the value `0` (the key holds the slot). -/
def coverInsert (m : SortedMap (ℕ × ℕ) ℕ) (p : ℕ × ℕ) : SortedMap (ℕ × ℕ) ℕ := m.insert p 0

/-- A level merged into the newer entries. -/
def mergeLevel (acc : List ((ℕ × ℕ) × ℕ)) (l : Level (ℕ × ℕ) ℕ) : List ((ℕ × ℕ) × ℕ) :=
  mergeNewer acc l.entries.toList

/-- A map's levels merged into one list, sorted by key. -/
def flattenLevels (ls : List (Level (ℕ × ℕ) ℕ)) : List ((ℕ × ℕ) × ℕ) := ls.foldl mergeLevel []

/-- The keys of the pairs `ps` sorted: inserted into a sorted map, its levels merged. -/
def coverKeys (ps : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (flattenLevels (ps.foldl coverInsert SortedMap.empty).levels).map Prod.fst

/-- **The coverage table** of the pairs `(mark, slot)`: the marks in ascending order and their
slots (ties by slot). -/
def coverTable (ps : List (ℕ × ℕ)) : Array ℕ × Array ℕ :=
  let ks := coverKeys ps
  ((ks.map Prod.fst).toArray, (ks.map Prod.snd).toArray)

/-- **The first slot holding the mark `e`**, `0` if none: one binary search among the marks. -/
def slotIn (tm ts : Array ℕ) (e : ℕ) : ℕ :=
  let i := lowerBound tm e 0 tm.size
  if tm.getD i 0 = e then ts.getD i 0 else 0

/-- **The number of slots whose marks lie in `[a, b)`**: two binary searches. -/
def countIn (tm : Array ℕ) (a b : ℕ) : ℕ := lowerBound tm b 0 tm.size - lowerBound tm a 0 tm.size

theorem get?_foldl_coverInsert (k : ℕ × ℕ) :
    ∀ (ps : List (ℕ × ℕ)) (m : SortedMap (ℕ × ℕ) ℕ),
      (ps.foldl coverInsert m).get? k = if k ∈ ps then some 0 else m.get? k := by
  intro ps
  induction ps with
  | nil => intro m; simp
  | cons p ps ih =>
    intro m
    rw [List.foldl_cons, ih, coverInsert, SortedMap.get?_insert]
    by_cases hk : k ∈ ps
    · simp [hk]
    · by_cases hp : p = k
      · subst hp; simp
      · have : k ∉ p :: ps := by simp [hk, Ne.symm hp]
        simp [hk, hp, this]

theorem foldl_mergeLevel (k : ℕ × ℕ) :
    ∀ (ls : List (Level (ℕ × ℕ) ℕ)) (acc : List ((ℕ × ℕ) × ℕ)), Ascending acc →
      Ascending (ls.foldl mergeLevel acc) ∧
        lookup (ls.foldl mergeLevel acc) k =
          (lookup acc k).or (ls.findSome? fun l ↦ lookup l.entries.toList k) := by
  intro ls
  induction ls with
  | nil => intro acc h; simp [h]
  | cons l ls ih =>
    intro acc h
    have hm : Ascending (mergeLevel acc l) := ascending_mergeNewer h l.sorted
    obtain ⟨h1, h2⟩ := ih _ hm
    refine ⟨h1, ?_⟩
    rw [List.foldl_cons, h2, mergeLevel, lookup_mergeNewer h, List.findSome?_cons]
    cases lookup acc k <;> cases lookup l.entries.toList k <;> rfl

theorem lookup_eq_none_iff {l : List ((ℕ × ℕ) × ℕ)} {k : ℕ × ℕ} :
    lookup l k = none ↔ ∀ e ∈ l, e.1 ≠ k := by
  simp only [lookup, Option.map_eq_none_iff, List.find?_eq_none, beq_iff_eq,
    Std.LawfulEqOrd.compare_eq_iff_eq]

/-- The flattened map: sorted by key, its keys those inserted. -/
theorem coverKeys_spec (ps : List (ℕ × ℕ)) :
    (coverKeys ps).Pairwise (fun a b ↦ compare a b = .lt) ∧ ∀ k, k ∈ coverKeys ps ↔ k ∈ ps := by
  have hasc := (foldl_mergeLevel (0, 0) (ps.foldl coverInsert SortedMap.empty).levels [] (by
    simp [Ascending])).1
  refine ⟨by simpa [coverKeys, flattenLevels, Ascending, List.pairwise_map] using hasc,
    fun k ↦ ?_⟩
  have h := (foldl_mergeLevel k (ps.foldl coverInsert SortedMap.empty).levels [] (by
    simp [Ascending])).2
  rw [lookup_nil, Option.none_or, ← SortedMap.get?_eq, get?_foldl_coverInsert,
    SortedMap.get?_empty] at h
  simp only [coverKeys, flattenLevels, List.mem_map]
  constructor
  · rintro ⟨e, he, rfl⟩
    by_contra hn
    rw [ite_eq_right_of_eq_false _ _ (eq_false hn), lookup_eq_none_iff] at h
    exact h e he rfl
  · intro hk
    rw [ite_eq_left_of_eq_true _ _ (eq_true hk)] at h
    by_contra hn
    have : lookup (List.foldl mergeLevel [] (ps.foldl coverInsert SortedMap.empty).levels) k =
        none := lookup_eq_none_iff.2 fun e he hek ↦ hn ⟨e, he, hek⟩
    rw [this] at h
    exact absurd h (by simp)

/-- The pairs `(mk s, s)` of a region of `len` slots. -/
def regionPairs (mk : ℕ → ℕ) (len : ℕ) : List (ℕ × ℕ) := (List.range len).map fun s ↦ (mk s, s)

theorem nodup_regionPairs (mk : ℕ → ℕ) (len : ℕ) : (regionPairs mk len).Nodup :=
  List.Nodup.map_on (fun a _ b _ h ↦ by simpa using congrArg Prod.snd h) List.nodup_range

/-- **The sorted keys are the region's pairs**, permuted. -/
theorem coverKeys_perm (mk : ℕ → ℕ) (len : ℕ) :
    (coverKeys (regionPairs mk len)).Perm (regionPairs mk len) := by
  obtain ⟨hs, hm⟩ := coverKeys_spec (regionPairs mk len)
  refine (List.perm_ext_iff_of_nodup ?_ (nodup_regionPairs mk len)).2 hm
  exact hs.imp fun {a b} h hab ↦ by subst hab; simp at h

theorem coverKeys_fst_sorted (ps : List (ℕ × ℕ)) :
    ((coverKeys ps).map Prod.fst).Pairwise (· ≤ ·) :=
  List.pairwise_map.2 ((coverKeys_spec ps).1.imp fun h ↦ (compare_pair_lt h).1)

/-- **Counting by the table**: `countIn` is the number of the region's slots whose marks lie in
`[a, b)`. -/
theorem countIn_coverTable (mk : ℕ → ℕ) (len a b : ℕ) :
    countIn (coverTable (regionPairs mk len)).1 a b =
      ((List.range len).filter fun s ↦ decide (a ≤ mk s ∧ mk s < b)).length := by
  have hmono := monotone_toArray (coverKeys_fst_sorted (regionPairs mk len))
  simp only [countIn, coverTable]
  rw [← countP_lt_lowerBound _ hmono, ← countP_lt_lowerBound _ hmono, List.toList_toArray,
    ← countP_Ico, List.countP_map, ← List.countP_eq_length_filter,
    (coverKeys_perm mk len).countP_eq, regionPairs, List.countP_map]
  rfl

/-- On keys sorted by mark, `slotIn` is the first key of mark `e`'s slot, `0` if none. -/
theorem slotIn_eq_find (K : List (ℕ × ℕ)) (hK : (K.map Prod.fst).Pairwise (· ≤ ·)) (e : ℕ) :
    slotIn (K.map Prod.fst).toArray (K.map Prod.snd).toArray e =
      ((K.find? fun p ↦ decide (p.1 = e)).map Prod.snd).getD 0 := by
  have hmono := monotone_toArray hK
  obtain ⟨hr, hlt, hge⟩ := lowerBound_full _ hmono e
  simp only [slotIn]
  generalize lowerBound (K.map Prod.fst).toArray e 0 (K.map Prod.fst).toArray.size = r at *
  simp only [List.size_toArray, List.length_map, List.getElem_toArray, List.getElem_map] at hr hlt hge
  have hKs : ∀ i j (hi : i < K.length) (hj : j < K.length), i ≤ j → K[i].1 ≤ K[j].1 := by
    intro i j hi hj hij
    have := hmono i j (by simpa using hi) (by simpa using hj) hij
    simp only [List.getElem_toArray, List.getElem_map] at this
    exact this
  have htake : (K.take r).find? (fun p ↦ decide (p.1 = e)) = none := by
    refine List.find?_eq_none.2 (fun x hx ↦ ?_)
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    simp only [List.getElem_take, decide_eq_true_eq]
    have := hlt i (by simp at hi; omega) (by simp at hi; omega)
    omega
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map]
  conv_rhs => rw [← List.take_append_drop r K, List.find?_append, htake, Option.none_or]
  by_cases hrK : r < K.length
  · rw [List.getElem?_eq_getElem hrK, List.drop_eq_getElem_cons hrK, List.find?_cons]
    simp only [Option.map_some, Option.getD_some]
    by_cases hre : K[r].1 = e
    · simp [hre]
    · simp only [hre, decide_false]
      rw [List.find?_eq_none.2 (fun x hx ↦ ?_)]
      · rfl
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
        simp only [List.getElem_drop, decide_eq_true_eq]
        have h1 := hge r hrK (Nat.le_refl _)
        have h2 := hKs r (r + 1 + i) hrK (by simp at hi; omega) (by omega)
        omega
  · rw [List.drop_eq_nil_of_le (by omega), List.getElem?_eq_none (by omega)]
    simp

/-- **The first slot by the table**: `slotIn` is the first of the region's slots holding the
mark `e`, `0` if none. -/
theorem slotIn_coverTable (mk : ℕ → ℕ) (len e : ℕ) :
    slotIn (coverTable (regionPairs mk len)).1 (coverTable (regionPairs mk len)).2 e =
      ((List.range len).find? fun s ↦ decide (mk s = e)).getD 0 := by
  have hsort := (coverKeys_spec (regionPairs mk len)).1
  have hperm := coverKeys_perm mk len
  -- the first pair of mark `e` in the sorted keys is the region's first
  have hfind : (coverKeys (regionPairs mk len)).find? (fun p ↦ decide (p.1 = e)) =
      (regionPairs mk len).find? (fun p ↦ decide (p.1 = e)) := by
    rw [← List.head?_filter, ← List.head?_filter]
    congr 1
    refine List.Perm.eq_of_pairwise (le := fun p q ↦ p.2 < q.2) (fun _ _ _ _ h h' ↦ by omega)
      ?_ ?_ (hperm.filter _)
    · refine List.pairwise_filter.2 (hsort.imp fun {p q} h hp hq ↦ ?_)
      have := compare_pair_lt h
      simp at hp hq
      exact this.2 (by omega)
    · refine List.Pairwise.filter _ ?_
      simp only [regionPairs, List.pairwise_map]
      exact List.pairwise_lt_range
  have hrange : ((List.range len).find? fun s ↦ decide (mk s = e)) =
      ((regionPairs mk len).find? (fun p ↦ decide (p.1 = e))).map Prod.snd := by
    simp [regionPairs, List.find?_map, Option.map_map, Function.comp_def]
  rw [hrange, ← hfind]
  exact slotIn_eq_find _ (coverKeys_fst_sorted _) e

/-- **The slots of the table's entries whose marks lie in `[a, b)`**, in the table's order: one
binary search and a run of the slots. -/
def slotsIn (tm ts : Array ℕ) (a b : ℕ) : List ℕ :=
  (List.range (countIn tm a b)).map fun i ↦ ts.getD (lowerBound tm a 0 tm.size + i) 0

/-- **A child's list's slots by the table** (`B1.Main.kidSlots`): when as many slots hold the mark
`a` as hold a mark of `[a, b)`, the slots of mark `a` (in slot order, the table's ties); else the
slot of each mark `a + j` in turn. -/
def kidSlotsIn (tm ts : Array ℕ) (a b : ℕ) : List ℕ :=
  if countIn tm a (a + 1) = countIn tm a b then slotsIn tm ts a (a + 1)
  else (List.range (countIn tm a b)).map fun j ↦ slotIn tm ts (a + j)

/-- **The slots of one mark by the table**: `slotsIn` of `[a, a + 1)` is the region's slots holding
the mark `a`, in slot order. -/
theorem slotsIn_coverTable (mk : ℕ → ℕ) (len a : ℕ) :
    slotsIn (coverTable (regionPairs mk len)).1 (coverTable (regionPairs mk len)).2 a (a + 1) =
      (List.range len).filter fun s ↦ decide (mk s = a) := by
  have hsort := (coverKeys_spec (regionPairs mk len)).1
  have hperm := coverKeys_perm mk len
  have hmono := monotone_toArray (coverKeys_fst_sorted (regionPairs mk len))
  obtain ⟨hr, hlt, hge⟩ := lowerBound_full _ hmono a
  obtain ⟨hr', hlt', hge'⟩ := lowerBound_full _ hmono (a + 1)
  simp only [slotsIn, countIn, coverTable]
  generalize coverKeys (regionPairs mk len) = K at *
  generalize lowerBound (K.map Prod.fst).toArray a 0 (K.map Prod.fst).toArray.size = r at *
  generalize lowerBound (K.map Prod.fst).toArray (a + 1) 0 (K.map Prod.fst).toArray.size = r' at *
  simp only [List.size_toArray, List.length_map, List.getElem_toArray, List.getElem_map] at hr hlt hge hr' hlt' hge'
  have hrr : r ≤ r' := by
    by_contra hc
    have h1 := hge' r' (by omega) (Nat.le_refl _)
    have h2 := hlt r' (by omega) (by omega)
    omega
  -- the run `[r, r')` of the sorted keys is the keys of mark `a`
  have hmid : (K.drop r).take (r' - r) = K.filter fun p ↦ decide (p.1 = a) := by
    have hsplit : K = K.take r ++ ((K.drop r).take (r' - r) ++ K.drop r') := by
      conv_lhs => rw [← List.take_append_drop r K, ← List.take_append_drop (r' - r) (K.drop r)]
      rw [List.drop_drop, Nat.add_sub_cancel' hrr]
    have h2 : ((K.drop r).take (r' - r)).filter (fun p ↦ decide (p.1 = a)) = (K.drop r).take (r' - r) := by
      refine List.filter_eq_self.2 fun x hx ↦ ?_
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      simp only [List.length_take, List.length_drop] at hi
      simp only [List.getElem_take, List.getElem_drop, decide_eq_true_eq]
      have h1 := hge (r + i) (by omega) (by omega)
      have h2 := hlt' (r + i) (by omega) (by omega)
      omega
    have h3 : (K.drop r').filter (fun p ↦ decide (p.1 = a)) = [] := by
      refine List.filter_eq_nil_iff.2 fun x hx ↦ ?_
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      simp only [List.length_drop] at hi
      simp only [List.getElem_drop, decide_eq_true_eq]
      have := hge' (r' + i) (by omega) (by omega)
      omega
    have h1 : (K.take r).filter (fun p ↦ decide (p.1 = a)) = [] := by
      refine List.filter_eq_nil_iff.2 fun x hx ↦ ?_
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      simp only [List.length_take] at hi
      simp only [List.getElem_take, decide_eq_true_eq]
      have := hlt i (by omega) (by omega)
      omega
    conv_rhs => rw [hsplit]
    rw [List.filter_append, List.filter_append, h1, h2, h3, List.nil_append, List.append_nil]
  -- the keys of mark `a`, sorted, are the region's, in slot order
  have hfil : K.filter (fun p ↦ decide (p.1 = a)) =
      (regionPairs mk len).filter (fun p ↦ decide (p.1 = a)) := by
    refine List.Perm.eq_of_pairwise (le := fun p q ↦ p.2 < q.2) (fun _ _ _ _ h h' ↦ by omega)
      ?_ ?_ (hperm.filter _)
    · refine List.pairwise_filter.2 (hsort.imp fun {p q} h hp hq ↦ ?_)
      have := compare_pair_lt h
      simp at hp hq
      exact this.2 (by omega)
    · refine List.Pairwise.filter _ ?_
      simp only [regionPairs, List.pairwise_map]
      exact List.pairwise_lt_range
  have hlist : (List.range (r' - r)).map (fun i ↦ (K.map Prod.snd).toArray.getD (r + i) 0) =
      ((K.drop r).take (r' - r)).map Prod.snd := by
    refine List.ext_getElem (by simp; omega) (fun i h1 h2 ↦ ?_)
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop,
      Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
      List.getElem?_eq_getElem (show r + i < K.length by omega), Option.map_some, Option.getD_some]
  rw [hlist, hmid, hfil]
  simp [regionPairs, List.filter_map, List.map_map, Function.comp_def]

/-- Under the gap walk's test, the slots of `[a, b)` are those of the mark `a`. -/
theorem filter_Ico_of_length_eq (l : List ℕ) (mk : ℕ → ℕ) (a b : ℕ)
    (h : (l.filter fun s ↦ decide (a ≤ mk s ∧ mk s < a + 1)).length =
      (l.filter fun s ↦ decide (a ≤ mk s ∧ mk s < b)).length) :
    l.filter (fun s ↦ decide (mk s = a)) = l.filter fun s ↦ decide (a ≤ mk s ∧ mk s < b) := by
  have e : l.filter (fun s ↦ decide (mk s = a)) = l.filter fun s ↦ decide (a ≤ mk s ∧ mk s < a + 1) :=
    List.filter_congr fun s _ ↦ by simp only [decide_eq_decide]; omega
  rw [e]
  by_cases hab : a + 1 ≤ b
  · exact (List.monotone_filter_right l (fun s hs ↦ by simp at hs ⊢; omega)).eq_of_length h
  · have h0 : l.filter (fun s ↦ decide (a ≤ mk s ∧ mk s < b)) = [] :=
      List.filter_eq_nil_iff.2 fun s _ ↦ by simp; omega
    rw [h0] at h ⊢
    exact List.length_eq_zero_iff.1 h

/-- **A child's list's slots by the table** are `kidSlots`' scan: the filter over the region in
slot order, or the first slot of each mark. -/
theorem kidSlotsIn_coverTable (mk : ℕ → ℕ) (len a b : ℕ) :
    kidSlotsIn (coverTable (regionPairs mk len)).1 (coverTable (regionPairs mk len)).2 a b =
      if ((List.range len).filter fun s ↦ decide (a ≤ mk s ∧ mk s < a + 1)).length =
          ((List.range len).filter fun s ↦ decide (a ≤ mk s ∧ mk s < b)).length then
        (List.range len).filter fun s ↦ decide (a ≤ mk s ∧ mk s < b)
      else (List.range ((List.range len).filter fun s ↦ decide (a ≤ mk s ∧ mk s < b)).length).map
        fun j ↦ ((List.range len).find? fun s ↦ decide (mk s = a + j)).getD 0 := by
  unfold kidSlotsIn
  rw [countIn_coverTable, countIn_coverTable]
  split_ifs with h
  · rw [slotsIn_coverTable, filter_Ico_of_length_eq _ mk a b h]
  · simp only [slotIn_coverTable]

end Cover

end

end LeanVM.Guest.Fast
