module

/-!
# A map in sorted arrays

The extractor's replay and lookups need a map that grows one key at a time. `SortedMap` keeps its
entries in levels, each an array sorted by key (strictly, so a key occurs once per level), newest
first, the levels' weights (insertions merged into them) distinct powers of two as in a binary
counter (`carry`). A lookup searches each level by binary search (`searchIn`) and takes the
newest hit. With `n` insertions there are at most `log₂ n + 1` levels, so a lookup costs
`O(log² n)` comparisons and the `n` insertions `O(n log n)` merged entries, worst-case.

* `searchIn_eq`: on an array sorted by key, the binary search is `lookup`, a scan of the entries;
* `lookup_mergeNewer`: two levels merged answer as the newer, then the older;
* **`SortedMap.get?_insert`**: `(m.insert k v).get? k' = if k = k' then some v else m.get? k'`.
-/

namespace LeanVM.Extraction.Fast

public section

variable {α β : Type} [Ord α]

/-- The value of the first entry with key `k`. -/
@[expose] def lookup (l : List (α × β)) (k : α) : Option β :=
  (l.find? fun e ↦ compare e.1 k == .eq).map (·.2)

/-- Entries sorted strictly by key. -/
def Ascending (l : List (α × β)) : Prop := l.Pairwise fun a b ↦ compare a.1 b.1 = .lt

/-- Binary search for `k` among the entries `[lo, hi)` of `t`. -/
@[expose] def searchIn (t : Array (α × β)) (k : α) (lo hi : Nat) : Option β :=
  if lo < hi then
    match t[(lo + hi) / 2]? with
    | none => none
    | some e =>
      match compare e.1 k with
      | .eq => some e.2
      | .lt => searchIn t k ((lo + hi) / 2 + 1) hi
      | .gt => searchIn t k lo ((lo + hi) / 2)
  else none
termination_by hi - lo

/-- Two sorted lists merged; on a key both hold, the entry of the first (the newer) is kept. -/
@[expose] def mergeNewer : List (α × β) → List (α × β) → List (α × β)
  | [], b => b
  | a, [] => a
  | x :: a, y :: b =>
    match compare x.1 y.1 with
    | .lt => x :: mergeNewer a (y :: b)
    | .eq => x :: mergeNewer a b
    | .gt => y :: mergeNewer (x :: a) b

theorem lookup_nil (k : α) : lookup ([] : List (α × β)) k = none := rfl

theorem mem_mergeNewer {a b : List (α × β)} {z : α × β} (h : z ∈ mergeNewer a b) :
    z ∈ a ∨ z ∈ b := by
  induction a, b using mergeNewer.induct with
  | case1 b => simp only [mergeNewer] at h; exact .inr h
  | case2 a ha => simp only [mergeNewer] at h; exact .inl h
  | case3 x a y b hc ih =>
    simp only [mergeNewer, hc] at h
    rcases List.mem_cons.1 h with rfl | h
    · exact .inl List.mem_cons_self
    · rcases ih h with h | h
      · exact .inl (List.mem_cons_of_mem _ h)
      · exact .inr h
  | case4 x a y b hc ih =>
    simp only [mergeNewer, hc] at h
    rcases List.mem_cons.1 h with rfl | h
    · exact .inl List.mem_cons_self
    · rcases ih h with h | h
      · exact .inl (List.mem_cons_of_mem _ h)
      · exact .inr (List.mem_cons_of_mem _ h)
  | case5 x a y b hc ih =>
    simp only [mergeNewer, hc] at h
    rcases List.mem_cons.1 h with rfl | h
    · exact .inr List.mem_cons_self
    · rcases ih h with h | h
      · exact .inl h
      · exact .inr (List.mem_cons_of_mem _ h)

variable [Std.TransOrd α] [Std.LawfulEqOrd α]

omit [Std.TransOrd α] in
theorem lookup_cons [DecidableEq α] (x : α × β) (l : List (α × β)) (k : α) :
    lookup (x :: l) k = if x.1 = k then some x.2 else lookup l k := by
  by_cases h : x.1 = k <;> simp [lookup, h]

omit [Std.TransOrd α] in
theorem lookup_eq_none {l : List (α × β)} {k : α} (h : ∀ e ∈ l, e.1 ≠ k) : lookup l k = none := by
  simp only [lookup, Option.map_eq_none_iff, List.find?_eq_none, beq_iff_eq,
    Std.LawfulEqOrd.compare_eq_iff_eq]
  exact h

/-! ## Binary search -/

theorem searchIn_eq_lookup (t : Array (α × β)) (ht : Ascending t.toList) (k : α) :
    ∀ (n lo hi : Nat), hi - lo = n → hi ≤ t.size →
      (∀ i (hi : i < t.size), i < lo → compare t[i].1 k = .lt) →
      (∀ i (hi' : i < t.size), hi ≤ i → compare t[i].1 k = .gt) →
      searchIn t k lo hi = lookup t.toList k := by
  have hsort : ∀ i j (hi : i < t.size) (hj : j < t.size), i < j →
      compare t[i].1 t[j].1 = .lt := by
    intro i j hi hj hij
    have := List.pairwise_iff_getElem.1 ht i j (by simpa using hi) (by simpa using hj) hij
    simpa using this
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro lo hi hn hhi hlo hhi'
  rw [searchIn]
  by_cases hlt : lo < hi
  · simp only [hlt, ↓reduceIte]
    have hmid : (lo + hi) / 2 < t.size := by omega
    rw [Array.getElem?_eq_getElem hmid]
    dsimp only
    cases hc : compare t[(lo + hi) / 2].1 k with
    | eq =>
      have hk : t[(lo + hi) / 2].1 = k := Std.LawfulEqOrd.eq_of_compare hc
      simp only [lookup]
      rw [(List.find?_eq_some_iff_getElem (xs := t.toList) (b := t[(lo + hi) / 2])).2 ⟨by simp [hk],
        (lo + hi) / 2, by simpa using hmid, by simp, fun j hj ↦ ?_⟩]
      · simp
      · have hj' : j < t.size := by omega
        have := hsort j _ hj' hmid hj
        rw [hk] at this
        simp [this]
    | lt =>
      refine ih _ (by omega) _ _ rfl hhi (fun i hi' hil ↦ ?_) hhi'
      by_cases hi'' : i = (lo + hi) / 2
      · subst hi''; exact hc
      · exact Std.TransCmp.lt_trans (hsort i _ hi' hmid (by omega)) hc
    | gt =>
      refine ih _ (by omega) _ _ rfl (by omega) hlo (fun i hi' hil ↦ ?_)
      by_cases hi'' : i = (lo + hi) / 2
      · subst hi''; exact hc
      · have h1 := hsort _ i hmid hi' (by omega)
        rw [Std.OrientedCmp.gt_iff_lt] at hc ⊢
        exact Std.TransCmp.lt_trans hc h1
  · simp only [hlt, ↓reduceIte]
    symm
    refine lookup_eq_none fun e he hk ↦ ?_
    obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem he
    have hi'' : i < t.size := by simpa using hi'
    have hk' : t[i].1 = k := by simpa using hk
    by_cases hil : i < lo
    · have := hlo i hi'' hil
      rw [hk'] at this; simp at this
    · have := hhi' i hi'' (by omega)
      rw [hk'] at this; simp at this

/-- **The binary search is the scan**, on an array sorted by key. -/
theorem searchIn_eq (t : Array (α × β)) (ht : Ascending t.toList) (k : α) :
    searchIn t k 0 t.size = lookup t.toList k :=
  searchIn_eq_lookup t ht k _ 0 t.size rfl (Nat.le_refl _) (fun _ _ h ↦ absurd h (Nat.not_lt_zero _))
    (fun _ h h' ↦ absurd h (by omega))

/-! ## Merging -/

theorem ascending_mergeNewer {a b : List (α × β)} (ha : Ascending a) (hb : Ascending b) :
    Ascending (mergeNewer a b) := by
  induction a, b using mergeNewer.induct with
  | case1 b => simpa [mergeNewer] using hb
  | case2 a _ => simpa [mergeNewer] using ha
  | case3 x a y b hc ih =>
    simp only [Ascending, List.pairwise_cons] at ha hb
    simp only [mergeNewer, hc, Ascending, List.pairwise_cons]
    refine ⟨fun z hz ↦ ?_, ih ha.2 (List.pairwise_cons.2 hb)⟩
    rcases mem_mergeNewer hz with hz | hz
    · exact ha.1 z hz
    · rcases List.mem_cons.1 hz with rfl | hz
      · exact hc
      · exact Std.TransCmp.lt_trans hc (hb.1 z hz)
  | case4 x a y b hc ih =>
    simp only [Ascending, List.pairwise_cons] at ha hb
    simp only [mergeNewer, hc, Ascending, List.pairwise_cons]
    refine ⟨fun z hz ↦ ?_, ih ha.2 hb.2⟩
    rcases mem_mergeNewer hz with hz | hz
    · exact ha.1 z hz
    · have hxy : x.1 = y.1 := Std.LawfulEqOrd.eq_of_compare hc
      rw [hxy]; exact hb.1 z hz
  | case5 x a y b hc ih =>
    simp only [Ascending, List.pairwise_cons] at ha hb
    simp only [mergeNewer, hc, Ascending, List.pairwise_cons]
    have hyx : compare y.1 x.1 = .lt := Std.OrientedCmp.gt_iff_lt.1 hc
    refine ⟨fun z hz ↦ ?_, ih (List.pairwise_cons.2 ha) hb.2⟩
    rcases mem_mergeNewer hz with hz | hz
    · rcases List.mem_cons.1 hz with rfl | hz
      · exact hyx
      · exact Std.TransCmp.lt_trans hyx (ha.1 z hz)
    · exact hb.1 z hz

/-- **Two levels merged answer as the newer, then the older.** -/
theorem lookup_mergeNewer {a b : List (α × β)} (ha : Ascending a) (k : α) :
    lookup (mergeNewer a b) k = (lookup a k).or (lookup b k) := by
  classical
  induction a, b using mergeNewer.induct with
  | case1 b => simp [mergeNewer, lookup_nil]
  | case2 a _ => simp [mergeNewer, lookup_nil]
  | case3 x a y b hc ih =>
    simp only [Ascending, List.pairwise_cons] at ha
    simp only [mergeNewer, hc, lookup_cons, ih ha.2]
    by_cases hk : x.1 = k <;> simp [hk]
  | case4 x a y b hc ih =>
    simp only [Ascending, List.pairwise_cons] at ha
    have hxy : x.1 = y.1 := Std.LawfulEqOrd.eq_of_compare hc
    simp only [mergeNewer, hc]
    rw [lookup_cons x (mergeNewer a b), lookup_cons x a, lookup_cons y b, ih ha.2, hxy]
    by_cases hk : y.1 = k <;> simp [hk]
  | case5 x a y b hc ih =>
    have ha' := ha
    simp only [Ascending, List.pairwise_cons] at ha'
    have hyx : compare y.1 x.1 = .lt := Std.OrientedCmp.gt_iff_lt.1 hc
    simp only [mergeNewer, hc]
    rw [lookup_cons y (mergeNewer (x :: a) b), lookup_cons y b, ih ha]
    by_cases hy : y.1 = k
    · have hnone : lookup (x :: a) k = none := by
        refine lookup_eq_none fun e he hek ↦ ?_
        rcases List.mem_cons.1 he with rfl | he
        · rw [hek, ← hy] at hyx; simp at hyx
        · have := Std.TransCmp.lt_trans hyx (ha'.1 e he)
          rw [hek, ← hy] at this; simp at this
      simp [hy, hnone]
    · simp [hy]

/-! ## Levels -/

/-- A level: its weight and its entries, sorted strictly by key. -/
structure Level (α β : Type) [Ord α] where
  /-- The insertions merged into the level. -/
  weight : Nat
  /-- The entries. -/
  entries : Array (α × β)
  sorted : Ascending entries.toList

/-- Two levels merged, the first the newer. -/
@[expose] def Level.merge (l l' : Level α β) : Level α β :=
  ⟨l.weight + l'.weight, (mergeNewer l.entries.toList l'.entries.toList).toArray,
    by simpa using ascending_mergeNewer l.sorted l'.sorted⟩

/-- A new level `l` on the levels `ls`, merged while its weight is the next one's. -/
@[expose] def carry : Level α β → List (Level α β) → List (Level α β)
  | l, [] => [l]
  | l, l' :: ls => if l.weight = l'.weight then carry (l.merge l') ls else l :: l' :: ls

/-- **A map in sorted arrays**: levels, newest first. -/
structure SortedMap (α β : Type) [Ord α] where
  /-- The levels, newest first. -/
  levels : List (Level α β)

namespace SortedMap

/-- The empty map. -/
@[expose] def empty : SortedMap α β := ⟨[]⟩

/-- The value at `k`: the newest level's that holds `k`. -/
@[expose] def get? (m : SortedMap α β) (k : α) : Option β :=
  m.levels.findSome? fun l ↦ searchIn l.entries k 0 l.entries.size

/-- The value at `k`, or `d`. -/
@[expose] def getD (m : SortedMap α β) (k : α) (d : β) : β := (m.get? k).getD d

/-- Whether `k` has a value. -/
@[expose] def contains (m : SortedMap α β) (k : α) : Bool := (m.get? k).isSome

/-- `m` with `v` at `k`. -/
@[expose] def insert (m : SortedMap α β) (k : α) (v : β) : SortedMap α β :=
  ⟨carry ⟨1, #[(k, v)], by simp [Ascending]⟩ m.levels⟩

theorem get?_eq (m : SortedMap α β) (k : α) :
    m.get? k = m.levels.findSome? fun l ↦ lookup l.entries.toList k := by
  simp only [get?, searchIn_eq _ (Level.sorted _)]

theorem findSome?_carry (l : Level α β) (ls : List (Level α β)) (k : α) :
    (carry l ls).findSome? (fun l ↦ lookup l.entries.toList k) =
      (lookup l.entries.toList k).or (ls.findSome? fun l ↦ lookup l.entries.toList k) := by
  classical
  induction ls generalizing l with
  | nil => simp only [carry, List.findSome?_cons, List.findSome?_nil]; cases lookup l.entries.toList k <;> rfl
  | cons l' ls ih =>
    simp only [carry]
    split
    · rw [ih, Level.merge]
      simp only [List.findSome?_cons]
      rw [lookup_mergeNewer l.sorted]
      cases lookup l.entries.toList k <;> cases lookup l'.entries.toList k <;> rfl
    · simp only [List.findSome?_cons]
      cases lookup l.entries.toList k <;> rfl

omit [Std.TransOrd α] [Std.LawfulEqOrd α] in
@[simp] theorem get?_empty (k : α) : (empty : SortedMap α β).get? k = none := rfl

/-- **The map answers as a function updated at `k`.** -/
theorem get?_insert [DecidableEq α] (m : SortedMap α β) (k k' : α) (v : β) :
    (m.insert k v).get? k' = if k = k' then some v else m.get? k' := by
  rw [get?_eq, insert, findSome?_carry, ← get?_eq]
  simp only [lookup_cons, lookup_nil]
  split <;> simp

theorem contains_insert [DecidableEq α] (m : SortedMap α β) (k k' : α) (v : β) :
    (m.insert k v).contains k' = (decide (k = k') || m.contains k') := by
  simp only [contains, get?_insert]
  split <;> simp_all

omit [Std.TransOrd α] [Std.LawfulEqOrd α] in
@[simp] theorem contains_empty (k : α) : (empty : SortedMap α β).contains k = false := rfl

theorem getD_insert [DecidableEq α] (m : SortedMap α β) (k k' : α) (v d : β) :
    (m.insert k v).getD k' d = if k = k' then v else m.getD k' d := by
  simp only [getD, get?_insert]
  split <;> rfl

omit [Std.TransOrd α] [Std.LawfulEqOrd α] in
@[simp] theorem getD_empty (k : α) (d : β) : (empty : SortedMap α β).getD k d = d := rfl

end SortedMap

end

end LeanVM.Extraction.Fast
