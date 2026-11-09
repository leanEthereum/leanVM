module

public import LeanVM.Cost.Bounds.ListLib
public import LeanVM.Cost.Bounds.Guest.Basic
public import LeanVM.Cost.Bounds.SortedMap
public import LeanVM.Cost.Decoder.Kids
import all LeanVM.Protocol.Extraction.Fast.SortedMap

/-!
# Bounds on the guest decoder's prices: the coverage table's searches

The searches of `Guest/Fast/Search.lean`, compiled in `Cost/Decoder/Kids.lean`, at the decoder's
sizes (every count, mark and slot below `2^34`):

* **`lowerBound_cost`**: a binary search over at most `2^34` entries, at most `lowerBoundPrice =
  915`; `slotIn_cost`, `countIn_cost`: one or two of them;
* the coverage table's sorted map at keys `(mark, slot)` (`mergeNewerCover_cost`,
  `levelMergeCover_cost`, `carryCover_amortized`: `Bounds/SortedMap.lean`'s amortized insertion),
  its insertions (`coverFold_cost`), its levels merged (`flattenLevels_cost`), **`coverTable_cost`**:
  at most `coverTablePrice N = 5405·N + 813` for `N ≤ 2^34` pairs;
* `TableGood`: what the searches need of a table (its marks sorted, both arrays of one size at
  most `2^34`, the entries below `2^34`); `coverTable_good` gives it for every list of fewer
  than `2^34` pairs below `2^34`.
-/

namespace LeanVM.Cost.Bounds.Guest

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Parameters
open LeanVM.Extraction.Fast LeanVM.Guest.Fast LeanVM.Cost.Decoder

public section

variable (P : MachineProgram)

/-! ## Binary search -/

/-- The binary search's result lies in `[lo, hi]`. -/
theorem lowerBound_le (t : Array ℕ) (e : ℕ) :
    ∀ n lo hi, hi - lo = n → lo ≤ hi → lo ≤ lowerBound t e lo hi ∧ lowerBound t e lo hi ≤ hi := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro lo hi hn hlh
  rw [lowerBound]
  split
  · split
    · have := ih (hi - ((lo + hi) / 2 + 1)) (by omega) ((lo + hi) / 2 + 1) hi rfl (by omega)
      omega
    · have := ih ((lo + hi) / 2 - lo) (by omega) lo ((lo + hi) / 2) rfl (by omega)
      omega
  · omega

theorem lowerBound_le_size (t : Array ℕ) (e : ℕ) : lowerBound t e 0 t.size ≤ t.size :=
  (lowerBound_le t e _ 0 t.size rfl (Nat.zero_le _)).2

/-- **The binary search's price**: `26` per halving of `[lo, hi)`, `5` at the end. -/
theorem lowerBound_cost_lt (hP : Includes P lowerBoundC.costDeps)
    (t : Array ℕ) (ht : ∀ i, t.getD i 0 < 2 ^ 64) (e : ℕ) (he : e < 2 ^ 64) :
    ∀ k lo hi, lo ≤ hi → hi ≤ 2 ^ 35 → hi - lo < 2 ^ k →
      machineCost P lowerBoundC.costIdx
        [encodeValue t, encodeValue e, encodeValue lo, encodeValue hi] ≤ 5 + 26 * k := by
  intro k
  induction k with
  | zero =>
    intro lo hi hlh hhi hk
    rw [lowerBoundC.costEq P hP]
    have : ¬ lo < hi := by simp at hk; omega
    simp only [this, ↓reduceIte]
    limbs_one
    omega
  | succ k ih =>
    intro lo hi hlh hhi hk
    rw [lowerBoundC.costEq P hP]
    rw [pow_succ] at hk
    have hmid := ht ((lo + hi) / 2)
    split
    · have h1 := ih ((lo + hi) / 2 + 1) hi (by omega) hhi (by omega)
      have h2 := ih lo ((lo + hi) / 2) (by omega) (by omega) (by omega)
      limbs_one
      split <;> omega
    · limbs_one
      omega

/-- The binary search's price over a whole array of at most `2^34` entries. -/
@[expose] def lowerBoundPrice : ℕ := 915

/-- **A binary search over at most `2^34` entries below `2^64`** (`lowerBoundC`, the search `slotInC`,
`countInC` call): at most `lowerBoundPrice = 915`. -/
theorem lowerBound_cost (hP : Includes P lowerBoundC.costDeps)
    (t : Array ℕ) (ht : ∀ i, t.getD i 0 < 2 ^ 64) (hs : t.size ≤ 2 ^ 34) (e : ℕ) (he : e < 2 ^ 64) :
    machineCost P lowerBoundC.costIdx
      [encodeValue t, encodeValue e, encodeValue 0, encodeValue t.size] ≤ lowerBoundPrice := by
  have := lowerBound_cost_lt P hP t ht e he 35 0 t.size (Nat.zero_le _) (by omega) (by omega)
  unfold lowerBoundPrice
  omega

/-- **The first slot holding a mark** (`slotInC`): one search, at most `933`. -/
theorem slotIn_cost (hP : Includes P slotInC.costDeps) (tm ts : Array ℕ)
    (ht : ∀ i, tm.getD i 0 < 2 ^ 64) (hs : tm.size ≤ 2 ^ 34) (e : ℕ) (he : e < 2 ^ 64) :
    machineCost P slotInC.costIdx [encodeValue tm, encodeValue ts, encodeValue e] ≤ 933 := by
  rw [slotInC.costEq P hP]
  have h1 := lowerBound_cost P (by includes) tm ht hs e he
  have h2 := ht (lowerBound tm e 0 tm.size)
  unfold lowerBoundPrice at h1
  limbs_one
  split <;> omega

/-- **The slots whose marks lie in `[a, b)`** (`countInC`): two searches, at most `1843`. -/
theorem countIn_cost (hP : Includes P countInC.costDeps) (tm : Array ℕ)
    (ht : ∀ i, tm.getD i 0 < 2 ^ 64) (hs : tm.size ≤ 2 ^ 34) (a b : ℕ) (ha : a < 2 ^ 64)
    (hb : b < 2 ^ 64) :
    machineCost P countInC.costIdx [encodeValue tm, encodeValue a, encodeValue b] ≤ 1843 := by
  rw [countInC.costEq P hP]
  have := lowerBound_cost P (by includes) tm ht hs a ha
  have := lowerBound_cost P (by includes) tm ht hs b hb
  have := lowerBound_le_size tm a
  have := lowerBound_le_size tm b
  unfold lowerBoundPrice at *
  limbs_one
  omega

theorem countIn_le (tm : Array ℕ) (a b : ℕ) : countIn tm a b ≤ tm.size := by
  unfold countIn
  have := lowerBound_le_size tm b
  omega

/-! ## A child's list's slots -/

section Slots

variable {t : Array ℕ × Array ℕ}

/-- **What the searches need of a coverage table**: both arrays of one size at most `2^34`, their
entries below `2^34` (the marks sorted is not needed for the prices). -/
@[expose] def TableGood (t : Array ℕ × Array ℕ) : Prop :=
  t.1.size = t.2.size ∧ t.1.size ≤ 2 ^ 34 ∧ (∀ i, t.1.getD i 0 < 2 ^ 34) ∧ ∀ i, t.2.getD i 0 < 2 ^ 34

theorem slotIn_lt (ht : TableGood t) (e : ℕ) : slotIn t.1 t.2 e < 2 ^ 34 := by
  unfold slotIn
  dsimp only
  split
  · exact ht.2.2.2 _
  · norm_num

theorem lt64_of_good (ht : TableGood t) (i : ℕ) : t.1.getD i 0 < 2 ^ 64 :=
  lt_trans (ht.2.2.1 i) (by norm_num)

/-- A child's list off the table has at most as many slots as the table. -/
theorem kidSlotsIn_length_le (tm ts : Array ℕ) (a b : ℕ) : (kidSlotsIn tm ts a b).length ≤ tm.size := by
  unfold kidSlotsIn slotsIn
  split
  · simp only [List.length_map, List.length_range]; exact countIn_le tm a (a + 1)
  · simp only [List.length_map, List.length_range]; exact countIn_le tm a b

/-- A child's list's slots off a good table are below `2^34`. -/
theorem kidSlotsIn_lt (ht : TableGood t) (a b : ℕ) : ∀ s ∈ kidSlotsIn t.1 t.2 a b, s < 2 ^ 34 := by
  intro s hs
  unfold kidSlotsIn slotsIn at hs
  split at hs
  · obtain ⟨i, _, rfl⟩ := List.mem_map.1 hs
    exact ht.2.2.2 _
  · obtain ⟨j, _, rfl⟩ := List.mem_map.1 hs
    exact slotIn_lt ht _

/-- The price of a child's list off a table of at most `N` marks. -/
@[expose] def kidSlotsInPrice (N : ℕ) : ℕ := 1000 * N + 6000

/-- **The slots of mark `a`, by the table** (`slotsInC` on `[a, a + 1)`), at most `N` marks: a
count, then a search and a read a slot: at most `967·N + 1876`. -/
theorem slotsIn_cost (hP : Includes P slotsInC.costDeps) (ht : TableGood t) (a : ℕ)
    (ha : a < 2 ^ 40) (N : ℕ) (hN : t.1.size ≤ N) :
    machineCost P slotsInC.costIdx [encodeValue t.1, encodeValue t.2, encodeValue a,
      encodeValue (a + 1)] ≤ 967 * N + 1876 := by
  rw [slotsInC.costEq P hP]
  have hsz := ht.2.1
  have hc := countIn_le t.1 a (a + 1)
  have h0 := countIn_cost P (by includes) t.1 (lt64_of_good ht) ht.2.1 a (a + 1) (by omega)
    (by omega)
  have h1 := rangeLoop_cost P (by includes) (countIn t.1 a (a + 1)) [] (by omega)
  have h2 := map_cost P (by includes) (fun i ↦ t.2.getD (lowerBound t.1 a 0 t.1.size + i) 0)
    (.closure slotsInC.lam0.costIdx [encodeValue t.1, encodeValue t.2, encodeValue a])
    (fun i ↦ RunsApp.of_spec (slotsInC.lam0.costSpec P (by includes) t.1 t.2 a i))
    (lowerBoundPrice + 14) (List.range (countIn t.1 a (a + 1))) (fun i hi ↦ by
      rw [List.mem_range] at hi
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        slotsInC.lam0.costEq P (by includes), List.length_cons, List.length_cons,
        List.length_cons, List.length_nil]
      have := lowerBound_cost P (by includes) t.1 (lt64_of_good ht) ht.2.1 a (by omega)
      have := lowerBound_le_size t.1 a
      limbs_one
      omega)
  rw [List.length_range] at h2
  unfold lowerBoundPrice at h2
  have := Nat.mul_le_mul_left (915 + 14 + 13) (hc.trans hN)
  have := Nat.mul_le_mul_left 15 (hc.trans hN)
  omega

/-- **A child's list's slots, by the table** (`kidSlotsInC`), at most `N` marks, `a, b < 2^40`:
two counts, then the slots of the mark `a` (`slotsIn_cost`) or a search a mark: at most
`kidSlotsInPrice N = 1000·N + 6000`. -/
theorem kidSlotsIn_cost (hP : Includes P kidSlotsInC.costDeps) (ht : TableGood t) (a b : ℕ)
    (ha : a < 2 ^ 40) (hb : b < 2 ^ 40) (N : ℕ) (hN : t.1.size ≤ N) :
    machineCost P kidSlotsInC.costIdx [encodeValue t.1, encodeValue t.2, encodeValue a,
      encodeValue b] ≤ kidSlotsInPrice N := by
  rw [kidSlotsInC.costEq P hP]
  have hsz := ht.2.1
  have hc := countIn_le t.1 a b
  have hc1 := countIn_le t.1 a (a + 1)
  have h0 := countIn_cost P (by includes) t.1 (lt64_of_good ht) ht.2.1 a (a + 1) (by omega)
    (by omega)
  have h1 := countIn_cost P (by includes) t.1 (lt64_of_good ht) ht.2.1 a b (by omega) (by omega)
  have hs := slotsIn_cost P (by includes) ht a ha N hN
  have h2 := rangeLoop_cost P (by includes) (countIn t.1 a b) [] (by omega)
  have h3 := map_cost P (by includes) (fun j ↦ slotIn t.1 t.2 (a + j))
    (.closure kidSlotsInC.lam0.costIdx [encodeValue t.1, encodeValue t.2, encodeValue a])
    (fun j ↦ RunsApp.of_spec (kidSlotsInC.lam0.costSpec P (by includes) t.1 t.2 a j))
    (933 + 9) (List.range (countIn t.1 a b)) (fun j hj ↦ by
      rw [List.mem_range] at hj
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        kidSlotsInC.lam0.costEq P (by includes), List.length_cons, List.length_cons,
        List.length_cons, List.length_nil]
      have := slotIn_cost P (by includes) t.1 t.2 (lt64_of_good ht) ht.2.1 (a + j) (by omega)
      limbs_one
      omega)
  rw [List.length_range] at h3
  have := Nat.mul_le_mul_left (933 + 9 + 13) (hc.trans hN)
  have := Nat.mul_le_mul_left 15 (hc.trans hN)
  unfold kidSlotsInPrice
  limbs_one
  split <;> omega

end Slots

/-! ## The coverage table's sorted map: keys `(mark, slot)` -/

section Cover

attribute [local instance] lexOrd

/-- A key of the coverage table: its mark and its slot word-sized. -/
@[expose] def CoverKey (k : ℕ × ℕ) : Prop := k.1 < 2 ^ 64 ∧ k.2 < 2 ^ 64

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- `mergeNewer` on the coverage keys (`mergeNewerCoverC`): at most `53` per entry and `3`. -/
theorem mergeNewerCover_cost (hP : Includes P mergeNewerCoverC.costDeps) :
    ∀ (n : ℕ) (a b : List ((ℕ × ℕ) × ℕ)), a.length + b.length = n →
      (∀ e ∈ a, CoverKey e.1) → (∀ e ∈ b, CoverKey e.1) →
      machineCost P mergeNewerCoverC.costIdx [encodeValue a, encodeValue b] ≤ 53 * n + 3 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b hn ha hb
  cases a with
  | nil => rw [mergeNewerCoverC.costEq_nil P hP]; omega
  | cons x a =>
    rw [mergeNewerCoverC.costEq_cons P hP]
    cases b with
    | nil => simp only [List.length_cons, List.length_nil] at hn; simp; omega
    | cons y b =>
      dsimp only
      have hx := ha x (by simp)
      have hy := hb y (by simp)
      have h1 := ih (a.length + (b.length + 1)) (by simp at hn; omega) a (y :: b) (by simp)
        (fun e he ↦ ha e (by simp [he])) hb
      have h2 := ih (a.length + b.length) (by simp at hn; omega) a b rfl
        (fun e he ↦ ha e (by simp [he])) (fun e he ↦ hb e (by simp [he]))
      have h3 := ih (a.length + 1 + b.length) (by simp at hn; omega) (x :: a) b (by simp)
        ha (fun e he ↦ hb e (by simp [he]))
      simp only [List.length_cons] at hn h1 h3
      unfold CoverKey at hx hy
      rw [limbs_of_lt hx.1, limbs_of_lt hy.1, limbs_of_lt hx.2, limbs_of_lt hy.2]
      generalize compareOn (fun x ↦ x.1) x.1 y.1 = o1
      generalize compare x.1 y.1 = o2
      cases o1 <;> cases o2 <;> dsimp only <;> (try split_ifs) <;> omega

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- Two levels merged (`levelMergeCoverC`), weights word-sized: at most `60` per entry and `20`. -/
theorem levelMergeCover_cost (hP : Includes P levelMergeCoverC.costDeps)
    (l l' : Level (ℕ × ℕ) ℕ) (hQ : KeysIn CoverKey [l, l'])
    (hw : l.weight < 2 ^ 64) (hw' : l'.weight < 2 ^ 64) :
    machineCost P levelMergeCoverC.costIdx [encodeValue l, encodeValue l'] ≤
      20 + 60 * (l.entries.size + l'.entries.size) := by
  rw [levelMergeCoverC.costEq P hP, limbs_of_lt hw, limbs_of_lt hw']
  have hm := mergeNewerCover_cost P (by includes) _ l.entries.toList l'.entries.toList rfl
    (fun e he ↦ hQ l (by simp) e (by simpa using he))
    (fun e he ↦ hQ l' (by simp) e (by simpa using he))
  have hlen := length_mergeNewer_le l.entries.toList l'.entries.toList
  simp only [Array.length_toList] at hm hlen
  have := limbs_le_two (x := l.weight + l'.weight) (by omega)
  omega

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- **An insertion into the coverage map, amortized** (`carryCoverC`), below `2^D ≤ 2^63`
insertions: `60·D + 35·(levels + 1)` plus the drop of `60` times the potential. -/
theorem carryCover_amortized (hP : Includes P carryCoverC.costDeps) (D : ℕ) (hD : D ≤ 63)
    (m : SortedMap (ℕ × ℕ) ℕ) (hm : smGood m) (hQ : KeysIn CoverKey m.levels)
    (hN : smWeightSum m < 2 ^ D) (l : Level (ℕ × ℕ) ℕ) (hw : l.weight = 1)
    (hs : l.entries.size = 1) (hk : ∀ e ∈ l.entries, CoverKey e.1) :
    machineCost P carryCoverC.costIdx [encodeValue l, encodeValue m.levels] +
        60 * potential D (carry l m.levels) ≤
      60 * potential D m.levels + 60 * D + 35 * (m.levels.length + 1) := by
  have h2D : 2 ^ D ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) hD
  refine insert_amortized CoverKey
    (fun l ls ↦ machineCost P carryCoverC.costIdx [encodeValue l, encodeValue ls]) 35 60
    D ?_ ?_ ?_ m hm hQ hN l hw hs hk
  · intro l _; rw [carryCoverC.costEq_nil P hP]; omega
  · intro l l' ls h1 h2 hne
    rw [carryCoverC.costEq_cons P hP, limbs_of_lt (by omega : l.weight < 2 ^ 64),
      limbs_of_lt (by omega : l'.weight < 2 ^ 64)]
    simp only [hne, ↓reduceIte]
    omega
  · intro l l' ls h1 heq hQ2
    have := levelMergeCover_cost P (by includes) l l' hQ2 (by omega) (by omega)
    rw [carryCoverC.costEq_cons P hP, limbs_of_lt (by omega : l.weight < 2 ^ 64),
      limbs_of_lt (by omega : l'.weight < 2 ^ 64)]
    simp only [heq, ↓reduceIte]
    omega

/-- The coverage map's invariant after some insertions, `r` left: a good map of keys
`CoverKey`, `r` more insertions keeping it below `2^D`. -/
@[expose] def CoverInv (D : ℕ) (m : SortedMap (ℕ × ℕ) ℕ) (r : ℕ) : Prop :=
  smGood m ∧ KeysIn CoverKey m.levels ∧ smWeightSum m + r ≤ 2 ^ D

open LeanVM.Cost.Auto.LeanVM.Extraction.Fast in
/-- **One insertion into the coverage map, amortized** (`coverKeysC.lam1`, `coverInsert`): at
most `60·D + 35·(D + 1) + 27` plus the drop of `60` times the potential. -/
theorem coverStep_amortized (hP : Includes P coverKeysC.lam1.costDeps) (D : ℕ) (hD : D ≤ 63)
    (m : SortedMap (ℕ × ℕ) ℕ) (r : ℕ) (hm : CoverInv D m (r + 1)) (p : ℕ × ℕ) (hp : CoverKey p) :
    CoverInv D (coverInsert m p) r ∧
      machineCost P coverKeysC.lam1.costIdx [encodeValue m, encodeValue p] +
          60 * potential D (coverInsert m p).levels ≤
        60 * potential D m.levels + (60 * D + 35 * (D + 1) + 27) := by
  obtain ⟨hg, hQ, hw⟩ := hm
  have hN : smWeightSum m < 2 ^ D := by omega
  obtain ⟨hlev, -⟩ := smGood_levels_le hg hN
  refine ⟨?_, ?_⟩
  · obtain ⟨h1, h2⟩ := smGood_insert hg p 0
    exact ⟨h1, keysIn_insert hQ hp _, by unfold coverInsert; omega⟩
  · rw [coverKeysC.lam1.costEq P hP, coverInsertC.costEq P (by includes),
      insertCoverC.costEq P (by includes)]
    have hcarry := carryCover_amortized P (by includes) D hD m hg hQ hN
      ⟨1, #[(p, 0)], by simp [Ascending]⟩ rfl rfl (fun e he ↦ by simp at he; rw [he]; exact hp)
    have hins : (coverInsert m p).levels = carry ⟨1, #[(p, 0)], by simp [Ascending]⟩ m.levels := rfl
    rw [hins]
    have := Nat.mul_le_mul_left 35 (show m.levels.length + 1 ≤ D + 1 by omega)
    omega

/-- **The insertions** (`listFoldl` of `coverKeysC.lam1` from the empty map): `n ≤ 2^D` keys, at
most `(60·D + 35·(D + 1) + 38)·n + 3`. -/
theorem coverFold_cost (hP : Includes P coverKeysC.costDeps) (D : ℕ) (hD : D ≤ 63)
    (ps : List (ℕ × ℕ)) (hn : ps.length ≤ 2 ^ D) (hp : ∀ p ∈ ps, CoverKey p) :
    machineCost P listFoldl.costIdx [.closure coverKeysC.lam1.costIdx [],
        encodeValue (SortedMap.empty : SortedMap (ℕ × ℕ) ℕ), encodeValue ps] ≤
      (60 * D + 35 * (D + 1) + 38) * ps.length + 3 := by
  have := listFoldl_amortized P (by includes) coverInsert (.closure coverKeysC.lam1.costIdx [])
    (fun a b ↦ RunsApp.of_spec (coverKeysC.lam1.costSpec P (by includes) a b))
    (60 * D + 35 * (D + 1) + 27) (fun m ↦ 60 * potential D m.levels) (CoverInv D)
    ps SortedMap.empty ⟨smGood_empty, fun _ h ↦ by simp [SortedMap.empty] at h,
      by simp [smWeightSum_empty]; omega⟩
    (fun acc r hacc p hpm ↦ by
      rw [appCost_fn, List.nil_append, List.length_nil]
      exact coverStep_amortized P (by includes) D hD acc r hacc p (hp p hpm))
  have h0 : potential D (SortedMap.empty : SortedMap (ℕ × ℕ) ℕ).levels = 0 := rfl
  simp only [h0, Nat.mul_zero, Nat.zero_add] at this
  nlinarith

/-- The coverage map after the insertions of `ps`: its invariant. -/
theorem coverInv_foldl (D : ℕ) : ∀ (ps : List (ℕ × ℕ)) (m : SortedMap (ℕ × ℕ) ℕ) (r : ℕ),
    CoverInv D m (r + ps.length) → (∀ p ∈ ps, CoverKey p) → CoverInv D (ps.foldl coverInsert m) r := by
  intro ps
  induction ps with
  | nil => intro m r h _; simpa using h
  | cons p ps ih =>
    intro m r h hp
    obtain ⟨hg, hQ, hw⟩ := h
    obtain ⟨h1, h2⟩ := smGood_insert hg p 0
    refine ih (coverInsert m p) r ⟨h1, keysIn_insert hQ (hp p (by simp)) _, ?_⟩
      (fun q hq ↦ hp q (by simp [hq]))
    unfold coverInsert; simp only [List.length_cons] at hw; omega

theorem coverWeight_foldl : ∀ (ps : List (ℕ × ℕ)) (m : SortedMap (ℕ × ℕ) ℕ), smGood m →
    smGood (ps.foldl coverInsert m) ∧
      smWeightSum (ps.foldl coverInsert m) = smWeightSum m + ps.length := by
  intro ps
  induction ps with
  | nil => intro m h; simpa using h
  | cons p ps ih =>
    intro m h
    obtain ⟨h1, h2⟩ := smGood_insert h p 0
    obtain ⟨h3, h4⟩ := ih (coverInsert m p) h1
    refine ⟨h3, ?_⟩
    rw [List.foldl_cons, h4]
    unfold coverInsert
    rw [h2, List.length_cons]
    omega

/-! ### The levels merged -/

/-- A level merged into the accumulator (`flattenLevelsC.lam0`, `mergeLevel`): at most
`56·(|acc| + |l|) + 11`. -/
theorem mergeLevel_cost (hP : Includes P flattenLevelsC.lam0.costDeps)
    (acc : List ((ℕ × ℕ) × ℕ)) (l : Level (ℕ × ℕ) ℕ) (ha : ∀ e ∈ acc, CoverKey e.1)
    (hl : ∀ e ∈ l.entries, CoverKey e.1) :
    machineCost P flattenLevelsC.lam0.costIdx [encodeValue acc, encodeValue l] ≤
      56 * (acc.length + l.entries.size) + 11 := by
  rw [flattenLevelsC.lam0.costEq P hP, mergeLevelC.costEq P (by includes)]
  have := mergeNewerCover_cost P (by includes) _ acc l.entries.toList rfl ha
    (fun e he ↦ hl e (by simpa using he))
  simp only [Array.length_toList] at this
  omega

/-- **The levels merged** (`listFoldl` of `flattenLevelsC.lam0`), the accumulator and the levels
holding at most `N` entries: at most `(56·N + 22)` per level and `3`. -/
theorem flattenFold_cost (hP : Includes P flattenLevelsC.costDeps) (N : ℕ) :
    ∀ (ls : List (Level (ℕ × ℕ) ℕ)) (acc : List ((ℕ × ℕ) × ℕ)),
      acc.length + (ls.map (·.entries.size)).sum ≤ N → (∀ e ∈ acc, CoverKey e.1) →
      KeysIn CoverKey ls →
      machineCost P listFoldl.costIdx
          [.closure flattenLevelsC.lam0.costIdx [], encodeValue acc, encodeValue ls] ≤
        (56 * N + 22) * ls.length + 3 := by
  have hf : ∀ a b, RunsApp P (.closure flattenLevelsC.lam0.costIdx []) [encodeValue a, encodeValue b]
      (encodeValue (mergeLevel a b)) :=
    fun a b ↦ RunsApp.of_spec (flattenLevelsC.lam0.costSpec P (by includes) a b)
  intro ls
  induction ls with
  | nil => intro acc _ _ _; rw [listFoldl.costEq_nil P (by includes) mergeLevel _ hf]; omega
  | cons l ls ih =>
    intro acc hN ha hQ
    rw [listFoldl.costEq_cons P (by includes) mergeLevel _ hf]
    simp only [List.map_cons, List.sum_cons] at hN
    have hl : ∀ e ∈ l.entries, CoverKey e.1 := hQ l (by simp)
    have h1 := mergeLevel_cost P (by includes) acc l ha hl
    have hlen := length_mergeNewer_le acc l.entries.toList
    simp only [Array.length_toList] at hlen
    have h2 := ih (mergeLevel acc l) (by unfold mergeLevel; omega)
      (fun e he ↦ by
        rcases mem_mergeNewer he with h | h
        · exact ha e h
        · exact hl e (by simpa using h))
      (fun l' hl' ↦ hQ l' (by simp [hl']))
    rw [appCost_fn, List.nil_append, List.length_nil]
    simp only [List.length_cons]
    rw [Nat.mul_add, Nat.mul_one]
    have : acc.length + l.entries.size ≤ N := by omega
    generalize (56 * N + 22) * ls.length = X at *
    omega

theorem length_flatten_le : ∀ (ls : List (Level (ℕ × ℕ) ℕ)) (acc : List ((ℕ × ℕ) × ℕ)),
    (ls.foldl mergeLevel acc).length ≤ acc.length + (ls.map (·.entries.size)).sum
  | [], acc => by simp
  | l :: ls, acc => by
    rw [List.foldl_cons]
    have h1 := length_flatten_le ls (mergeLevel acc l)
    have h2 := length_mergeNewer_le acc l.entries.toList
    simp only [List.map_cons, List.sum_cons]
    simp only [Array.length_toList] at h2
    have h3 : (mergeLevel acc l).length = (mergeNewer acc l.entries.toList).length := rfl
    omega

/-- **The coverage keys sorted** (`coverKeysC`): `N ≤ 2^34` pairs, at most `5373·N + 793`. -/
theorem coverKeys_cost (hP : Includes P coverKeysC.costDeps) (ps : List (ℕ × ℕ))
    (hn : ps.length ≤ 2 ^ 34) (hp : ∀ p ∈ ps, CoverKey p) :
    machineCost P coverKeysC.costIdx [encodeValue ps] ≤ 5373 * ps.length + 793 := by
  rw [coverKeysC.costEq P hP]
  have h1 := coverFold_cost P (by includes) 35 (by norm_num) ps (by omega) hp
  have hinv := coverInv_foldl 35 ps SortedMap.empty 0
    ⟨smGood_empty, fun _ h ↦ by simp [SortedMap.empty] at h, by rw [smWeightSum_empty]; omega⟩
    hp
  obtain ⟨hg, hQ, -⟩ := hinv
  have hwt := (coverWeight_foldl ps SortedMap.empty smGood_empty).2
  rw [smWeightSum_empty, Nat.zero_add] at hwt
  have hN : smWeightSum (ps.foldl coverInsert SortedMap.empty) < 2 ^ 35 := by omega
  obtain ⟨hlev, -⟩ := smGood_levels_le hg hN
  have hent := smEntryCount_le hg
  unfold smEntryCount at hent
  have h2 := flattenFold_cost P (by includes) ps.length
    (ps.foldl coverInsert SortedMap.empty).levels [] (by rw [List.length_nil]; omega) (by simp) hQ
  rw [flattenLevelsC.costEq P (by includes)]
  -- the keys: one projection per entry of the flattened list
  have hflat : (flattenLevels (ps.foldl coverInsert SortedMap.empty).levels).length ≤ ps.length := by
    have := length_flatten_le (ps.foldl coverInsert SortedMap.empty).levels []
    rw [List.length_nil, Nat.zero_add] at this
    unfold flattenLevels; omega
  have h3 := map_cost P (by includes) (Prod.fst : (ℕ × ℕ) × ℕ → ℕ × ℕ)
    (.closure coverKeysC.lam0.costIdx [])
    (fun a ↦ RunsApp.of_spec (coverKeysC.lam0.costSpec P (by includes) a)) 2
    (flattenLevels (ps.foldl coverInsert SortedMap.empty).levels)
    (fun a _ ↦ by rw [appCost_fn, List.nil_append, coverKeysC.lam0.costEq P (by includes), List.length_nil])
  have := Nat.mul_le_mul_right (56 * ps.length + 22) hlev
  nlinarith

theorem length_coverKeys_le (ps : List (ℕ × ℕ)) : (coverKeys ps).length ≤ ps.length := by
  obtain ⟨hg, hwt⟩ := coverWeight_foldl ps SortedMap.empty smGood_empty
  rw [smWeightSum_empty, Nat.zero_add] at hwt
  have hent := smEntryCount_le hg
  unfold smEntryCount at hent
  have := length_flatten_le (ps.foldl coverInsert SortedMap.empty).levels []
  rw [List.length_nil, Nat.zero_add] at this
  unfold coverKeys flattenLevels
  rw [List.length_map]
  omega

/-- **The coverage table's price** for `N` pairs. -/
@[expose] def coverTablePrice (N : ℕ) : ℕ := 5405 * N + 813

/-- **The coverage table** (`coverTableC`): `N ≤ 2^34` pairs of word-sized marks and slots, at
most `coverTablePrice N = 5405·N + 813`. -/
theorem coverTable_cost (hP : Includes P coverTableC.costDeps) (ps : List (ℕ × ℕ))
    (hn : ps.length ≤ 2 ^ 34) (hp : ∀ p ∈ ps, CoverKey p) :
    machineCost P coverTableC.costIdx [encodeValue ps] ≤ coverTablePrice ps.length := by
  rw [coverTableC.costEq P hP]
  have h1 := coverKeys_cost P (by includes) ps hn hp
  have hK := length_coverKeys_le ps
  have h2 := map_cost P (by includes) (Prod.fst : ℕ × ℕ → ℕ) (.closure coverTableC.lam0.costIdx [])
    (fun a ↦ RunsApp.of_spec (coverTableC.lam0.costSpec P (by includes) a)) 2 (coverKeys ps)
    (fun a _ ↦ by rw [appCost_fn, List.nil_append, coverTableC.lam0.costEq P (by includes), List.length_nil])
  have h3 := map_cost P (by includes) (Prod.snd : ℕ × ℕ → ℕ) (.closure coverTableC.lam1.costIdx [])
    (fun a ↦ RunsApp.of_spec (coverTableC.lam1.costSpec P (by includes) a)) 2 (coverKeys ps)
    (fun a _ ↦ by rw [appCost_fn, List.nil_append, coverTableC.lam1.costEq P (by includes), List.length_nil])
  simp only [List.length_map]
  unfold coverTablePrice
  omega

theorem getD_lt_of_mem {l : List ℕ} {B : ℕ} (h : ∀ x ∈ l, x < B) (hB : 0 < B) (i : ℕ) :
    l.toArray.getD i 0 < B := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray]
  cases hi : l[i]? with
  | none => simpa using hB
  | some x => exact h x (List.mem_of_getElem? hi)

/-- **The coverage table of pairs below `2^34`**, at most `2^34` of them, is good. -/
theorem coverTable_good (ps : List (ℕ × ℕ)) (hn : ps.length ≤ 2 ^ 34)
    (hp : ∀ p ∈ ps, p.1 < 2 ^ 34 ∧ p.2 < 2 ^ 34) : TableGood (coverTable ps) := by
  have hmem := (coverKeys_spec ps).2
  have hK := length_coverKeys_le ps
  refine ⟨by simp [coverTable], by simp [coverTable]; omega, ?_, ?_⟩
  · exact getD_lt_of_mem (fun x hx ↦ by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
      exact (hp k ((hmem k).1 hk)).1) (by norm_num)
  · exact getD_lt_of_mem (fun x hx ↦ by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
      exact (hp k ((hmem k).1 hk)).2) (by norm_num)

end Cover

end

end LeanVM.Cost.Bounds.Guest
