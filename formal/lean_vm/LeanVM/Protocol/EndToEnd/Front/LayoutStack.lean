/-
  LeanVM.Protocol.EndToEnd.Front.LayoutStack

  The verifier's `stack_offsets` and `Placement::stack_point` as statements about sorted
  lists and cube points: the order is the stable sort by size, the offsets are prefix sums of the
  heights in that order, and a placed point is the claim's point between the bits of its index.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.LayoutArith

/-!
# `stack_offsets` and `stack_point`

Facts about the transcriptions of `crates/verifier/src/multilinear.rs` at leanVM `40f877dc`
(`Placement`, `stack_offsets`, `selector_point`), in the form the layout correspondence uses:

* `stackOffsets_eq`: the order of `stack_offsets`, sorted by "larger first, ties by index", is
  the *stable* sort of the indices by size (`mergeSort_range_stackLe`), and the offsets are the
  prefix sums of the heights in that order (`placeFold_getElem?`, `placeFold_snd`);
* `log2Ceil_eq_clog`: `log2_ceil` is `Nat.clog 2`;
* `stackPoint_aligned`, `stackPoint_strided`: a placed point is the claim's point followed by the
  bits of the index above the window, the slot bits below the window for a strided placement.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol.Verifier List

@[expose] public section

/-! ## The order of `stack_offsets` -/

/-- Two indices that occur in both orders in a list without duplicates are equal. -/
theorem eq_of_pair_sublist {L : List ℕ} (hL : L.Nodup) {a b : ℕ} (h1 : [a, b] <+ L)
    (h2 : [b, a] <+ L) : a = b := by
  have key : ∀ {x y}, [x, y] <+ L → x ≠ y → L.idxOf x < L.idxOf y := by
    intro x y h hxy
    obtain ⟨r1, r2, rfl, hx, hy⟩ := List.cons_sublist_iff.mp h
    have hy' : y ∈ r2 := List.singleton_sublist.mp hy
    have hy1 : y ∉ r1 := fun hy1 ↦ List.disjoint_of_nodup_append hL hy1 hy'
    rw [List.idxOf_append_of_mem hx, List.idxOf_append_of_notMem hy1]
    have := List.idxOf_lt_length_of_mem hx
    omega
  by_contra hab
  have := key h1 hab
  have := key h2 (Ne.symm hab)
  omega

/-- Two increasing indices occur in that order in the range. -/
theorem pair_sublist_range {n a b : ℕ} (hab : a < b) (hb : b < n) : [a, b] <+ List.range n := by
  have : List.range n = List.range (a + 1) ++ (List.range (n - (a + 1))).map (a + 1 + ·) := by
    rw [← List.range_add]; congr 1; omega
  rw [this, show [a, b] = [a] ++ [b] from rfl]
  refine List.Sublist.append ?_ ?_
  · exact List.singleton_sublist.mpr (List.mem_range.mpr (by omega))
  · exact List.singleton_sublist.mpr
      (List.mem_map.mpr ⟨b - (a + 1), List.mem_range.mpr (by omega), by omega⟩)

/-- The comparator of `stack_offsets`. -/
def stackLe (size : ℕ → ℕ) (i j : ℕ) : Bool :=
  decide (size j < size i) || (decide (size i = size j) && decide (i ≤ j))

/-- `stack_offsets`' order is the stable sort by size, larger first: breaking ties by index is
what `mergeSort`'s stability does. -/
theorem mergeSort_range_stackLe (size : ℕ → ℕ) (n : ℕ) :
    (List.range n).mergeSort (stackLe size) =
      (List.range n).mergeSort fun i j ↦ decide (size j ≤ size i) := by
  have trans1 : ∀ a b c, stackLe size a b → stackLe size b c → stackLe size a c := by
    intro a b c; simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  have total1 : ∀ a b, stackLe size a b || stackLe size b a := by
    intro a b; simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega
  have trans2 : ∀ a b c : ℕ, decide (size b ≤ size a) → decide (size c ≤ size b) →
      decide (size c ≤ size a) := by
    intro a b c; simp only [decide_eq_true_eq]; omega
  have total2 : ∀ a b : ℕ, decide (size b ≤ size a) || decide (size a ≤ size b) := by
    intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
  apply List.Perm.eq_of_pairwise (le := fun a b ↦ stackLe size a b = true)
  · intro a b _ _ h1 h2
    simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1 h2
    omega
  · exact List.pairwise_mergeSort trans1 total1 _
  · have hs := List.pairwise_mergeSort trans2 total2 (List.range n)
    have hnd : ((List.range n).mergeSort fun i j ↦ decide (size j ≤ size i)).Nodup :=
      (List.mergeSort_perm _ _).nodup_iff.mpr List.nodup_range
    rw [List.pairwise_iff_forall_sublist] at hs ⊢
    intro a b hab
    have hle := hs hab
    simp only [decide_eq_true_eq] at hle
    simp only [stackLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    by_cases hlt : size b < size a
    · exact Or.inl hlt
    · refine Or.inr ⟨by omega, ?_⟩
      by_contra hba
      have hmem := fun x (hx : x ∈ [a, b]) ↦
        (List.mergeSort_perm (List.range n) _).mem_iff.mp (hab.subset hx)
      have hb := List.mem_range.mp (hmem a (by simp))
      have h2 := List.pair_sublist_mergeSort trans2 total2 (by simp only [decide_eq_true_eq]; omega)
        (pair_sublist_range (n := n) (show b < a by omega) hb)
      have := eq_of_pair_sublist hnd hab h2
      omega
  · exact (List.mergeSort_perm _ _).trans (List.mergeSort_perm _ _).symm
/-- The step of `stack_offsets`' fold. -/
def placeStep (w : ℕ → ℕ) (acc : List ℕ × ℕ) (i : ℕ) : List ℕ × ℕ :=
  (acc.1.set i acc.2, acc.2 + w i)

/-- The running total of the fold: the sum of the heights. -/
theorem placeFold_snd (w : ℕ → ℕ) (l : List ℕ) (acc : List ℕ × ℕ) :
    (l.foldl (placeStep w) acc).2 = acc.2 + (l.map w).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih => simp [ih, placeStep]; omega

/-- The fold keeps the length of the offset list. -/
theorem placeFold_length (w : ℕ → ℕ) (l : List ℕ) (acc : List ℕ × ℕ) :
    (l.foldl (placeStep w) acc).1.length = acc.1.length := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih => simp [ih, placeStep]

/-- An index the fold does not visit keeps its entry. -/
theorem placeFold_getElem?_of_not_mem (w : ℕ → ℕ) (l : List ℕ) (acc : List ℕ × ℕ) (i : ℕ)
    (hi : i ∉ l) : (l.foldl (placeStep w) acc).1[i]? = acc.1[i]? := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
    simp only [List.mem_cons, not_or] at hi
    simp only [List.foldl_cons]
    rw [ih _ hi.2]
    simp [placeStep, Ne.symm hi.1]

/-- The offset of the `k`-th index of the order: the running total plus the heights before
it. -/
theorem placeFold_getElem? (w : ℕ → ℕ) (l : List ℕ) (hl : l.Nodup) (acc : List ℕ × ℕ)
    (hlt : ∀ i ∈ l, i < acc.1.length) (k : ℕ) (hk : k < l.length) :
    (l.foldl (placeStep w) acc).1[l[k]]? = some (acc.2 + ((l.take k).map w).sum) := by
  induction l generalizing acc k with
  | nil => simp at hk
  | cons a l ih =>
    simp only [List.foldl_cons]
    rcases k with _ | k
    · simp only [List.getElem_cons_zero, List.take_zero, List.map_nil, List.sum_nil, add_zero]
      rw [placeFold_getElem?_of_not_mem _ _ _ _ (List.nodup_cons.mp hl).1]
      simp [placeStep, hlt a (by simp)]
    · simp only [List.getElem_cons_succ, List.take_succ_cons, List.map_cons, List.sum_cons]
      rw [ih (List.nodup_cons.mp hl).2 _
        (fun i hi ↦ by simpa [placeStep] using hlt i (by simp [hi]))
        k (by simpa using hk)]
      simp [placeStep, add_assoc]

/-- `stack_offsets(sizes)`: the stable sort by size, and the fold of the heights along it. -/
theorem stackOffsets_eq (sizes : List ℕ) :
    stackOffsets sizes =
      let order := (List.range sizes.length).mergeSort
        fun i j ↦ decide (sizes.getD j 0 ≤ sizes.getD i 0)
      let placed := order.foldl (placeStep fun i ↦ 2 ^ sizes.getD i 0)
        (List.replicate sizes.length 0, 0)
      (placed.1, log2Ceil placed.2) := by
  show (_, _) = _
  simp only
  rw [← mergeSort_range_stackLe]
  rfl

/-! ## `log2_ceil` -/

/-- `log2_ceil` is the ceiling logarithm. -/
theorem log2Ceil_eq_clog (t : ℕ) : log2Ceil t = Nat.clog 2 t := by
  rcases Nat.lt_or_ge t 2 with ht | ht
  · interval_cases t <;> rfl
  · have hm : t - 1 ≠ 0 := by omega
    have hL : log2Ceil t = Nat.log2 (t - 1) + 1 := by
      simp [log2Ceil, bitLength, hm]
    have hup : t - 1 < 2 ^ (Nat.log2 (t - 1) + 1) := Nat.lt_log2_self
    have hlo : 2 ^ Nat.log2 (t - 1) ≤ t - 1 := Nat.log2_self_le hm
    rw [hL]
    apply le_antisymm
    · by_contra h
      have h' : Nat.clog 2 t ≤ Nat.log2 (t - 1) := by omega
      rw [Nat.clog_le_iff_le_pow (by norm_num)] at h'
      omega
    · rw [Nat.clog_le_iff_le_pow (by norm_num)]
      omega

/-! ## Placed points -/

/-- Dropping the low `v` coordinates of the cube point of `n` leaves the cube point of
`n / 2 ^ v`. -/
theorem drop_boolPoint (μ v n : ℕ) :
    (boolPoint μ n).drop v = boolPoint (μ - v) (n / 2 ^ v) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_drop, getElem_boolPoint, Nat.testBit_div_two_pow]
  rw [Nat.add_comm]

/-- The low `k` coordinates of the cube point of `n`. -/
theorem take_boolPoint (μ k n : ℕ) (hk : k ≤ μ) :
    (boolPoint μ n).take k = boolPoint k n := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.getElem_take, getElem_boolPoint]

/-- The cube point of `n` on `k` coordinates depends only on `n % 2 ^ k`. -/
theorem boolPoint_mod (k n : ℕ) : boolPoint k (n % 2 ^ k) = boolPoint k n := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [getElem_boolPoint, Nat.testBit_mod_two_pow]
  simp only [length_boolPoint] at h1
  simp [h1]

/-- **A placed point**: the point, then the bits of the index above the window. -/
theorem stackPoint_aligned (v off μ : ℕ) (z : List E) :
    ({ variableCount := v, index := off } : Placement).stackPoint z μ =
      z ++ boolPoint (μ - v) (off / 2 ^ v) := by
  simp [Placement.stackPoint, selectorPoint_eq_boolPoint, Nat.shiftRight_eq_div_pow]

/-- The cube point of `x + 2 ^ a · m`, for `x < 2 ^ a`: the bits of `x`, then those of `m`. -/
theorem boolPoint_add_two_pow_mul (a b x m : ℕ) (hx : x < 2 ^ a) :
    boolPoint (a + b) (x + 2 ^ a * m) = boolPoint a x ++ boolPoint b m := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [length_boolPoint] at h1
  rw [getElem_boolPoint, List.getElem_append]
  rw [show x + 2 ^ a * m = 2 ^ a * m + x by ring, Nat.testBit_two_pow_mul_add m hx]
  by_cases hi : i < a
  · simp only [hi, ↓reduceIte, ↓reduceDIte, length_boolPoint, getElem_boolPoint]
  · simp only [hi, ↓reduceIte, ↓reduceDIte, length_boolPoint, getElem_boolPoint]

/-- **A slice placement** at slot `slot` of an aligned region of `2 ^ (v + k)` cells at `off`
(`index = off + slot · 2 ^ v`): the point, the slot's bits, then the region's bits
above it. -/
theorem stackPoint_slice (v k off slot μ : ℕ) (hk : v + k ≤ μ) (hoff : 2 ^ (v + k) ∣ off)
    (hslot : slot < 2 ^ k) (z : List E) :
    ({ variableCount := v, index := off + slot * 2 ^ v } : Placement).stackPoint z μ =
      z ++ boolPoint k slot ++ boolPoint (μ - (v + k)) (off / 2 ^ (v + k)) := by
  rw [stackPoint_aligned, List.append_assoc]
  congr 1
  obtain ⟨m, rfl⟩ := hoff
  have hdiv : (2 ^ (v + k) * m + slot * 2 ^ v) / 2 ^ v = slot + 2 ^ k * m := by
    rw [pow_add, show 2 ^ v * 2 ^ k * m + slot * 2 ^ v = 2 ^ v * (slot + 2 ^ k * m) by ring,
      Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
  rw [hdiv, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _),
    show μ - v = k + (μ - (v + k)) by omega, boolPoint_add_two_pow_mul _ _ _ _ hslot]

end
end LeanVM.Protocol.EndToEnd.Front
