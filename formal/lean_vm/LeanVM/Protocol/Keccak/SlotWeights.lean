/-
  LeanVM.Protocol.Keccak.SlotWeights

  `keccakSlotWeights` and the fold of `keccakOpen` in closed form: the weight a claim puts on
  each (slot, slice), and its multilinear extension at the slot point.
-/

module

public import LeanVM.Protocol.Keccak.Candidate

/-!
# The slot weights

`keccakSlotWeights logSteps claim first count` (the weights of `keccakOpen`) writes, for each
segment `seg < count` and position `j = z + 64ℓ`, the weight `eq(point_P, seg)·w_j` at row
`25(first + seg) + ℓ`, column `z` of a `64 × 64` array of zeros. `slotWeights_getD`: entry `(o, z)`
is `slotW … o z`, the weight of segment `o / 25 - first` at position `64·(o mod 25) + z` on the rows
`25·first ≤ o < 25·(first + count)`, `0` elsewhere. `foldAll_eq`: `keccakOpen`'s fold of the rows
along the slot challenges is the rows' multilinear extension at the slot point, column by column,
which the Rust `open` (`crates/verifier/src/keccak.rs`) computes directly, weighting each
slot's row by `eq_kernel(slot)`.
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Compile Finset

@[expose] public section

/-! ## Arrays of rows -/

/-- Entry `(o, z)` of an array of rows, `0` outside. -/
def rowsF (rows : Array (Array E)) (o z : ℕ) : E := (rows.getD o #[]).getD z 0

/-- Sixty-four rows of sixty-four entries. -/
def Sized (rows : Array (Array E)) : Prop := rows.size = 64 ∧ ∀ o < 64, (rows.getD o #[]).size = 64

theorem modify_getD (rows : Array (Array E)) (i o : ℕ) (f : Array E → Array E) :
    (rows.modify i f).getD o #[] = if i = o ∧ o < rows.size then f (rows.getD o #[])
      else rows.getD o #[] := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases h1 : i = o
  · subst h1
    by_cases h2 : i < rows.size
    · simp [h2]
    · simp [h2]
  · simp [h1]

theorem modify_step {rows : Array (Array E)} (hs : Sized rows) (i z' : ℕ) (x : E) :
    Sized (rows.modify i fun row ↦ row.setIfInBounds z' x) ∧
      ∀ o z, rowsF (rows.modify i fun row ↦ row.setIfInBounds z' x) o z =
        if i = o ∧ z' = z ∧ o < 64 ∧ z < 64 then x else rowsF rows o z := by
  refine ⟨⟨by simp [hs.1], fun o ho ↦ ?_⟩, fun o z ↦ ?_⟩
  · rw [modify_getD]
    split_ifs
    · rw [Array.size_setIfInBounds]; exact hs.2 o ho
    · exact hs.2 o ho
  · rw [rowsF, modify_getD, rowsF]
    by_cases h1 : i = o ∧ o < rows.size
    · rw [ite_eq_left h1, setIfInBounds_getD]
      have ho : o < 64 := hs.1 ▸ h1.2
      rw [hs.2 o ho]
      by_cases h2 : z' = z ∧ z' < 64
      · rw [ite_eq_left h2, ite_eq_left (show i = o ∧ z' = z ∧ o < 64 ∧ z < 64 from
          ⟨h1.1, h2.1, ho, h2.1 ▸ h2.2⟩)]
      · rw [ite_eq_right h2, ite_eq_right (show ¬ (i = o ∧ z' = z ∧ o < 64 ∧ z < 64) from
          fun h ↦ h2 ⟨h.2.1, h.2.1 ▸ h.2.2.2⟩)]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ (i = o ∧ z' = z ∧ o < 64 ∧ z < 64) from
        fun h ↦ h1 ⟨h.1, hs.1 ▸ h.2.2.1⟩)]

/-- The inner loop of `keccakSlotWeights`: one segment's writes, at rows `b .. b + 24`. -/
theorem inner_rows (rows0 : Array (Array E)) (hs : Sized rows0) (b : ℕ) (V : ℕ → E)
    (hb : b + 25 ≤ 64) : ∀ J, J ≤ 1600 →
      Sized ((List.range J).foldl (fun rows j ↦ rows.modify (b + j / 64)
        fun row ↦ row.setIfInBounds (j % 64) (V j)) rows0) ∧
      ∀ o z, rowsF ((List.range J).foldl (fun rows j ↦ rows.modify (b + j / 64)
        fun row ↦ row.setIfInBounds (j % 64) (V j)) rows0) o z =
        if b ≤ o ∧ o < b + 25 ∧ z < 64 ∧ 64 * (o - b) + z < J then V (64 * (o - b) + z)
        else rowsF rows0 o z
  | 0, _ => ⟨hs, fun o z ↦ by simp⟩
  | J + 1, hJ => by
    obtain ⟨hs', hg⟩ := inner_rows rows0 hs b V hb J (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hs'', hg''⟩ := modify_step hs' (b + J / 64) (J % 64) (V J)
    refine ⟨hs'', fun o z ↦ ?_⟩
    rw [hg'', hg]
    by_cases h1 : b + J / 64 = o ∧ J % 64 = z ∧ o < 64 ∧ z < 64
    · rw [ite_eq_left h1, ite_eq_left (by omega)]
      congr 1; omega
    · rw [ite_eq_right h1]
      by_cases h2 : b ≤ o ∧ o < b + 25 ∧ z < 64 ∧ 64 * (o - b) + z < J
      · rw [ite_eq_left h2, ite_eq_left (by omega)]
      · rw [ite_eq_right h2, ite_eq_right (by omega)]

/-- The weight `keccakSlotWeights` puts at row `o`, column `z`. -/
def slotW (segments w : List E) (first count o z : ℕ) : E :=
  if 25 * first ≤ o ∧ o < 25 * (first + count) ∧ z < 64 then
    segments.getD (o / 25 - first) 0 * w.getD (64 * (o % 25) + z) 0 else 0

/-- The outer loop of `keccakSlotWeights`. -/
theorem outer_rows (segments w : List E) (first count : ℕ) (hfc : first + count ≤ 2) :
    ∀ S, S ≤ count →
      Sized ((List.range S).foldl (fun rows segment ↦ (List.range keccakBits).foldl (fun rows j ↦
        rows.modify (25 * (first + segment) + j / 64) fun row ↦
          row.setIfInBounds (j % 64) (segments.getD segment 0 * w.toArray.getD j 0)) rows)
        (Array.replicate 64 (Array.replicate 64 0))) ∧
      ∀ o z, rowsF ((List.range S).foldl (fun rows segment ↦ (List.range keccakBits).foldl
        (fun rows j ↦ rows.modify (25 * (first + segment) + j / 64) fun row ↦
          row.setIfInBounds (j % 64) (segments.getD segment 0 * w.toArray.getD j 0)) rows)
        (Array.replicate 64 (Array.replicate 64 0))) o z = slotW segments w first S o z
  | 0, _ => by
    refine ⟨⟨by simp, fun o ho ↦ ?_⟩, fun o z ↦ ?_⟩
    · simp [Array.getD_eq_getD_getElem?, ho]
    · simp only [List.range_zero, List.foldl_nil, rowsF, slotW]
      rw [ite_eq_right (by omega)]
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      by_cases h : o < 64
      · by_cases h' : z < 64 <;> simp [h, h']
      · simp [h]
  | S + 1, hS => by
    obtain ⟨hs, hg⟩ := outer_rows segments w first count hfc S (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hs', hg'⟩ := inner_rows _ hs (25 * (first + S))
      (fun j ↦ segments.getD S 0 * w.toArray.getD j 0) (by omega) keccakBits le_rfl
    have hk : keccakBits = 1600 := rfl
    refine ⟨hs', fun o z ↦ ?_⟩
    rw [hg', hg, slotW, slotW]
    by_cases h1 : 25 * (first + S) ≤ o ∧ o < 25 * (first + S) + 25 ∧ z < 64 ∧
        64 * (o - 25 * (first + S)) + z < keccakBits
    · rw [ite_eq_left h1, ite_eq_left (by omega), array_getD_toArray]
      have e1 : o / 25 - first = S := by omega
      have e2 : o % 25 = o - 25 * (first + S) := by omega
      rw [e1, e2]
    · rw [ite_eq_right h1]
      by_cases h2 : 25 * first ≤ o ∧ o < 25 * (first + S) ∧ z < 64
      · rw [ite_eq_left h2, ite_eq_left (by omega)]
      · rw [ite_eq_right h2, ite_eq_right (by omega)]

theorem qkeccakSlotBits_eq : qkeccakSlotBits = 6 := by decide

/-- **`keccakSlotWeights` in closed form.** -/
theorem toListRows_getD (A : Array (Array E)) {o : ℕ} (ho : o < A.size) (z : ℕ) :
    ((A.toList.map Array.toList).getD o []).getD z 0 = (A.getD o #[]).getD z 0 := by
  simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, ho]

theorem toListRows_row (A : Array (Array E)) {o : ℕ} (ho : o < A.size) :
    (A.toList.map Array.toList).getD o [] = (A.getD o #[]).toList := by
  simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, ho]

theorem mapRange_getD (f : ℕ → List E) {n i : ℕ} (hi : i < n) :
    ((List.range n).map f).getD i [] = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl

theorem slotWeights_getD (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ)
    (hfc : first + count ≤ 2) {o z : ℕ} (ho : o < 64) :
    ((keccakSlotWeights logSteps claim first count).getD o []).getD z 0 =
      slotW (eqKernel (claim.point.drop (logSteps - 4))) claim.weights first count o z := by
  obtain ⟨hs, hg⟩ := outer_rows (eqKernel (claim.point.drop (logSteps - 4))) claim.weights
    first count hfc count le_rfl
  rw [← hg o z, rowsF]
  unfold keccakSlotWeights
  simp only [qkeccakSlotBits_eq, show (2 : ℕ) ^ 6 = 64 from rfl]
  exact toListRows_getD _ (by rw [hs.1]; exact ho) z

theorem slotWeights_length (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ)
    (hfc : first + count ≤ 2) : (keccakSlotWeights logSteps claim first count).length = 64 := by
  obtain ⟨hs, -⟩ := outer_rows (eqKernel (claim.point.drop (logSteps - 4))) claim.weights
    first count hfc count le_rfl
  unfold keccakSlotWeights
  simp only [qkeccakSlotBits_eq, show (2 : ℕ) ^ 6 = 64 from rfl, List.length_map,
    Array.length_toList]
  exact hs.1

theorem slotWeights_row_length (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ)
    (hfc : first + count ≤ 2) {o : ℕ} (ho : o < 64) :
    ((keccakSlotWeights logSteps claim first count).getD o []).length = 64 := by
  obtain ⟨hs, -⟩ := outer_rows (eqKernel (claim.point.drop (logSteps - 4))) claim.weights
    first count hfc count le_rfl
  unfold keccakSlotWeights
  simp only [qkeccakSlotBits_eq, show (2 : ℕ) ^ 6 = 64 from rfl]
  rw [toListRows_row _ (by rw [hs.1]; exact ho), Array.length_toList]
  exact hs.2 o ho

/-! ## The fold along the slot -/

/-- `keccakOpen`'s fold of the rows along the slot challenges. -/
def foldAll (slot : List E) (rows : List (List E)) : List (List E) :=
  slot.foldl (fun rows challenge ↦
    (List.range (rows.length / 2)).map fun i ↦
      List.zipWith (fun lo hi ↦ lo + challenge * (lo + hi)) (rows.getD (2 * i) [])
        (rows.getD (2 * i + 1) [])) rows

theorem zipWith_getD (f : E → E → E) (l₁ l₂ : List E) {z : ℕ} (h₁ : z < l₁.length)
    (h₂ : z < l₂.length) : (List.zipWith f l₁ l₂).getD z 0 = f (l₁.getD z 0) (l₂.getD z 0) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem h₁,
    List.getElem?_eq_getElem h₂]

/-- **The fold is the multilinear extension**, column by column. -/
theorem foldAll_eq : ∀ (pt : List E) (rows : List (List E)), rows.length = 2 ^ pt.length →
    (∀ o < rows.length, (rows.getD o []).length = 64) →
    (foldAll pt rows).length = 1 ∧ ((foldAll pt rows).headD []).length = 64 ∧
      ∀ z < 64, ((foldAll pt rows).headD []).getD z 0 =
        ∑ o ∈ range (2 ^ pt.length), eqAt pt o * (rows.getD o []).getD z 0
  | [], rows, hl, hr => by
    rcases rows with _ | ⟨r, _ | ⟨r', rs⟩⟩
    · simp at hl
    · exact ⟨rfl, hr 0 (by simp), fun z _ ↦ by simp [foldAll]⟩
    · simp at hl
  | c :: pt, rows, hl, hr => by
    have step : foldAll (c :: pt) rows = foldAll pt ((List.range (rows.length / 2)).map fun i ↦
        List.zipWith (fun lo hi ↦ lo + c * (lo + hi)) (rows.getD (2 * i) [])
          (rows.getD (2 * i + 1) [])) := rfl
    have hl' : rows.length / 2 = 2 ^ pt.length := by
      rw [hl, List.length_cons, pow_succ]; omega
    have hrow : ∀ i < rows.length / 2, ((List.range (rows.length / 2)).map fun i ↦
        List.zipWith (fun lo hi ↦ lo + c * (lo + hi)) (rows.getD (2 * i) [])
          (rows.getD (2 * i + 1) [])).getD i [] =
        List.zipWith (fun lo hi ↦ lo + c * (lo + hi)) (rows.getD (2 * i) [])
          (rows.getD (2 * i + 1) []) := by
      intro i hi
      exact mapRange_getD _ hi
    obtain ⟨h1, h2, h3⟩ := foldAll_eq pt ((List.range (rows.length / 2)).map fun i ↦
        List.zipWith (fun lo hi ↦ lo + c * (lo + hi)) (rows.getD (2 * i) [])
          (rows.getD (2 * i + 1) [])) (by rw [List.length_map, List.length_range, hl'])
      (fun i hi ↦ by
        have hi2 : i < rows.length / 2 := by simpa using hi
        rw [hrow i hi2, List.length_zipWith, hr _ (by omega), hr _ (by omega), min_self])
    rw [step]
    refine ⟨h1, h2, fun z hz ↦ ?_⟩
    rw [h3 z hz, List.length_cons, sum_cube_succ]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi' := Finset.mem_range.1 hi
    rw [← hl'] at hi' 
    rw [hrow i (by omega), zipWith_getD _ _ _ (by rw [hr _ (by omega)]; exact hz)
      (by rw [hr _ (by omega)]; exact hz), eqAt_cons, eqAt_cons]
    have e1 : 2 * i % 2 = 0 := by omega
    have e2 : (2 * i + 1) % 2 = 1 := by omega
    have e3 : 2 * i / 2 = i := by omega
    have e4 : (2 * i + 1) / 2 = i := by omega
    simp only [e1, e2, e3, e4, ite_true, zero_ne_one, ite_false]
    ring

/-- `keccakOpen` (`open`, `keccak.rs`), with the fold named. -/
theorem keccakOpen_eq (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    keccakOpen logSteps claim first count value =
      sumcheck value 3 (List.replicate qkeccakSlotBits none) >>= fun x ↦
        VerifierProgram.ret (x.1, (foldAll x.1 (keccakSlotWeights logSteps claim first
            count)).headD [],
          x.2) := rfl

end
end LeanVM.Protocol.KeccakGkr
