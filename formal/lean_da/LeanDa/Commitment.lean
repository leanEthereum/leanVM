import LeanDa.Merkle

/-!
# The deployed commitment is the model's

For every hash function `H`, `commitCodewords`, the commitment as the crate computes it on
codewords given as lists, is `commitCells` of the matrix the rows form
(`commitCodewords_eq_commitCells`). A tree built level by level over the leaves `f 0 … f (2^d - 1)`
has the root `merkleRoot H d f` (`treeRoot_map_range`), and the crate lists the leaves the model
indexes: the row digests then the padding rows, and the cell digests column by column.
-/

namespace LeanDa

variable (H : List UInt8 → Digest)

/-! ## Trees built level by level -/

theorem treeLevel_map_range (d : ℕ) (f : ℕ → Digest) :
    treeLevel H ((List.range (2 ^ (d + 1))).map f) = (List.range (2 ^ d)).map (up H f) := by
  have hlen : 2 ^ (d + 1) / 2 = 2 ^ d := by rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)]
  rw [treeLevel, List.length_map, List.length_range, hlen]
  refine List.map_congr_left fun i hi ↦ ?_
  rw [List.mem_range] at hi
  have h1 : 2 * i < 2 ^ (d + 1) := by rw [pow_succ]; omega
  have h2 : 2 * i + 1 < 2 ^ (d + 1) := by rw [pow_succ]; omega
  simp only [up, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h1,
    List.getElem?_range h2, Option.map_some, Option.getD_some]

/-- **A tree built level by level has the model's root.** -/
theorem treeRoot_map_range (d : ℕ) (f : ℕ → Digest) :
    treeRoot H ((List.range (2 ^ d)).map f) = merkleRoot H d f := by
  induction d generalizing f with
  | zero => rw [treeRoot]; simp [merkleRoot]
  | succ d ih =>
    have hlen : ¬((List.range (2 ^ (d + 1))).map f).length ≤ 1 := by
      rw [List.length_map, List.length_range, pow_succ]
      have := Nat.one_le_two_pow (n := d)
      omega
    rw [treeRoot]
    simp only [hlen, ↓reduceIte]
    rw [treeLevel_map_range, ih]
    rfl

/-! ## The leaves -/

theorem ofFn_eq_map_range {α : Type} {n : ℕ} (f : ℕ → α) :
    (List.ofFn fun j : Fin n ↦ f j) = (List.range n).map f :=
  List.ext_getElem (by simp) fun j _ _ ↦ by simp

/-- `(range a).flatMap (fun j ↦ (range b).map (g j))` lists `g` column by column. -/
theorem flatMap_range_map_range (a b : ℕ) (hb : 0 < b) (g : ℕ → ℕ → Digest) :
    (List.range a).flatMap (fun j ↦ (List.range b).map (g j)) =
      (List.range (a * b)).map fun l ↦ g (l / b) (l % b) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [List.range_succ, List.flatMap_append, ih, List.flatMap_singleton, Nat.succ_mul,
      List.range_add, List.map_append, List.map_map]
    congr 1
    refine List.map_congr_left fun i hi ↦ ?_
    rw [List.mem_range] at hi
    simp only [Function.comp_apply]
    rw [show (a * b + i) / b = a by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hi, Nat.zero_add],
      show (a * b + i) % b = i by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]]

theorem listCell_eq {row : List K} (hrow : row.length = 2 ^ logM) {j : ℕ} (hj : j < 128) :
    listCell row j = List.ofFn fun s : Fin 256 ↦ row.getD (256 * j + s) 0 := by
  have hlen : (listCell row j).length = 256 := by
    simp only [listCell, cellSymbols, List.length_take, List.length_drop, hrow, logM]
    omega
  refine List.ext_getElem (by rw [hlen, List.length_ofFn]) fun s h₁ h₂ ↦ ?_
  rw [List.getElem_ofFn]
  simp only [listCell, cellSymbols, List.getElem_take, List.getElem_drop]
  rw [List.getD_eq_getElem _ _ (by rw [hrow, logM]; rw [List.length_ofFn] at h₂; omega)]
  congr 1
  ring

/-- The digest of a cell of a codeword is the model's. -/
theorem listCellDigest_eq {row : List K} (hrow : row.length = 2 ^ logM) {j : ℕ} (hj : j < 128) :
    listCellDigest H row j = cellDigest H fun s : Fin 256 ↦ row.getD (256 * j + s) 0 := by
  rw [listCellDigest, listCell_eq hrow hj]
  rfl

theorem paddingCell_eq : paddingCell H = cellDigest H 0 := by
  rw [paddingCell, cellDigest, cellBytes, show (0 : Cell) = fun _ ↦ 0 from rfl, List.ofFn_const]
  rfl

theorem paddedCell_cellsOfRows (rows : List (List K)) {i j : ℕ} (hi : i < rows.length)
    (hj : j < 128) :
    paddedCell (cellsOfRows rows) i j = fun s : Fin 256 ↦ rows[i].getD (256 * j + s) 0 := by
  funext s
  simp only [paddedCell, hi, hj, and_self, ↓reduceDIte, cellsOfRows, pos]
  rw [show (128 * i + j) / 128 = i by omega, show (128 * i + j) % 128 = j by omega,
    List.getD_eq_getElem _ _ hi]

theorem paddedCell_cellsOfRows_of_le (rows : List (List K)) {i : ℕ} (hi : rows.length ≤ i)
    (j : ℕ) : paddedCell (cellsOfRows rows) i j = 0 := by
  simp only [paddedCell, show ¬(i < rows.length ∧ j < 128) from fun h ↦ by omega, ↓reduceDIte]

theorem rowDigest_eq {rows : List (List K)} (hrows : ∀ row ∈ rows, row.length = 2 ^ logM)
    {i : ℕ} (hi : i < rows.length) : rowDigest H rows[i] = rowLeaves H (cellsOfRows rows) i := by
  rw [rowDigest, rowLeaves, ofFn_eq_map_range (n := 64)
    (fun j ↦ cellDigest H (paddedCell (cellsOfRows rows) i j)), List.flatMap_map, payloadCells]
  congr 1
  rw [List.flatMap_def, List.flatMap_def]
  congr 1
  refine List.map_congr_left fun j hj ↦ ?_
  rw [List.mem_range] at hj
  rw [listCellDigest_eq H (hrows _ (List.getElem_mem hi)) (by omega),
    paddedCell_cellsOfRows rows hi (by omega)]

theorem paddingRow_eq {rows : List (List K)} {i : ℕ} (hi : rows.length ≤ i) :
    paddingRow H = rowLeaves H (cellsOfRows rows) i := by
  simp only [paddingRow, rowLeaves, paddedCell_cellsOfRows_of_le rows hi, paddingCell_eq,
    List.ofFn_const, payloadCells]

theorem rowLeaves_eq (rows : List (List K)) (hrows : ∀ row ∈ rows, row.length = 2 ^ logM) :
    rows.map (rowDigest H) ++ List.replicate (nPad rows.length - rows.length) (paddingRow H) =
      (List.range (2 ^ logPad rows.length)).map (rowLeaves H (cellsOfRows rows)) := by
  have hle := le_nPad rows.length
  change _ = (List.range (nPad rows.length)).map _
  refine List.ext_getElem (by simp only [List.length_append, List.length_map,
    List.length_replicate, List.length_range]; omega) fun i h₁ h₂ ↦ ?_
  rw [List.getElem_map, List.getElem_range]
  by_cases hi : i < rows.length
  · rw [List.getElem_append_left (by simpa using hi), List.getElem_map, rowDigest_eq H hrows hi]
  · rw [List.getElem_append_right (by simpa using hi), List.getElem_replicate,
      paddingRow_eq H (rows := rows) (i := i) (by omega)]

theorem colLeaves_eq (rows : List (List K)) (hrows : ∀ row ∈ rows, row.length = 2 ^ logM) :
    ((List.range cellsPerRow).flatMap fun j ↦ (List.range (nPad rows.length)).map fun i ↦
        if h : i < rows.length then listCellDigest H rows[i] j else paddingCell H) =
      (List.range (2 ^ (7 + logPad rows.length))).map (colLeaves H (cellsOfRows rows)) := by
  have hpos : 0 < nPad rows.length := by unfold nPad; positivity
  rw [flatMap_range_map_range _ _ hpos, cellsPerRow, show 2 ^ (7 + logPad rows.length) =
    128 * nPad rows.length by rw [pow_add]; rfl]
  refine List.map_congr_left fun l hl ↦ ?_
  rw [List.mem_range] at hl
  have hj : l / nPad rows.length < 128 := (Nat.div_lt_iff_lt_mul hpos).mpr hl
  rw [colLeaves]
  split_ifs with hi
  · rw [listCellDigest_eq H (hrows _ (List.getElem_mem hi)) hj, paddedCell_cellsOfRows rows hi hj]
  · rw [paddedCell_cellsOfRows_of_le rows (by omega), paddingCell_eq]

/-! ## The commitment -/

/-- **The deployed commitment is the model's**: on codewords of `2^15` symbols, `commitCodewords`
is `commitCells` of the matrix they form. -/
theorem commitCodewords_eq_commitCells (rows : List (List K))
    (hrows : ∀ row ∈ rows, row.length = 2 ^ logM) :
    commitCodewords H rows = commitCells H (cellsOfRows rows) := by
  rw [commitCodewords, commitCells, rowRoot, colRoot, rowLeaves_eq H rows hrows,
    colLeaves_eq H rows hrows, treeRoot_map_range, treeRoot_map_range]

end LeanDa
