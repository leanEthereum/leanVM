module

public import LeanDa.WithHash
import Mathlib.Data.List.GetD

@[expose] public section

/-!
# The deployed commitment is the model's

For every hash function `H`, `commitCodewords`, the commitment as the crate computes it on
codewords given as lists, is `commitCells` of the matrix the rows form
(`commitCodewords_eq_commitCells`). A tree built level by level over the leaves `f 0 … f (2^d - 1)`
has the root `merkleRoot H d f` (`treeRoot_map_range`), and the crate lists the leaves the model
indexes: a codeword's cell digests, a blob's tree, and the blob roots then the padding rows' (the
zero codeword's), the tree over the blob roots.

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

namespace LeanDa

variable (H : List UInt8 → Common.DigestBytes)

/-! ## Trees built level by level -/

theorem treeLevel_map_range (d : ℕ) (f : ℕ → Common.DigestBytes) :
    treeLevelWithHash H ((List.range (2 ^ (d + 1))).map f) = (List.range (2 ^ d)).map (upWithHash H f) := by
  have hlen : 2 ^ (d + 1) / 2 = 2 ^ d := by rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)]
  rw [treeLevelWithHash, List.length_map, List.length_range, hlen]
  refine List.map_congr_left fun i hi ↦ ?_
  rw [List.mem_range] at hi
  have h1 : 2 * i < 2 ^ (d + 1) := by rw [pow_succ]; omega
  have h2 : 2 * i + 1 < 2 ^ (d + 1) := by rw [pow_succ]; omega
  simp only [upWithHash, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h1,
    List.getElem?_range h2, Option.map_some, Option.getD_some]

/-- **A tree built level by level has the model's root.** -/
theorem treeRoot_map_range (d : ℕ) (f : ℕ → Common.DigestBytes) :
    treeRootWithHash H ((List.range (2 ^ d)).map f) = merkleRootWithHash H d f := by
  induction d generalizing f with
  | zero => rw [treeRootWithHash]; simp [merkleRootWithHash]
  | succ d ih =>
    have hlen : ¬((List.range (2 ^ (d + 1))).map f).length ≤ 1 := by
      rw [List.length_map, List.length_range, pow_succ]
      have := Nat.one_le_two_pow (n := d)
      omega
    rw [treeRootWithHash]
    simp only [hlen, ↓reduceIte]
    rw [treeLevel_map_range, ih]
    rfl

/-! ## The leaves -/

theorem listCell_eq {row : List E} (hrow : row.length = 2 ^ logM) {j : ℕ} (hj : j < 128) :
    listCell row j = List.ofFn fun s : Fin 128 ↦ row.getD (128 * j + s) 0 := by
  have hlen : (listCell row j).length = 128 := by
    simp only [listCell, cellSymbols, List.length_take, List.length_drop, hrow, logM]
    omega
  refine List.ext_getElem (by rw [hlen, List.length_ofFn]) fun s h₁ h₂ ↦ ?_
  rw [List.getElem_ofFn]
  simp only [listCell, cellSymbols, List.getElem_take, List.getElem_drop]
  rw [List.getD_eq_getElem _ _ (by rw [hrow, logM]; rw [List.length_ofFn] at h₂; omega)]
  congr 1
  ring

/-- The digest of a cell of a codeword is the model's. -/
theorem listCellDigest_eq {row : List E} (hrow : row.length = 2 ^ logM) {j : ℕ} (hj : j < 128) :
    listCellDigestWithHash H row j = cellDigestWithHash H fun s : Fin 128 ↦ row.getD (128 * j + s) 0 := by
  rw [listCellDigestWithHash, listCell_eq hrow hj]
  rfl

theorem paddingCell_eq : paddingCellWithHash H = cellDigestWithHash H 0 := by
  rw [paddingCellWithHash, cellDigestWithHash, cellBytes, show (0 : Cell) = fun _ ↦ 0 from rfl, List.ofFn_const]
  rfl

theorem paddedCell_cellsOfRows (rows : List (List E)) {i j : ℕ} (hi : i < rows.length)
    (hj : j < 128) :
    paddedCell (cellsOfRows rows) i j = fun s : Fin 128 ↦ rows[i].getD (128 * j + s) 0 := by
  funext s
  simp only [paddedCell, hi, hj, and_self, ↓reduceDIte, cellsOfRows, cellPosition]
  rw [show (128 * i + j) / 128 = i by omega, show (128 * i + j) % 128 = j by omega,
    List.getD_eq_getElem _ _ hi]

theorem paddedCell_cellsOfRows_of_le (rows : List (List E)) {i : ℕ} (hi : rows.length ≤ i)
    (j : ℕ) : paddedCell (cellsOfRows rows) i j = 0 := by
  simp only [paddedCell, show ¬(i < rows.length ∧ j < 128) from fun h ↦ by omega, ↓reduceDIte]

/-- A codeword's blob root, its tree built level by level, is the model's. -/
theorem listBlobRoot_eq {rows : List (List E)} (hrows : ∀ row ∈ rows, row.length = 2 ^ logM)
    {i : ℕ} (hi : i < rows.length) :
    listBlobRootWithHash H rows[i] = blobRootWithHash H (cellsOfRows rows) i := by
  rw [listBlobRootWithHash, blobRootWithHash, ← treeRoot_map_range, show cellsPerRow = 2 ^ 7 from rfl]
  refine congrArg _ (List.map_congr_left fun j hj ↦ ?_)
  rw [List.mem_range] at hj
  rw [cellLeavesWithHash, listCellDigest_eq H (hrows _ (List.getElem_mem hi)) (by omega),
    paddedCell_cellsOfRows rows hi (by omega)]

/-- The zero codeword's blob root is a padding row's. -/
theorem paddingBlobRoot_eq {rows : List (List E)} {i : ℕ} (hi : rows.length ≤ i) :
    paddingBlobRootWithHash H = blobRootWithHash H (cellsOfRows rows) i := by
  rw [paddingBlobRootWithHash, blobRootWithHash, ← treeRoot_map_range,
    show cellsPerRow = 2 ^ 7 from rfl, show List.replicate (2 ^ 7) (paddingCellWithHash H) =
      (List.range (2 ^ 7)).map fun _ ↦ paddingCellWithHash H by simp]
  refine congrArg _ (List.map_congr_left fun j _ ↦ ?_)
  rw [cellLeavesWithHash, paddedCell_cellsOfRows_of_le rows hi, paddingCell_eq]

/-- The crate's blob roots, then the padding rows', are the model's leaves of the tree over the
blob roots. -/
theorem blobRoots_eq (rows : List (List E)) (hrows : ∀ row ∈ rows, row.length = 2 ^ logM)
    (hle : rows.length ≤ maxRows) :
    rows.map (listBlobRootWithHash H) ++
        List.replicate (maxRows - rows.length) (paddingBlobRootWithHash H) =
      (List.range (2 ^ logMaxRows)).map (blobRootWithHash H (cellsOfRows rows)) := by
  change _ = (List.range maxRows).map _
  refine List.ext_getElem (by simp only [List.length_append, List.length_map,
    List.length_replicate, List.length_range]; omega) fun i h₁ h₂ ↦ ?_
  rw [List.getElem_map, List.getElem_range]
  by_cases hi : i < rows.length
  · rw [List.getElem_append_left (by simpa using hi), List.getElem_map, listBlobRoot_eq H hrows hi]
  · rw [List.getElem_append_right (by simpa using hi), List.getElem_replicate,
      paddingBlobRoot_eq H (rows := rows) (i := i) (by omega)]

/-! ## The commitment -/

/-- **The deployed commitment is the model's**: on codewords of `2^14` symbols, `commitCodewords`
is `commitCells` of the matrix they form. -/
theorem commitCodewords_eq_commitCells (rows : List (List E))
    (hrows : ∀ row ∈ rows, row.length = 2 ^ logM) (hle : rows.length ≤ maxRows) :
    commitCodewordsWithHash H rows = commitCellsWithHash H (cellsOfRows rows) := by
  rw [commitCodewordsWithHash, commitCellsWithHash, blobRoots_eq H rows hrows hle, treeRoot_map_range]

end LeanDa
