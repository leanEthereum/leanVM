/-
  LeanVM.Guest.B1.Da.Witness

  A LeanDA witness's commitment, vector digest and inner products, as the guest computes them:
  over any cells of the rows and chunks of the vector.
-/

module

public import LeanVM.Guest.B1.Da.Columns
public import LeanVM.Protocol.Compile.Rom.Encoding

/-!
# A witness, as the guest computes it

`commitOf r sym`: the commitment of `r` rows whose cell `b` of row `i` is `sym b i`, as the hash
of the row tree's root (`rowLeafOf`: the row digests, then the zero row's) and the column tree's
over the column roots (`colLeafOf`: the cell digests, then the zero cell's). `commitCodewords_eq`
says LeanDA's commitment is it; `vectorDigest_chain` that the vector digest is the guest's chain
of `12288` compressions over the `128` chunks of the vector; `dot_eq` that a row's inner product is
the sum over the cells of the guest's per-cell products.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Node

@[expose] public section

/-! ## Digests -/

theorem toBytes_injective : Function.Injective Da.toBytes := fun a b h =>
  Compile.Rom.digestBytes_injective (by rw [← toBytes_toList, ← toBytes_toList, h])

section
variable (r : ℕ) (sym : ℕ → ℕ → List K)

/-- The digest of cell `b` of row `i`. -/
def cellDOf (b i : ℕ) : Digest := blake2sBytes ((sym b i).flatMap kBytes)

/-- Leaf `i` of column `b`'s tree: the cell's digest, then the zero cell's. -/
def colLeafOf (b i : ℕ) : Digest := if i < r then cellDOf sym b i else padCellD

/-- Row `i`'s digest: the hash of its prefix cells' digests. -/
def rowDOf (i : ℕ) : Digest := blake2sBytes ((List.range 64).flatMap fun b => digestBytes (cellDOf sym b i))

/-- Leaf `i` of the row tree: the row's digest, then the zero row's. -/
def rowLeafOf (i : ℕ) : Digest := if i < r then rowDOf sym i else padRowD

/-- The row tree's root. -/
def rowRootOf : Digest := nodeD (rowLeafOf r sym) (LeanDa.logPad r) 0

/-- The column tree's root, over the columns' roots. -/
def colRootOf : Digest := nodeD (fun b => nodeD (colLeafOf r sym b) (LeanDa.logPad r) 0) 7 0

/-- The commitment. -/
def commitOf : Digest := hashPair (rowRootOf r sym) (colRootOf r sym)

end

/-- **LeanDA's commitment** of rows whose cells are `sym`. -/
theorem commitCodewords_eq {rows : List (List K)} {sym : ℕ → ℕ → List K} (hr : 1 ≤ rows.length)
    (hcell : ∀ i (hi : i < rows.length), ∀ b < 128, LeanDa.listCell rows[i] b = sym b i) :
    LeanDa.commitCodewords Da.blake2s rows = Da.toBytes (commitOf rows.length sym) := by
  set r := rows.length with hr'
  obtain ⟨hrN, -⟩ := (logPad_iff (lp := LeanDa.logPad r) hr).mp rfl
  have hcd : ∀ i (hi : i < r), ∀ j < 128, LeanDa.listCellDigest Da.blake2s rows[i] j = Da.toBytes (cellDOf sym j i) := by
    intro i hi j hj
    rw [LeanDa.listCellDigest, hcell i hi j hj, Da.blake2s, cellDOf,
      show (sym j i).flatMap LeanDa.kBytes = (sym j i).flatMap kBytes from
        List.flatMap_congr fun a _ => leanDa_kBytes a]
  have hrd : ∀ i (hi : i < r), LeanDa.rowDigest Da.blake2s rows[i] = Da.toBytes (rowDOf sym i) := by
    intro i hi
    rw [LeanDa.rowDigest, LeanDa.payloadCells, Da.blake2s, rowDOf]
    congr 2
    refine List.flatMap_congr fun j hj => ?_
    rw [hcd i hi j (by have := List.mem_range.mp hj; omega), toBytes_toList]
  have hrowTree : LeanDa.treeRoot Da.blake2s (rows.map (LeanDa.rowDigest Da.blake2s) ++
      List.replicate (LeanDa.nPad r - r) (LeanDa.paddingRow Da.blake2s)) = Da.toBytes (rowRootOf r sym) := by
    rw [rowRootOf, ← treeRoot_nodeD]
    congr 1
    apply List.ext_getElem (by simp; rw [← hr']; exact Nat.add_sub_cancel' hrN)
    intro i h1 h2
    simp only [List.length_map, List.length_range] at h2
    by_cases hir : i < r
    · rw [List.getElem_append_left (by simp; omega)]
      simp only [List.getElem_map, List.getElem_range, rowLeafOf, hir, ↓reduceIte]
      exact hrd i hir
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_replicate, List.getElem_map, List.getElem_range, rowLeafOf, hir, ↓reduceIte]
      exact paddingRow_eq
  have hcolTree : LeanDa.treeRoot Da.blake2s ((List.range LeanDa.cellsPerRow).flatMap fun j =>
      (List.range (LeanDa.nPad r)).map fun i =>
        if h : i < r then LeanDa.listCellDigest Da.blake2s rows[i] j else LeanDa.paddingCell Da.blake2s) =
      Da.toBytes (colRootOf r sym) := by
    rw [colRootOf, ← treeRoot_blocks (LeanDa.logPad r) 7 (colLeafOf r sym),
      show LeanDa.cellsPerRow = 2 ^ 7 from rfl, show LeanDa.nPad r = 2 ^ LeanDa.logPad r from rfl]
    congr 1
    refine List.flatMap_congr fun j hj => List.map_congr_left fun i hi => ?_
    have hj' : j < 128 := List.mem_range.mp hj
    by_cases hir : i < r
    · simp only [hir, ↓reduceDIte, colLeafOf, ↓reduceIte]
      exact hcd i hir j hj'
    · simp only [hir, ↓reduceDIte, colLeafOf, ↓reduceIte]
      exact paddingCell_eq
  show Da.blake2s (LeanDa.pairBytes (LeanDa.treeRoot Da.blake2s (rows.map (LeanDa.rowDigest Da.blake2s) ++
    List.replicate (LeanDa.nPad r - r) (LeanDa.paddingRow Da.blake2s)))
    (LeanDa.treeRoot Da.blake2s ((List.range LeanDa.cellsPerRow).flatMap fun j =>
      (List.range (LeanDa.nPad r)).map fun i =>
        if h : i < r then LeanDa.listCellDigest Da.blake2s rows[i] j else LeanDa.paddingCell Da.blake2s))) = _
  rw [hrowTree, hcolTree, blake2s_pairBytes]
  rfl

/-! ## Chunks -/

/-- A list of `m·n` items is its `n` chunks of `m`. -/
theorem flatMap_chunks {α : Type} (l : List α) (m n : ℕ) (h : l.length = m * n) :
    (List.range n).flatMap (fun b => (l.drop (m * b)).take m) = l := by
  induction n generalizing l with
  | zero => simp at h; simp [h]
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    have hl : (l.take (m * n)).length = m * n := by rw [List.length_take]; rw [h]; exact min_eq_left (by nlinarith)
    have e : ∀ b ∈ List.range n, (l.drop (m * b)).take m = ((l.take (m * n)).drop (m * b)).take m := by
      intro b hb
      have hb' := List.mem_range.mp hb
      rw [List.drop_take, List.take_take]
      congr 1
      have : m * b + m ≤ m * n := by nlinarith
      omega
    rw [List.flatMap_congr e, ih _ hl]
    conv_rhs => rw [← List.take_append_drop (m * n) l]
    congr 1
    rw [List.take_of_length_le (by rw [List.length_drop, h]; rw [Nat.mul_succ]; omega)]

theorem length_chunk {α : Type} {l : List α} {m n b : ℕ} (h : l.length = m * n) (hb : b < n) :
    ((l.drop (m * b)).take m).length = m := by
  rw [List.length_take, List.length_drop, h]
  have : m * b + m ≤ m * n := by nlinarith
  omega

/-! ## Inner products -/

/-- **A row's inner product** with the vector, chunk by chunk. -/
theorem dot_eq {vector : List E} {row : List K} {ws : ℕ → List E} {sy : ℕ → List K}
    (hv : vector = (List.range 128).flatMap ws) (hrow : row = (List.range 128).flatMap sy)
    (hwl : ∀ b < 128, (ws b).length = 256) (hsl : ∀ b < 128, (sy b).length = 256) :
    LeanDa.dot (fun x => vector.getD x 0) (fun x => row.getD x 0) =
      ∑ b ∈ Finset.range 128, ∑ k ∈ Finset.range 256, (ws b).getD k 0 * ofK ((sy b).getD k 0) := by
  unfold LeanDa.dot
  rw [Fin.sum_univ_eq_sum_range (fun x => vector.getD x 0 * LeanDa.ι (row.getD x 0)) (2 ^ 15),
    show 2 ^ 15 = 256 * 128 by rfl, sum_range_mul 256]
  refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun k hk => ?_
  have hb' := Finset.mem_range.mp hb
  have hk' := Finset.mem_range.mp hk
  rw [hv, hrow, getD_flatMap_range ws 0 hwl hb' hk', getD_flatMap_range sy 0 hsl hb' hk']
  rfl

/-! ## The vector digest -/

/-- The vector hash's blocks: block `96b + j` is block `j` of chunk `b`. -/
def vecBlocks (ws : ℕ → List E) (i : ℕ) : Fin 4 → E := vxBlocks ((ws (i / 96)).getD · 0) (i % 96)

/-- The vector hash's metadata cells: the running byte count, final at the last block. -/
def vecMd (i : ℕ) : E := metadataCell (64 * (i + 1)) (decide (i + 1 = 12288))

/-- **The vector digest**, as the guest's chain over the `128` chunks. -/
theorem vectorDigest_chain (ws : ℕ → List E) (hwl : ∀ b < 128, (ws b).length = 256) :
    chainRun paramIv (vecBlocks ws) vecMd (96 * 128) =
      blake2sBytes (((List.range 128).flatMap ws).flatMap eBytes) := by
  rw [show 96 * 128 = 12287 + 1 by rfl, chainRun_blocks (blocks := vecBlocks ws) (md := vecMd) (n := 12287)
    (fun j _ r => vxBlocks_canonical _ _ r)
    (fun j hj => by simp only [vecMd]; congr 1; simp only [decide_eq_false_iff_not]; omega) rfl]
  have hbytes : (List.range (12287 + 1)).flatMap (fun j => blockBytes (vecBlocks ws j)) =
      ((List.range 128).flatMap ws).flatMap eBytes := by
    rw [show 12287 + 1 = 96 * 128 by rfl, flatMap_range_mul 96, List.flatMap_assoc]
    refine List.flatMap_congr fun b hb => ?_
    have hb' := List.mem_range.mp hb
    rw [← vx_bytes _ (hwl b hb')]
    refine List.flatMap_congr fun j hj => ?_
    have hj' := List.mem_range.mp hj
    show blockBytes (vxBlocks ((ws ((96 * b + j) / 96)).getD · 0) ((96 * b + j) % 96)) = _
    rw [show (96 * b + j) / 96 = b by omega, show (96 * b + j) % 96 = j by omega]
  rw [hbytes]

/-- Column `b`'s part of the vector hash: its `96` blocks from the state after `96b`. -/
theorem vecChain_col (ws : ℕ → List E) {b : ℕ} (hb : b < 128) :
    chainRun paramIv (vecBlocks ws) vecMd (96 * (b + 1)) =
      chainRun (chainRun paramIv (vecBlocks ws) vecMd (96 * b)) (vxBlocks ((ws b).getD · 0))
        (vxMd (decide (b = 127)) (cvOf b)) 96 := by
  rw [show 96 * (b + 1) = 96 * b + 96 by ring, chainRun_add]
  have hb1 : ∀ i < 96, vecBlocks ws (96 * b + i) = vxBlocks ((ws b).getD · 0) i := fun i hi => by
    show vxBlocks ((ws ((96 * b + i) / 96)).getD · 0) ((96 * b + i) % 96) = _
    rw [show (96 * b + i) / 96 = b by omega, show (96 * b + i) % 96 = i by omega]
  have hm1 : ∀ i < 96, vecMd (96 * b + i) = vxMd (decide (b = 127)) (cvOf b) i := fun i hi => by
    rw [vxMd_counters hb hi]
    show metadataCell (64 * (96 * b + i + 1)) (decide (96 * b + i + 1 = 12288)) = _
    rw [decide_eq_decide.mpr (show 96 * b + i + 1 = 12288 ↔ (b = 127 ∧ i = 95) by omega)]
  exact chainRun_congr 96 hb1 hm1

end
end LeanVM.Guest.B1.Digest
