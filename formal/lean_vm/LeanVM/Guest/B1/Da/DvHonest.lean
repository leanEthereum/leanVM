/-
  LeanVM.Guest.B1.Da.DvHonest

  The words an honest run of `da_verify` (G:4509-4547) leaves in its buffers, as functions of the
  cells' symbols and the challenge: each blob's region (its tree over its cells' digests, its
  running sum), the regions' bases, the tree over the blobs' roots.

  `da_verify` checks Benedikt Wagner's LeanDA witnesses (`Da.MatrixWitness.Opens`), as ported here.
-/

module

public import LeanVM.Guest.B1.Da.VerifyMath
public import LeanVM.Guest.B1.Da.AtBase
public import LeanVM.Guest.B1.Da.CellComplete
public import LeanVM.Guest.B1.Da.LevelsComplete
public import LeanVM.Guest.B1.Da.Help

/-!
# `da_verify`'s honest words

For `r` blobs of cells `syms i h` (`128` symbols each) padded to `2^L`, the challenge `z`:

* `colWs z h`: column `h`'s weights, the dual codeword on the cell `h` (`dualAt z (128 h + e)`);
  `cellDot syms z i h`: cell `(i, h)`'s dot product with them; `runSum syms z i h`: blob `i`'s
  running sum after `h` columns.
* `blobLeaves syms i`: blob `i`'s leaves, its cells' digests; `regionCells syms z i`: its region,
  `641` words: the tree over its leaves (`510`), two zeros, the running sums `0 … 128`.
* `blobsCells`, `rowbaseCells bb`, `rootsCells`: `da_verify`'s three buffers (the regions, their
  bases `g^(bb + 641 i)`, the tree over the blob roots and the padding blobs' roots).
* `readsAt_block`: a block of a buffer of equal blocks; `runSum_succ`, `runSum_zero`,
  `runSum_full` (orthogonality).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest

@[expose] public section

section
variable (r L : ℕ) (syms : ℕ → ℕ → List E) (z : E)

/-- Column `h`'s weights: the dual codeword on the cell `h`. -/
def colWs (h : ℕ) : List E := (List.range 128).map fun e => dualAt z (128 * h + e)

/-- Cell `(i, h)`'s dot product with its column's weights. -/
def cellDot (i h : ℕ) : E :=
  ((List.range LeanDa.cellSymbols).map fun e => (colWs z h).getD e 0 * (syms i h).getD e 0).sum

/-- Blob `i`'s running sum after `h` columns. -/
def runSum (i h : ℕ) : E := ((List.range h).map (cellDot syms z i)).sum

/-- Blob `i`'s leaves: its cells' digests. -/
def blobLeaves (i : ℕ) : List (E × E) := (List.range 128).map fun h => digestHalves (cellD syms i h)

/-- **Blob `i`'s region**: the tree over its leaves, two zeros, its running sums. -/
def regionCells (i : ℕ) : List E :=
  treeCells (blobLeaves syms i) 7 ++ [0, 0] ++ (List.range 129).map (runSum syms z i)

/-- The regions of the `r` blobs, `641` words each. -/
def blobsCells : List E := (List.range r).flatMap (regionCells syms z)

/-- The regions' bases at `bb`. -/
def rowbaseCells (bb : ℕ) : List E := (List.range r).map fun i => gen ^ (bb + 641 * i)

/-- The blob roots and the padding blobs' roots. -/
def rootLeaves : List (E × E) := (List.range (2 ^ L)).map fun i => digestHalves (blobLeaf r syms i)

/-- **The tree over the blob roots**, `4·2^L` words. -/
def rootsCells : List E := treeCells (rootLeaves r L syms) L ++ [0, 0]

end

theorem length_blobLeaves (syms : ℕ → ℕ → List E) (i : ℕ) : (blobLeaves syms i).length = 128 := by
  simp [blobLeaves]

theorem length_regionCells (syms : ℕ → ℕ → List E) (z : E) (i : ℕ) :
    (regionCells syms z i).length = 641 := by
  rw [regionCells, List.length_append, List.length_append,
    length_treeCells (by rw [length_blobLeaves]; norm_num)]
  simp

theorem length_blobsCells (r : ℕ) (syms : ℕ → ℕ → List E) (z : E) :
    (blobsCells r syms z).length = 641 * r := by
  rw [blobsCells, length_flatMap_range _ 641 r (length_regionCells syms z), mul_comm]

theorem length_rootLeaves (r L : ℕ) (syms : ℕ → ℕ → List E) : (rootLeaves r L syms).length = 2 ^ L := by
  simp [rootLeaves]

theorem length_rootsCells (r L : ℕ) (syms : ℕ → ℕ → List E) : (rootsCells r L syms).length = 4 * 2 ^ L := by
  rw [rootsCells, List.length_append, length_treeCells (length_rootLeaves r L syms)]
  have := Nat.one_le_two_pow (n := L)
  simp only [List.length_cons, List.length_nil]
  omega

/-! ## Reading blocks -/

/-- **A block of a buffer of equal blocks**: block `i` of `(range n).flatMap f` at `g^(b + m i)`. -/
theorem readsAt_block {rd : Reader} {b m n : ℕ} {f : ℕ → List E} (hf : ∀ j, (f j).length = m)
    (h : ReadsAt rd (gen ^ b) ((List.range n).flatMap f)) {i : ℕ} (hi : i < n) :
    ReadsAt rd (gen ^ (b + m * i)) (f i) := by
  intro k hk
  have hk' : k < m := by rw [hf i] at hk; exact hk
  have hlen := length_flatMap_range f m n hf
  have hmi : m * i + k < m * n := by
    calc m * i + k < m * i + m := by omega
      _ = m * (i + 1) := by ring
      _ ≤ m * n := Nat.mul_le_mul_left _ hi
  have hmi' : m * i + k < n * m := by rw [Nat.mul_comm n m]; exact hmi
  have hl := h (m * i + k) (by rw [hlen]; exact hmi')
  have hv : ((List.range n).flatMap f)[m * i + k]'(by rw [hlen]; exact hmi') = (f i)[k] := by
    rw [← List.getD_eq_getElem _ 0, ← List.getD_eq_getElem _ 0]
    exact flatMap_getD f m hf 0 n i k hi hk'
  rw [hv] at hl
  rw [pow_add, loadHolds_mul_gen_pow]
  exact hl

/-- Word `k` of a buffer read at its base. -/
theorem loadHolds_of_reads {rd : Reader} {p : E} {xs : List E} (h : ReadsAt rd p xs) {k : ℕ}
    (hk : k < xs.length) {v : E} (hv : xs.getD k 0 = v) : LoadHolds rd p k v := by
  rw [← hv, List.getD_eq_getElem _ _ hk]
  exact h k hk

/-! ## The running sums -/

section
variable {syms : ℕ → ℕ → List E} {z : E}

theorem runSum_zero (i : ℕ) : runSum syms z i 0 = 0 := by simp [runSum]

theorem runSum_succ (i h : ℕ) : runSum syms z i (h + 1) = runSum syms z i h + cellDot syms z i h := by
  simp [runSum, List.range_succ]

/-- **A blob orthogonal to the dual codeword has running sum zero after its `128` columns.** -/
theorem runSum_full {i : ℕ}
    (hdot : ∑ h ∈ Finset.range 128, ∑ e ∈ Finset.range 128,
      dualAt z (128 * h + e) * (syms i h).getD e 0 = 0) :
    runSum syms z i 128 = 0 := by
  rw [runSum, list_sum_range]
  refine (Finset.sum_congr rfl fun h hh => ?_).trans hdot
  rw [cellDot, list_sum_range]
  refine Finset.sum_congr rfl fun e he => ?_
  have he' := Finset.mem_range.mp he
  simp [colWs, List.getD_eq_getElem?_getD, he']

/-- **A cell's check returns its digest's cells and its dot product.** -/
theorem cellRets_eq (i h : ℕ) :
    cellRets (syms i h) (colWs z h) = digestCells (cellD syms i h) ++ [cellDot syms z i h] := rfl

/-! ## Words of a region -/

theorem regionCells_leaf {i h : ℕ} (hh : h < 128) :
    (regionCells syms z i).getD (2 * h) 0 = (digestHalves (cellD syms i h)).1 ∧
      (regionCells syms z i).getD (2 * h + 1) 0 = (digestHalves (cellD syms i h)).2 := by
  have hl := length_treeCells (k := 7) (length_blobLeaves syms i)
  have hp : (pairCells (blobLeaves syms i)).length = 256 := by
    rw [length_pairCells, length_blobLeaves]
  have htree : treeCells (blobLeaves syms i) 7 = pairCells (blobLeaves syms i) ++
      (List.range 7).flatMap fun l => pairCells (treeLvl (blobLeaves syms i) (l + 1)) := by
    rw [treeCells, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    rfl
  have e : ∀ j < 256, (regionCells syms z i).getD j 0 = (pairCells (blobLeaves syms i)).getD j 0 := by
    intro j hj
    rw [regionCells, List.append_assoc, List.getD_append _ _ _ _ (by rw [hl]; omega), htree,
      List.getD_append _ _ _ _ (by rw [hp]; exact hj)]
  rw [e _ (by omega), e _ (by omega), (pairCells_getD _ h).1, (pairCells_getD _ h).2]
  simp [blobLeaves, hh]

theorem regionCells_sum {i h : ℕ} (hh : h ≤ 128) :
    (regionCells syms z i).getD (512 + h) 0 = runSum syms z i h := by
  have hl := length_treeCells (k := 7) (length_blobLeaves syms i)
  rw [regionCells, List.getD_append_right _ _ _ _ (by simp [hl])]
  simp [hl, List.getD_eq_getElem?_getD, show h < 129 by omega]

end

end
end LeanVM.Guest.B1.Da
