/-
  LeanVM.Guest.B1.Da.DvLoops

  `da_verify`'s loops on its honest buffers: the regions' bases (`da_verify_loop0`), a
  column's cells (`da_verify_column_loop0`), the blobs' trees (`da_verify_loop2`), the padding
  blobs' roots (`da_verify_loop3`), and the tree over the blobs' roots (`da_levels` at the padded
  count).

  `da_verify` checks Benedikt Wagner's LeanDA witnesses (`Da.MatrixWitness.Opens`), as ported here.
-/

module

public import LeanVM.Guest.B1.Da.DvHonest
public import LeanVM.Guest.B1.Da.LoopsComplete
public import LeanVM.Guest.B1.Digest.Steps
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.GuestConst
-- Private: `guest_const%` inserts literals, so importers need not see the guest's source.
import LeanVM.Guest.Data.Source

/-!
# The loops, on the honest buffers

On a memory holding the regions at `g^bb` (`blobsCells`), their bases at `g^bR` (`rowbaseCells`)
and the roots' tree at `g^bT` (`rootsCells`): `l17_rel`, `l19_rel`, `l20_rel` run each loop to its
end, `l21_rel` column `h`'s run over the blobs, its weights at `g^lv`; `dl_rel` the tree over the
roots, returning `daRoot`'s cells. `hreg`: a region's words.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest

@[expose] public section

variable {rd : Reader} {r L : ℕ} {syms : ℕ → ℕ → List E} {z : E} {bb bR bT : ℕ}

/-- **Region `i`'s words**, at its base. -/
theorem hreg (hB : ReadsAt rd (gen ^ bb) (blobsCells r syms z)) {i : ℕ} (hi : i < r) {k : ℕ}
    (hk : k < 641) {v : E} (hv : (regionCells syms z i).getD k 0 = v) :
    LoadHolds rd (gen ^ (bb + 641 * i)) k v :=
  loadHolds_of_reads (readsAt_block (length_regionCells syms z) hB hi)
    (by rw [length_regionCells]; exact hk) hv

/-- Region `i`'s base, at the bases. -/
theorem hbase (hR : ReadsAt rd (gen ^ bR) (rowbaseCells r bb)) {i : ℕ} (hi : i < r) :
    LoadHolds rd (gen ^ bR * gen ^ i) 0 (gen ^ (bb + 641 * i)) := by
  rw [loadHolds_mul_gen_pow]
  exact loadHolds_of_reads hR (by simp [rowbaseCells]; omega) (by simp [rowbaseCells,
    List.getD_eq_getElem?_getD, hi])

theorem gen_pow_pow (i k : ℕ) : (gen ^ i) ^ k = gen ^ (k * i) := by rw [← pow_mul, mul_comm]

/-- **The regions' bases** (`da_verify_loop0`): each base, each running sum's first word zero. -/
theorem l17_rel (hr1 : 1 ≤ r) (hB : ReadsAt rd (gen ^ bb) (blobsCells r syms z))
    (hR : ReadsAt rd (gen ^ bR) (rowbaseCells r bb)) :
    coreProgram.Rel rd name% «da_verify_loop0» [1, gen ^ r, gen ^ bb, gen ^ bR] [] := by
  have := loopF_complete (rd := rd) find_l17 dv_loops_shape.1.1 (N := gen ^ r)
    (rest := [gen ^ bb, gen ^ bR]) (m := r) rfl (fun i hi => l17_block (by
      rw [gen_pow_pow, ← pow_add gen bb]; exact hbase hR hi) (by
      rw [gen_pow_pow, ← pow_add gen bb]
      exact hreg (k := 512) hB hi (by norm_num) (by
        rw [show (512 : ℕ) = 512 + 0 from rfl, regionCells_sum (by norm_num), runSum_zero]))) 0 hr1
  rwa [pow_zero] at this

/-- **Column `h`'s cells** (`da_verify_column_loop0`): each blob's cell checked, its running sum's
step, its
digest at its tree's leaf `h`, the weights read at `g^lv`. -/
theorem l21_rel (hr1 : 1 ≤ r) {h : ℕ} (hh : h < 128) (hsl : ∀ i j, (syms i j).length = 128)
    (hB : ReadsAt rd (gen ^ bb) (blobsCells r syms z))
    (hR : ReadsAt rd (gen ^ bR) (rowbaseCells r bb)) {lv : ℕ}
    (hlv : ReadsAt rd (gen ^ lv) (colWs z h)) :
    coreProgram.Rel rd name% «da_verify_column_loop0» [1, gen ^ r, gen ^ lv, gen ^ bR, gen ^ h,
        gen ^ h * gen ^ h] [] := by
  have := loopF_complete (rd := rd) find_l21 dv_loops_shape.2.2.2.1 (N := gen ^ r)
    (rest := [gen ^ lv, gen ^ bR, gen ^ h, gen ^ h * gen ^ h]) (m := r) rfl (fun i hi => ?_) 0 hr1
  · rwa [pow_zero] at this
  have hc := da_verify_cell_complete rd (gen ^ lv) (syms i h) (colWs z h) (hsl i h)
    (by simp [colWs, LeanDa.cellSymbols]) hlv
  rw [cellRets_eq] at hc
  obtain ⟨hl1, hl2⟩ := regionCells_leaf (syms := syms) (z := z) (i := i) hh
  refine l21_block (base := gen ^ (bb + 641 * i)) (prev := runSum syms z i h) hc (hbase hR hi)
    ?_ ?_ ?_ ?_
  · rw [loadHolds_mul_gen_pow]
    exact hreg hB hi (by omega) (by rw [show h + 512 = 512 + h by ring, regionCells_sum (by omega)])
  · rw [loadHolds_mul_gen_pow]
    exact hreg hB hi (by omega) (by
      rw [show h + 513 = 512 + (h + 1) by ring, regionCells_sum (by omega), runSum_succ])
  · rw [← pow_add, loadHolds_mul_gen_pow]
    exact hreg hB hi (by omega) (by rw [show h + h + 0 = 2 * h by ring, hl1])
  · rw [← pow_add, loadHolds_mul_gen_pow]
    exact hreg hB hi (by omega) (by rw [show h + h + 1 = 2 * h + 1 by ring, hl2])

/-- The roots' tree's leaf words. -/
theorem roots_leaf {i : ℕ} (hi : i < 2 ^ L) :
    (rootsCells r L syms).getD (2 * i) 0 = (digestHalves (blobLeaf r syms i)).1 ∧
      (rootsCells r L syms).getD (2 * i + 1) 0 = (digestHalves (blobLeaf r syms i)).2 := by
  have hl := length_treeCells (length_rootLeaves r L syms)
  have hp : (pairCells (rootLeaves r L syms)).length = 2 * 2 ^ L := by
    rw [length_pairCells, length_rootLeaves]
  have htree : treeCells (rootLeaves r L syms) L = pairCells (rootLeaves r L syms) ++
      (List.range L).flatMap fun l => pairCells (treeLvl (rootLeaves r L syms) (l + 1)) := by
    rw [treeCells, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    rfl
  have hp1 := Nat.one_le_two_pow (n := L)
  have e : ∀ j < 2 * 2 ^ L, (rootsCells r L syms).getD j 0 = (pairCells (rootLeaves r L syms)).getD j 0 := by
    intro j hj
    rw [rootsCells, List.getD_append _ _ _ _ (by rw [hl]; omega), htree,
      List.getD_append _ _ _ _ (by rw [hp]; exact hj)]
  rw [e _ (by omega), e _ (by omega), (pairCells_getD _ i).1, (pairCells_getD _ i).2]
  simp [rootLeaves, hi]

/-- **The blobs' trees** (`da_verify_loop2`): each blob's sum zero after its columns, its tree's
root
written among the roots' leaves. -/
theorem l19_rel (hr1 : 1 ≤ r) (hrL : r ≤ 2 ^ L) (hB : ReadsAt rd (gen ^ bb) (blobsCells r syms z))
    (hR : ReadsAt rd (gen ^ bR) (rowbaseCells r bb)) (hT : ReadsAt rd (gen ^ bT) (rootsCells r L syms))
    (hdot : ∀ i < r, ∑ h ∈ Finset.range 128, ∑ e ∈ Finset.range 128,
      dualAt z (128 * h + e) * (syms i h).getD e 0 = 0) :
    coreProgram.Rel rd name% «da_verify_loop2» [1, gen ^ r, gen ^ bR, gen ^ bT] [] := by
  have := loopF_complete (rd := rd) find_l19 dv_loops_shape.2.1.1 (N := gen ^ r) (rest := [gen ^ bR, gen ^ bT])
    (m := r) rfl (fun i hi => ?_) 0 hr1
  · rwa [pow_zero] at this
  have hlen := length_blobLeaves syms i
  have hregR := readsAt_block (length_regionCells syms z) hB hi
  rw [regionCells, List.append_assoc, readsAt_append] at hregR
  have hc := da_levels_complete 7 (Or.inr rfl) rd (gen ^ (bb + 641 * i)) (blobLeaves syms i)
    (by rw [hlen]; norm_num) (treeMem_of_reads (by rw [hlen]; norm_num)
      hregR.1)
  have hroot : cellRoot 7 (blobLeaves syms i) = digestHalves (blobLeaf r syms i) := by
    rw [blobLeaf, ite_pos' hi, blobLeaves, ← cellRoot_mRoot]
    rfl
  rw [hroot] at hc
  obtain ⟨hl1, hl2⟩ := roots_leaf (r := r) (L := L) (syms := syms) (i := i) (by omega)
  refine l19_block (hbase hR hi) (hreg hB hi (by norm_num) (by
    rw [show (640 : ℕ) = 512 + 128 from rfl, regionCells_sum le_rfl, runSum_full (hdot i hi)])) hc ?_ ?_
  · rw [← pow_add, loadHolds_mul_gen_pow]
    exact loadHolds_of_reads hT (by rw [length_rootsCells]; omega) (by
      rw [show i + i + 0 = 2 * i by ring, hl1])
  · rw [← pow_add, loadHolds_mul_gen_pow]
    exact loadHolds_of_reads hT (by rw [length_rootsCells]; omega) (by
      rw [show i + i + 1 = 2 * i + 1 by ring, hl2])

/-- **The padding blobs' roots** (`da_verify_loop3`). -/
theorem l20_rel (hrL : r < 2 ^ L) (hT : ReadsAt rd (gen ^ bT) (rootsCells r L syms)) :
    coreProgram.Rel rd name% «da_verify_loop3» [1, gen ^ (2 ^ L - r), gen ^ bT, gen ^ r] [] := by
  have := loopF_complete (rd := rd) find_l20 dv_loops_shape.2.2.1.1 (N := gen ^ (2 ^ L - r))
    (rest := [gen ^ bT, gen ^ r]) (m := 2 ^ L - r) rfl (fun d hd => ?_) 0 (by omega)
  · rwa [pow_zero] at this
  obtain ⟨hl1, hl2⟩ := roots_leaf (r := r) (L := L) (syms := syms) (i := r + d) (by omega)
  have hpad : blobLeaf r syms (r + d) = daPadBlobDigest := by rw [blobLeaf, ite_neg' (by omega)]
  rw [hpad] at hl1 hl2
  have hp : gen ^ bT * (gen ^ r * gen ^ r) * (gen ^ d * gen ^ d) = gen ^ bT * gen ^ (2 * (r + d)) := by
    simp only [← pow_add]
    ring_nf
  refine l20_block ?_ ?_
  · rw [hp, loadHolds_mul_gen_pow]
    exact loadHolds_of_reads hT (by rw [length_rootsCells]; omega) (by rw [Nat.add_zero, hl1])
  · rw [hp, loadHolds_mul_gen_pow]
    exact loadHolds_of_reads hT (by rw [length_rootsCells]; omega) hl2

/-- **The tree over the roots** returns `daRoot`'s cells. -/
theorem dl_rel (hL : L ≤ guest_const% DA_LOG_MAX_ROWS) (hT : ReadsAt rd (gen ^ bT) (rootsCells r L syms)) :
    coreProgram.Rel rd (daLevelsName L) [gen ^ bT] (digestCells (daRoot r L syms)) := by
  rw [rootsCells, readsAt_append] at hT
  have hc := da_levels_complete L (Or.inl hL) rd (gen ^ bT) (rootLeaves r L syms) (length_rootLeaves r L syms)
    (treeMem_of_reads (length_rootLeaves r L syms) hT.1)
  rw [rootLeaves, cellRoot_mRoot] at hc
  exact hc

end
end LeanVM.Guest.B1.Da
