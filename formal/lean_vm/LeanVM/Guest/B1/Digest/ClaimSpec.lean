/-
  LeanVM.Guest.B1.Digest.ClaimSpec

  The specification side of the claim lists' hashes: the chaining value after whole claim blocks,
  a run of blocks at a byte offset as `ChainCells`, the final block, and the counters the guest
  builds from a window's base by disjoint bits.
-/

module

public import LeanVM.Guest.B1.Digest.ClaimWindow

/-!
# Claim-list hashes, block by block

A claim list is `4n` canonical cells, `n` blocks; its digest is `blake2sBytes` of their bytes
(`claimBytes_eq`). The guest hashes block `k + j` of a run under the metadata cell of the counter
`64·k + 64·(j + 1)`, which it builds as `E(2^11·q) + metadata(64·(j + 1))` for a window's base
(`windowMd_eq`, `baseMd_eq`): `chainCells_prefix` is such a run from the chaining value after
`k` blocks (`prefixDigest`), `final_iff` the last block.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- The chaining value after the first `k` blocks of the cells `cs`. -/
def prefixDigest (cs : List E) (k : ℕ) : Digest :=
  absorbBlocks paramIv 0 ((List.range k).map fun j => blockBytes (blocksOf cs j))

theorem prefixDigest_add (cs : List E) (k m : ℕ) :
    prefixDigest cs (k + m) = absorbBlocks (prefixDigest cs k) (64 * k)
      ((List.range m).map fun j => blockBytes (blocksOf cs (k + j))) := by
  rw [prefixDigest, List.range_add, List.map_append, absorbBlocks_append, List.map_map]
  simp only [List.length_map, List.length_range, Nat.zero_add, prefixDigest]
  rfl

/-- **A run of `m` blocks from block `k`** (`claims_window`, `claims_tail`): from the chaining value
after `k` blocks, under the counters `64·k + 64·(j + 1)`, a `ChainCells` run is exactly canonical
blocks reaching the chaining value after `k + m`. -/
theorem chainCells_prefix {cs : List E} {k m : ℕ} {out : E × E} {b : ℕ → Fin 4 → E} {md : ℕ → E}
    (hb : ∀ j < m, b j = blocksOf cs (k + j))
    (hmd : ∀ j < m, md j = metadataCell (64 * k + 64 * (j + 1)) false) :
    ChainCells (digestScalars (prefixDigest cs k)) b md m out ↔
      (∀ j < m, ∀ r, IsCanonical128 (blocksOf cs (k + j) r)) ∧
        out = digestScalars (prefixDigest cs (k + m)) := by
  have hrun : chainRun (prefixDigest cs k) b md m = prefixDigest cs (k + m) := by
    rw [chainRun_nonfinal m hmd, prefixDigest_add]
    congr 1
    exact List.map_congr_left fun j hj => by rw [hb j (List.mem_range.mp hj)]
  unfold ChainCells
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨-, h, hh, hc, hout⟩)
    · exact ⟨fun j hj => absurd hj (by omega), rfl⟩
    · have := digestScalars_injective hh
      subst this
      refine ⟨fun j hj r => ?_, by rw [hout, hrun]⟩
      rw [← hb j hj]; exact (hc j hj).1 r
  · rintro ⟨hc, hout⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact Or.inl ⟨rfl, hout⟩
    · refine Or.inr ⟨hm, _, rfl, fun j hj => ⟨fun r => ?_, ?_⟩, by rw [hout, hrun]⟩
      · rw [hb j hj]; exact hc j hj r
      · rw [hmd j hj]; exact isCanonical128_metadataCell _ _

/-- A window's counters: `E(2^11·q) + metadata(64·(j + 1))`, `j < 31`, is the counter
`64·32q + 64·(j + 1)`. -/
theorem baseMd_eq (q j : ℕ) (hj : j < 31) :
    baseMd (eOfNat (2 ^ 11 * q)) j = metadataCell (64 * (32 * q) + 64 * (j + 1)) false := by
  rw [baseMd, eOfNat_add_metadataCell, two_pow_mul_xor (by omega)]
  congr 1
  ring

/-- The last counter of a window is the next window's base. -/
theorem eOfNat_next (q : ℕ) :
    eOfNat (2 ^ 11 * (q + 1)) = metadataCell (64 * (32 * q) + 64 * (31 + 1)) false := by
  rw [eOfNat_eq_metadataCell]
  congr 1
  ring

theorem windowMd_eq (q j : ℕ) (hj : j < 32) :
    windowMd (eOfNat (2 ^ 11 * q)) (eOfNat (2 ^ 11 * (q + 1))) j =
      metadataCell (64 * (32 * q) + 64 * (j + 1)) false := by
  unfold windowMd
  split_ifs with h
  · exact baseMd_eq q j h
  · rw [show j = 31 by omega]; exact eOfNat_next q

/-- The bytes of `4n` cells are their `n` blocks'. -/
theorem flatMap_cellBytes_blocks (cs : List E) (n : ℕ) (hlen : cs.length = 4 * n) :
    cs.flatMap cellBytes = (List.range n).flatMap fun j => blockBytes (blocksOf cs j) := by
  rw [← flatMap_range_getD cs 0 cellBytes, hlen, flatMap_range_mul 4]
  refine List.flatMap_congr fun j _ => ?_
  simp [blockBytes, blocksOf, List.range_succ, List.append_assoc]

/-- **The last block** (`claim_list_digest`, G:2797-2798): from the chaining value after `n - 1`
blocks, the last block at the total length with the final flag gives the digest of the cells. -/
theorem final_iff {cs : List E} {n : ℕ} (hlen : cs.length = 4 * n) (hn : 1 ≤ n)
    (hcan : ∀ r, IsCanonical128 (blocksOf cs (n - 1) r)) {d0 d1 : E} :
    CompressCells (blocksOf cs (n - 1)) (digestScalars (prefixDigest cs (n - 1))).1
        (digestScalars (prefixDigest cs (n - 1))).2 d0 d1 (metadataCell (64 * n) true) ↔
      (d0, d1) = digestScalars (blake2sBytes (cs.flatMap cellBytes)) := by
  rw [compressCells_iff hcan (isCanonical128_metadataCell _ _), unpackMetadata_metadataCell,
    flatMap_cellBytes_blocks cs n hlen]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.flatMap_def,
    blake2sBytes_split _ (fun b hb => by
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hb; exact length_blockBytes _) _ (by simp)
      (Or.inr (by simp [← List.length_pos_iff]))]
  simp only [Nat.add_sub_cancel, ↓reduceIte, List.length_map, List.length_range, length_blockBytes,
    prefixDigest]
  constructor <;> intro h <;> rw [h] <;> congr 2

/-- Blocks of two lists agree when their cells do. -/
theorem blocksOf_eq {a b : List E} {j j' : ℕ} (h : ∀ r < 4, a.getD (4 * j + r) 0 = b.getD (4 * j' + r) 0) :
    blocksOf a j = blocksOf b j' := by
  have h0 := h 0 (by omega)
  simp only [Nat.add_zero] at h0
  simp only [blocksOf, h0, h 1 (by omega), h 2 (by omega), h 3 (by omega)]

/-- The memory's cells from `p`, as a list. -/
noncomputable def cellsFrom (rd : Reader) (p : E) (len : ℕ) : List E := (List.range len).map (cellAt rd p)

theorem cellsFrom_getD {rd : Reader} {p : E} {len i : ℕ} (hi : i < len) :
    (cellsFrom rd p len).getD i 0 = cellAt rd p i := by
  rw [List.getD_eq_getElem _ _ (by simp [cellsFrom]; omega)]
  simp [cellsFrom]

theorem length_cellsFrom (rd : Reader) (p : E) (len : ℕ) : (cellsFrom rd p len).length = len := by
  simp [cellsFrom]

/-- The blocks of a run of cells read through `p·g^(4b)` are blocks `b + j` of the memory's cells
from `p`. -/
theorem blocksOf_slice {rd : Reader} {p : E} {b len : ℕ} {cs : List E} (m : ℕ)
    (h : CellsAt rd (p * gen ^ (4 * b)) cs) (hlen : cs.length = 4 * m) (hle : 4 * (b + m) ≤ len) :
    ∀ j < m, blocksOf cs j = blocksOf (cellsFrom rd p len) (b + j) := by
  intro j hj
  refine blocksOf_eq fun r hr => ?_
  rw [cellsFrom_getD (by omega), List.getD_eq_getElem _ _ (by omega),
    (cellsAt_slice h (4 * j + r) (by omega)).1]
  congr 1
  ring

/-- The reads of a run of cells through `p·g^b` are the memory's. -/
theorem loads_slice {rd : Reader} {p : E} {b : ℕ} {cs : List E}
    (h : CellsAt rd (p * gen ^ b) cs) :
    ∀ k < cs.length, LoadHolds rd p (b + k) (cellAt rd p (b + k)) := fun k hk =>
  (cellsAt_slice h k hk).2

/-- Blocks `b .. b + m - 1` of a list of cells, as a list of `4m` cells. -/
def sliceOf (cs : List E) (b m : ℕ) : List E := (List.range (4 * m)).map fun k => cs.getD (4 * b + k) 0

theorem length_sliceOf (cs : List E) (b m : ℕ) : (sliceOf cs b m).length = 4 * m := by
  simp [sliceOf]

theorem blocksOf_sliceOf (cs : List E) (b m : ℕ) : ∀ j < m, blocksOf (sliceOf cs b m) j = blocksOf cs (b + j) := by
  intro j hj
  refine blocksOf_eq fun r hr => ?_
  rw [List.getD_eq_getElem _ _ (by simp [sliceOf]; omega)]
  simp only [sliceOf, List.getElem_map, List.getElem_range]
  congr 1
  ring

theorem sliceOf_getD (cs : List E) (b m k : ℕ) (hk : k < 4 * m) :
    (sliceOf cs b m).getD k 0 = cs.getD (4 * b + k) 0 := by
  rw [List.getD_eq_getElem _ _ (by simp [sliceOf]; omega)]
  simp [sliceOf]

/-- A slice of cells read at `p` is read at `p·g^(4b)`. -/
theorem cellsAt_sliceOf {rd : Reader} {p : E} {cs : List E} {b m : ℕ} (h : CellsAt rd p cs)
    (hle : 4 * (b + m) ≤ cs.length) : CellsAt rd (p * gen ^ (4 * b)) (sliceOf cs b m) := by
  intro k hk
  have hk' : k < 4 * m := by simpa [sliceOf] using hk
  rw [loadHolds_mul_gen_pow]
  simp only [sliceOf, List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact h _ (by omega)

/-- The blocks of canonical cells are canonical. -/
theorem blocks_canonical {cs : List E} {n : ℕ} (hlen : cs.length = 4 * n)
    (h : ∀ c ∈ cs, IsCanonical128 c) : ∀ j < n, ∀ r, IsCanonical128 (blocksOf cs j r) := by
  intro j hj r
  have hr : ∀ (r : ℕ) (hr : r < 4), (blocksOf cs j ⟨r, hr⟩ : E) = cs.getD (4 * j + r) 0 := by
    intro r hr
    interval_cases r <;> rfl
  obtain ⟨r, hr4⟩ := r
  rw [hr r hr4, List.getD_eq_getElem _ _ (by omega)]
  exact h _ (List.getElem_mem _)

end
end LeanVM.Guest.B1.Digest
