/-
  LeanVM.Guest.Value.Hash

  Chained BLAKE2s over canonical cells: a sequence of `BLAKE2S` instructions with cumulative
  counters, the final flag on the last block and zero fill computes `blake2sBytes` of the cells'
  bytes.
-/

module

public import LeanVM.Guest.Value.Cells

/-!
# Chained BLAKE2s over cells

The guest hashes a byte string of `d.length` bytes as `n + 1` compressions over four cells each
(`zkDSL.md` §BLAKE2s): block `j < n` carries the counter `64·(j + 1)` and no flag, the last carries
the total length and the last-block flag, and the bytes past the end are zero cells. That is
`blake2sBytes d` (`Spec/Blake2s.lean`, `hash/mod.rs:157-204`), and this module proves it in the
pieces the guest's loops compose:

* `chain_nonfinal`: a run of non-final blocks from any chaining value at any byte offset is
  `absorbBlocks`, the specification's non-final steps;
* `chain_final`: the last block, zero-filled, is `absorb … 0`;
* `absorb_split`, `blake2sBytes_split`: the specification's hash, cut after whole blocks;
* `chain_absorb` and `chain_eq_blake2sBytes`: a whole chain, from any state or from the IV.

The forms the guest uses are corollaries: one block under the default IV
(`blake2s_default`; every Fiat-Shamir step and Merkle node), the empty input as one zero block at
counter 0 with the final flag (`blake2s_empty`; `claim_list_digest`, G:2771,
`child_claim_list_digest`, G:2850, `da_hash_roots`, G:3096), chains from the IV with
compile-time counters over whole blocks (`chain_eq_blake2sBytes_blocks`; `statement_digest`,
G:2698-2701, `da_hash_roots`, G:3093-3108, `da_verify_cell`, G:3000-3016), and runtime counters
by the disjoint-bit split (`Cells.eOfNat_add_metadataCell`; `claims_window`, `claims_tail`,
`claim_list_digest`, G:2726-2799, `da_vector_cell`, G:3045-3085), whose windows compose by
`absorbBlocks_append` and `chain_nonfinal` at the window's byte offset.
-/

namespace LeanVM.Guest.Value

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash

@[expose] public section

/-! ## The specification's hash, cut after whole blocks -/

/-- Absorb whole 64-byte blocks from the chaining value `h` after `t` bytes, each compressed at
the byte count including it with no flag: `absorb`'s non-final steps (`hash/mod.rs:157-170`). -/
def absorbBlocks (h : Digest) (t : ℕ) : List (List UInt8) → Digest
  | [] => h
  | b :: bs => absorbBlocks (compress h (blockWords b) (t + 64).toUInt64 0 0) (t + 64) bs

/-- Whole blocks absorb in sequence. -/
theorem absorbBlocks_append (h : Digest) (t : ℕ) (bs cs : List (List UInt8)) :
    absorbBlocks h t (bs ++ cs) = absorbBlocks (absorbBlocks h t bs) (t + 64 * bs.length) cs := by
  induction bs generalizing h t with
  | nil => rfl
  | cons b bs ih =>
    rw [List.cons_append, absorbBlocks, absorbBlocks, ih, List.length_cons]
    congr 1
    ring

/-- The bytes of whole blocks. -/
theorem length_flatten_of_64 (bs : List (List UInt8)) (hbs : ∀ b ∈ bs, b.length = 64) :
    bs.flatten.length = 64 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [List.flatten_cons, List.length_append, hbs b (by simp),
      ih fun c hc ↦ hbs c (by simp [hc]), List.length_cons]
    ring

/-- **`absorb` after whole blocks**: absorbing `bs.length + n` more blocks of `bs.flatten ++ rest`
is absorbing the whole blocks `bs`, then `n` more of `rest`. -/
theorem absorb_split (h : Digest) (t : ℕ) (bs : List (List UInt8)) (hbs : ∀ b ∈ bs, b.length = 64)
    (n : ℕ) (rest : List UInt8) :
    absorb h t (bs.length + n) (bs.flatten ++ rest) =
      absorb (absorbBlocks h t bs) (t + 64 * bs.length) n rest := by
  induction bs generalizing h t with
  | nil => simp [absorbBlocks]
  | cons b bs ih =>
    have hb : b.length = 64 := hbs b (by simp)
    rw [List.length_cons, show bs.length + 1 + n = (bs.length + n) + 1 by omega, absorb,
      List.flatten_cons, List.append_assoc, List.take_left' hb, List.drop_left' hb,
      ih _ _ fun c hc ↦ hbs c (by simp [hc]), absorbBlocks]
    congr 1
    ring

/-- **BLAKE2s-256 cut after its whole blocks**: whole blocks `bs`, then a last block `r` of at
most 64 bytes, nonempty unless the input is. -/
theorem blake2sBytes_split (bs : List (List UInt8)) (hbs : ∀ b ∈ bs, b.length = 64)
    (r : List UInt8) (hr : r.length ≤ 64) (hr' : bs = [] ∨ r ≠ []) :
    blake2sBytes (bs.flatten ++ r) =
      compress (absorbBlocks paramIv 0 bs) (blockWords r) (64 * bs.length + r.length).toUInt64
        lastBlock 0 := by
  have hlen := length_flatten_of_64 bs hbs
  have hn : ((bs.flatten ++ r).length - 1) / 64 = bs.length + 0 := by
    rw [List.length_append, hlen]
    rcases hr' with h | h
    · subst h
      simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, Nat.add_zero]
      omega
    · have := List.length_pos_of_ne_nil h
      omega
  rw [blake2sBytes, hn, absorb_split paramIv 0 bs hbs 0 r, absorb, Nat.zero_add]

/-! ## Chains of cells -/

/-- **A run of non-final compressions over cells** (`CompressCells`, `Spec/Isa.lean:165`): from the
chaining value of `h` after `t` bytes, `n` compressions of the blocks `blocks j` at the counters
`t + 64·(j + 1)` with no flag reach the chaining value of `absorbBlocks h t` over their bytes,
`absorb`'s non-final steps (`Spec/Blake2s.lean:172`). -/
theorem chain_nonfinal {n : ℕ} {h : Digest} {t : ℕ} {blocks : ℕ → Fin 4 → E} {st : ℕ → E × E}
    {md : ℕ → E} (h0 : st 0 = digestScalars h)
    (hmd : ∀ j < n, md j = metadataCell (t + 64 * (j + 1)) false)
    (hc : ∀ j < n, CompressCells (blocks j) (st j).1 (st j).2 (st (j + 1)).1 (st (j + 1)).2 (md j)) :
    st n = digestScalars (absorbBlocks h t ((List.range n).map fun j ↦ blockBytes (blocks j))) := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    have ih := ih (fun j hj ↦ hmd j (by omega)) (fun j hj ↦ hc j (by omega))
    have hcn := hc n (by omega)
    rw [ih, hmd n (by omega)] at hcn
    have := compressCells_eq hcn
    rw [unpackMetadata_metadataCell] at this
    simp only [Bool.false_eq_true, ↓reduceIte] at this
    rw [List.range_succ, List.map_append, absorbBlocks_append, List.length_map, List.length_range,
      List.map_singleton, absorbBlocks, absorbBlocks, show t + 64 * n + 64 = t + 64 * (n + 1) by ring,
      ← this]

/-- **The last compression over cells**: from the chaining value of `h` after `t` bytes, the
block whose bytes are `r` then zeros, at the counter `t + r.length` with the last-block flag, is
`absorb h t 0 r` (`Spec/Blake2s.lean:172`): the zero fill is `blockWords`'s own padding. -/
theorem chain_final {h : Digest} {t : ℕ} {m : Fin 4 → E} {md out0 out1 : E} {r : List UInt8}
    (hr : blockBytes m = r ++ List.replicate (64 - r.length) 0)
    (hmd : md = metadataCell (t + r.length) true)
    (hc : CompressCells m (digestScalars h).1 (digestScalars h).2 out0 out1 md) :
    (out0, out1) = digestScalars (absorb h t 0 r) := by
  have := compressCells_eq hc
  rw [hmd, unpackMetadata_metadataCell, hr, blockWords_append_zeros] at this
  exact this

/-- **A whole chain from any state**: from the chaining value of `h` after `t` bytes, `n`
non-final blocks at counters `t + 64·(j + 1)` and a last block at `t + d.length` with the flag,
over the bytes of `d` zero-filled to `64·(n + 1)`, give `absorb h t n d` (`Spec/Blake2s.lean:172`). -/
theorem chain_absorb {n : ℕ} {h : Digest} {t : ℕ} {blocks : ℕ → Fin 4 → E} {st : ℕ → E × E}
    {md : ℕ → E} {d : List UInt8} (hlo : 64 * n ≤ d.length)
    (hbytes : (List.range (n + 1)).flatMap (fun j ↦ blockBytes (blocks j)) =
      d ++ List.replicate (64 * (n + 1) - d.length) 0)
    (h0 : st 0 = digestScalars h)
    (hmd : ∀ j < n, md j = metadataCell (t + 64 * (j + 1)) false)
    (hfin : md n = metadataCell (t + d.length) true)
    (hc : ∀ j ≤ n, CompressCells (blocks j) (st j).1 (st j).2 (st (j + 1)).1 (st (j + 1)).2 (md j)) :
    st (n + 1) = digestScalars (absorb h t n d) := by
  set bs := (List.range n).map fun j ↦ blockBytes (blocks j) with hbs_def
  have hbs : ∀ b ∈ bs, b.length = 64 := by
    intro b hb
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hb
    exact length_blockBytes _
  have hblen : bs.length = n := by simp [bs]
  have hflat : bs.flatten.length = 64 * n := by rw [length_flatten_of_64 bs hbs, hblen]
  have hsplit : (List.range (n + 1)).flatMap (fun j ↦ blockBytes (blocks j)) =
      bs.flatten ++ blockBytes (blocks n) := by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.flatMap_def]
  rw [hsplit] at hbytes
  have hhi : d.length ≤ 64 * (n + 1) := by
    have := congrArg List.length hbytes
    simp only [List.length_append, length_blockBytes, List.length_replicate, hflat] at this
    omega
  have hpre : bs.flatten = d.take (64 * n) := by
    have := congrArg (List.take (64 * n)) hbytes
    rwa [List.take_left' hflat, List.take_append_of_le_length hlo] at this
  have hlast : blockBytes (blocks n) =
      d.drop (64 * n) ++ List.replicate (64 - (d.drop (64 * n)).length) 0 := by
    have := congrArg (List.drop (64 * n)) hbytes
    rw [List.drop_left' hflat, List.drop_append_of_le_length hlo] at this
    rw [this, List.length_drop]
    congr 2
    omega
  have hn := chain_nonfinal (n := n) (blocks := blocks) h0 hmd (fun j hj ↦ hc j (by omega))
  rw [← hbs_def] at hn
  have hcn := hc n (le_refl n)
  rw [hn] at hcn
  have hfin' : md n = metadataCell (t + 64 * n + (d.drop (64 * n)).length) true := by
    rw [hfin, List.length_drop]
    congr 1
    omega
  have := chain_final hlast hfin' hcn
  rw [Prod.mk.eta] at this
  have key := absorb_split h t bs hbs 0 (d.drop (64 * n))
  rw [hblen, Nat.add_zero, hpre, List.take_append_drop] at key
  rw [this, key]

/-- **Chained BLAKE2s over cells equals `blake2sBytes`**: from the IV, the `n + 1` compressions of
a byte string `d` of `(d.length - 1) / 64 + 1` blocks (one zero block for the empty string), each
non-final block at the cumulative counter `64·(j + 1)` with no flag, the last at `d.length` with
the last-block flag, over the bytes of `d` zero-filled to whole blocks, give `blake2sBytes d`
(`Spec/Blake2s.lean:180`). -/
theorem chain_eq_blake2sBytes {n : ℕ} {blocks : ℕ → Fin 4 → E} {st : ℕ → E × E} {md : ℕ → E}
    {d : List UInt8} (hn : (d.length - 1) / 64 = n)
    (hbytes : (List.range (n + 1)).flatMap (fun j ↦ blockBytes (blocks j)) =
      d ++ List.replicate (64 * (n + 1) - d.length) 0)
    (h0 : st 0 = ivCells)
    (hmd : ∀ j < n, md j = metadataCell (64 * (j + 1)) false)
    (hfin : md n = metadataCell d.length true)
    (hc : ∀ j ≤ n, CompressCells (blocks j) (st j).1 (st j).2 (st (j + 1)).1 (st (j + 1)).2 (md j)) :
    st (n + 1) = digestScalars (blake2sBytes d) := by
  have hlo : 64 * n ≤ d.length := by
    rcases Nat.eq_zero_or_pos d.length with h | h
    · rw [h] at hn ⊢
      simp at hn
      omega
    · omega
  rw [blake2sBytes, hn]
  exact chain_absorb (t := 0) hlo hbytes h0 (fun j hj ↦ by rw [hmd j hj, Nat.zero_add])
    (by rw [hfin, Nat.zero_add]) hc

/-- **Whole blocks**: a chain over `n + 1` blocks of cells, all bytes data, the last block at the
counter `64·(n + 1)` with the flag, is `blake2sBytes` of the cells' bytes (`statement_digest`,
`da_hash_roots`, `da_verify_cell`). -/
theorem chain_eq_blake2sBytes_blocks {n : ℕ} {blocks : ℕ → Fin 4 → E} {st : ℕ → E × E}
    {md : ℕ → E} (h0 : st 0 = ivCells)
    (hmd : ∀ j < n, md j = metadataCell (64 * (j + 1)) false)
    (hfin : md n = metadataCell (64 * (n + 1)) true)
    (hc : ∀ j ≤ n, CompressCells (blocks j) (st j).1 (st j).2 (st (j + 1)).1 (st (j + 1)).2 (md j)) :
    st (n + 1) = digestScalars
      (blake2sBytes ((List.range (n + 1)).flatMap fun j ↦ blockBytes (blocks j))) := by
  have hlen : ((List.range (n + 1)).flatMap fun j ↦ blockBytes (blocks j)).length = 64 * (n + 1) := by
    rw [List.flatMap_def, length_flatten_of_64 _ (by
      intro b hb
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hb
      exact length_blockBytes _)]
    simp
  refine chain_eq_blake2sBytes (by rw [hlen]; omega) ?_ h0 hmd (by rw [hfin, hlen]) hc
  rw [hlen, Nat.sub_self, List.replicate_zero, List.append_nil]

/-- **One block under the default IV** (`blake2s(a, b, out)` with no keywords: the IV, counter
64, the final flag; every Fiat-Shamir step and Merkle node): the output is `blake2sBytes` of the
block's 64 bytes. -/
theorem blake2s_default {m : Fin 4 → E} {out0 out1 : E}
    (hc : CompressCells m ivCells.1 ivCells.2 out0 out1 (metadataCell 64 true)) :
    (out0, out1) = digestScalars (blake2sBytes (blockBytes m)) := by
  have := chain_final (h := paramIv) (t := 0) (r := blockBytes m) (by simp) (by simp) hc
  rw [this, blake2sBytes, length_blockBytes]

/-- `blake2s_default` as an equivalence, over canonical message cells. -/
theorem blake2s_default_iff {m : Fin 4 → E} {out0 out1 : E} (hm : ∀ i, IsCanonical128 (m i)) :
    CompressCells m ivCells.1 ivCells.2 out0 out1 (metadataCell 64 true) ↔
      (out0, out1) = digestScalars (blake2sBytes (blockBytes m)) := by
  refine ⟨blake2s_default, fun h ↦ ?_⟩
  refine (compressCells_iff (h := paramIv) hm (isCanonical128_metadataCell 64 true)).mpr ?_
  rw [h, unpackMetadata_metadataCell, blake2sBytes, length_blockBytes]
  rfl

/-- **The empty input** (`blake2s([0, 0], [0, 0], out, md=MD_FINAL)`, G:2771, G:2850, and
`counter=0, final=1`, G:3096): one zero block at counter 0 with the final flag under the IV is
`blake2sBytes []`. -/
theorem blake2s_empty {out0 out1 : E}
    (hc : CompressCells ![0, 0, 0, 0] ivCells.1 ivCells.2 out0 out1 (metadataCell 0 true)) :
    (out0, out1) = digestScalars (blake2sBytes []) := by
  have hz : ∀ i, (![0, 0, 0, 0] : Fin 4 → E) i = 0 := by
    intro i
    fin_cases i <;> rfl
  have hb : blockBytes ![0, 0, 0, 0] = [] ++ List.replicate (64 - 0) 0 := by
    simp only [blockBytes, hz, cellBytes_zero, List.nil_append, Nat.sub_zero, ← List.replicate_add]
  exact chain_final (h := paramIv) (t := 0) hb rfl hc

end
end LeanVM.Guest.Value
