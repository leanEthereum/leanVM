/-
  LeanVM.Guest.B1.Da.Link

  What `da_verify`'s soundness needs of LeanDA's definitions: bytes, the padding digests, the
  vector hash's counters, the trees and the inner products.
-/

module

public import LeanVM.Guest.B1.Da.VerifyBody
public import LeanVM.Guest.B1.Da.Pad
public import LeanVM.Guest.B1.Sig.Bytes

/-!
# LeanDA's definitions, as the guest computes them

* `leanDa_kBytes`, `vectorDigest_eq`: LeanDA's symbol bytes are this project's, and its vector
  digest is BLAKE2s of the entries' `eBytes`;
* `paddingCell_eq`, `paddingRow_eq`, `padCell_cells`, `padRow_cells`: the padding digests and
  the guest's constants;
* `vxMd_counters`: a column's metadata cells under honest counter words are the running byte
  counts of the whole vector;
* `nodeD_shift`, `nodeD_congr`, `nodeD_add`, `levels_root`, `treeRoot_blocks`: trees;
* `getElem?_flatMap_range`, `listCell_flatMap`: rows as concatenations of cells.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Node

@[expose] public section

/-! ## Bytes -/

theorem leanDa_kBytes (a : K) : LeanDa.kBytes a = kBytes a := by
  rw [Sig.kBytes_eq]
  apply List.ext_getElem (by simp [LeanDa.kBytes])
  intro t h1 h2
  simp only [LeanDa.kBytes, List.getElem_map, List.getElem_range, Sig.getElem_leBytes, kToNat,
    Nat.shiftRight_eq_div_pow, pow_mul]
  rfl

theorem vectorDigest_eq (v : List E) :
    LeanDa.vectorDigest Da.blake2s v = Da.toBytes (blake2sBytes (v.flatMap eBytes)) := by
  rw [LeanDa.vectorDigest, Da.blake2s, List.flatMap_assoc]
  congr 2
  refine List.flatMap_congr fun e _ => ?_
  simp [leanDa_kBytes, eBytes, LeanDa.limb, E.limb]

/-! ## The padding digests -/

theorem zeros_bytes : (List.replicate 256 (0 : K)).flatMap LeanDa.kBytes = List.replicate 2048 0 := by
  decide +kernel

theorem paddingCell_eq : LeanDa.paddingCell Da.blake2s = Da.toBytes padCellD := by
  rw [LeanDa.paddingCell, LeanDa.cellSymbols, zeros_bytes, Da.blake2s, blake2s_zeros]

theorem replicate_toBytes (d : Digest) : ∀ n,
    (List.replicate n (Da.toBytes d)).flatMap Vector.toList = (List.replicate n d).flatMap digestBytes
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, List.replicate_succ, List.flatMap_cons, List.flatMap_cons, replicate_toBytes d n,
      toBytes_toList]

theorem paddingRow_eq : LeanDa.paddingRow Da.blake2s = Da.toBytes padRowD := by
  rw [LeanDa.paddingRow, paddingCell_eq, LeanDa.payloadCells, replicate_toBytes, Da.blake2s]
  exact congrArg Da.toBytes blake2s_padRow

theorem padCell_cells : digestScalars padCellD = (padCell0, padCell1) := by
  refine Prod.ext ?_ ?_ <;> simp only [digestScalars, wordsCell, word, ofLimbs_inj] <;> decide

theorem padRow_cells : digestScalars padRowD = (padRow0, padRow1) := by
  refine Prod.ext ?_ ?_ <;> simp only [digestScalars, wordsCell, word, ofLimbs_inj] <;> decide

/-! ## The vector hash's counters -/

/-- Column `b`'s counter words: `counters[3b + k] = (3b + k)·2048`. -/
def cvOf (b : ℕ) (k : ℕ) : E := word ((3 * b + k) * 2048) 0 0

theorem word_add_mdF (c : ℕ) : word c 0 0 + mdF = metadataCell c true := by
  unfold mdF word
  rw [ofLimbs_add, metadataCell]
  simp [ofBits_zero]

/-- **The counters are the running byte counts**: block `j` of column `b` is compressed at
`64·(96b + j + 1)` bytes, final at the very last block. -/
theorem vxMd_counters {b j : ℕ} (hb : b < 128) (hj : j < 96) :
    vxMd (decide (b = 127)) (cvOf b) j = metadataCell (64 * (96 * b + j + 1)) (decide (b = 127 ∧ j = 95)) := by
  unfold vxMd
  by_cases h1 : j % 32 = 31
  · rw [ite_pos' h1]
    by_cases h2 : b = 127 ∧ j = 95
    · obtain ⟨rfl, rfl⟩ := h2
      rw [ite_pos' (by decide), cvOf, word_add_mdF]
      rfl
    · have h2' : ¬(decide (b = 127) = true ∧ j = 95) := by simpa using h2
      rw [ite_neg' h2', cvOf, decide_eq_false h2, ← word_md]
      congr 1
      omega
  · rw [ite_neg' h1, cvOf, show (3 * b + j / 32) * 2048 = 2 ^ 11 * (3 * b + j / 32) by ring,
      word_eq_eOfNat, word_eq_eOfNat (64 * _), eOfNat_add_of_lt (by omega), ← word_eq_eOfNat,
      decide_eq_false (by omega : ¬(b = 127 ∧ j = 95)), ← word_md]
    congr 1
    omega

/-! ## Trees -/

theorem nodeD_shift : ∀ (k : ℕ) (L : ℕ → Digest) (i : ℕ),
    nodeD L k i = nodeD (fun t => L (2 ^ k * i + t)) k 0
  | 0, L, i => by simp [nodeD]
  | k + 1, L, i => by
    rw [nodeD, nodeD, nodeD_shift k L (2 * i), nodeD_shift k L (2 * i + 1),
      nodeD_shift k _ 0, nodeD_shift k _ 1]
    congr 2 <;> funext t <;> congr 1 <;> ring

theorem nodeD_congr : ∀ (k : ℕ) {L L' : ℕ → Digest}, (∀ t < 2 ^ k, L t = L' t) →
    nodeD L k 0 = nodeD L' k 0
  | 0, L, L', h => h 0 (by norm_num)
  | k + 1, L, L', h => by
    rw [nodeD, nodeD, nodeD_shift k L 1, nodeD_shift k L' 1]
    rw [nodeD_congr k (L := L) (L' := L') fun t ht => h t (by rw [pow_succ]; omega),
      nodeD_congr k (L := fun t => L (2 ^ k * (2 * 0 + 1) + t)) (L' := fun t => L' (2 ^ k * (2 * 0 + 1) + t))
        fun t ht => h _ (by rw [pow_succ]; omega)]

theorem nodeD_add (L : ℕ → Digest) (a : ℕ) : ∀ (c i : ℕ), nodeD L (a + c) i = nodeD (nodeD L a) c i
  | 0, i => rfl
  | c + 1, i => by rw [← Nat.add_assoc, nodeD, nodeD, nodeD_add L a c, nodeD_add L a c]

/-- **A tree's root from its leaves**: the leaves stored at `tree·g^(2i)` determine the root
`da_levels` returns. -/
theorem levels_root {rd : Reader} {k : ℕ} {tree r0 r1 : E} {L : ℕ → Digest}
    (h : Meaning_da_levels k rd [tree] [r0, r1])
    (hl : ∀ i < 2 ^ k, CellsAt rd (tree * gen ^ (2 * i)) [(digestScalars (L i)).1, (digestScalars (L i)).2]) :
    (r0, r1) = digestScalars (nodeD L k 0) := by
  obtain ⟨tree', r0', r1', ha, hr, hm⟩ := h
  simp only [List.cons.injEq, and_true] at ha hr
  obtain ⟨rfl⟩ := ha
  obtain ⟨rfl, rfl⟩ := hr
  rcases hm with ⟨rfl, hc⟩ | ⟨hk, leaf, hlv, hroot⟩
  · have h0 := hl 0 (by norm_num)
    rw [Nat.mul_zero, pow_zero, mul_one] at h0
    obtain ⟨a0, a1⟩ := cellsAt_two.mp hc
    obtain ⟨b0, b1⟩ := cellsAt_two.mp h0
    rw [loadHolds_unique a0 b0, loadHolds_unique a1 b1]
    rfl
  · rw [hroot]
    congr 1
    refine nodeD_congr k fun t ht => digestScalars_injective ?_
    have h1 := hlv 0 (Nat.zero_le _) t (by simpa using ht)
    rw [lvOff, Nat.sub_zero, Nat.sub_self, Nat.zero_add] at h1
    obtain ⟨a0, a1⟩ := cellsAt_two.mp h1
    obtain ⟨b0, b1⟩ := cellsAt_two.mp (hl t ht)
    exact Prod.ext (loadHolds_unique a0 b0) (loadHolds_unique a1 b1)

/-- A run of `k·n` indices mapped, cut into `n` runs of `k`. -/
theorem map_range_mul {α : Type} (k : ℕ) (g : ℕ → α) :
    ∀ n, (List.range (k * n)).map g = (List.range n).flatMap fun b => (List.range k).map fun r => g (k * b + r)
  | 0 => by simp
  | n + 1 => by
      rw [show k * (n + 1) = k * n + k by ring, List.range_add, List.map_append, map_range_mul k g n,
        List.range_succ, List.flatMap_append, List.map_map]
      simp [Function.comp_def]

/-- **A tree over blocks of `2^a` leaves** is the tree over the blocks' roots. -/
theorem treeRoot_blocks (a c : ℕ) (L : ℕ → ℕ → Digest) :
    LeanDa.treeRoot Da.blake2s ((List.range (2 ^ c)).flatMap fun j =>
        (List.range (2 ^ a)).map fun i => Da.toBytes (L j i)) =
      Da.toBytes (nodeD (fun j => nodeD (L j) a 0) c 0) := by
  have e : (List.range (2 ^ c)).flatMap (fun j => (List.range (2 ^ a)).map fun i => Da.toBytes (L j i)) =
      (List.range (2 ^ (a + c))).map fun m => Da.toBytes (L (m / 2 ^ a) (m % 2 ^ a)) := by
    rw [pow_add, map_range_mul]
    refine List.flatMap_congr fun j _ => List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    have hp : 0 < 2 ^ a := by positivity
    rw [show (2 ^ a * j + i) / 2 ^ a = j by
        rw [Nat.add_comm, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hi', Nat.zero_add],
      show (2 ^ a * j + i) % 2 ^ a = i by rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi']]
  rw [e, treeRoot_nodeD, nodeD_add]
  congr 2
  funext j
  rw [nodeD_shift]
  refine nodeD_congr a fun t ht => ?_
  have hp : 0 < 2 ^ a := by positivity
  rw [show (2 ^ a * j + t) / 2 ^ a = j by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt ht, Nat.zero_add],
    show (2 ^ a * j + t) % 2 ^ a = t by rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]]

/-! ## Rows -/

theorem length_flatMap_range {α : Type} {m : ℕ} (L : ℕ → List α) :
    ∀ n, (∀ b < n, (L b).length = m) → ((List.range n).flatMap L).length = m * n
  | 0, _ => by simp
  | n + 1, hl => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append,
      length_flatMap_range L n (fun b hb => hl b (by omega)), hl n (by omega)]
    ring

theorem getElem?_flatMap_range {α : Type} {m : ℕ} (L : ℕ → List α) :
    ∀ n, (∀ b < n, (L b).length = m) → ∀ b < n, ∀ k < m,
      ((List.range n).flatMap L)[m * b + k]? = (L b)[k]?
  | 0, _, b, hb, _, _ => absurd hb (by omega)
  | n + 1, hl, b, hb, k, hk => by
    have hlen := length_flatMap_range L n (fun b hb => hl b (by omega))
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rcases Nat.lt_or_ge b n with h | h
    · rw [List.getElem?_append_left (by rw [hlen]; nlinarith)]
      exact getElem?_flatMap_range L n (fun b hb => hl b (by omega)) b h k hk
    · obtain rfl : b = n := by omega
      rw [List.getElem?_append_right (by rw [hlen]; omega), hlen, Nat.add_sub_cancel_left]

/-- Cell `j` of a row given as the concatenation of its cells. -/
theorem listCell_flatMap (L : ℕ → List K) (hl : ∀ b < 128, (L b).length = 256) {j : ℕ} (hj : j < 128) :
    LeanDa.listCell ((List.range 128).flatMap L) j = L j := by
  rw [LeanDa.listCell, LeanDa.cellSymbols]
  apply List.ext_getElem?
  intro t
  rw [List.getElem?_take, List.getElem?_drop]
  by_cases ht : t < 256
  · rw [ite_pos' ht, show j * 256 + t = 256 * j + t by ring, getElem?_flatMap_range L 128 hl j hj t ht]
  · rw [ite_neg' ht, List.getElem?_eq_none (by rw [hl j hj]; omega)]

end
end LeanVM.Guest.B1.Digest
