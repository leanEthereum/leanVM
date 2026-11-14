/-
  LeanVM.Guest.B1.Da.VerifyMath

  From the digests and sums `da_verify` computes, a witness that opens its claim
  (`Da.MatrixWitness.Opens`).
-/

module

public import LeanVM.Guest.B1.Da.Tree
public import LeanVM.Guest.B1.Da.DualMath
public import LeanVM.Guest.WithHashBridge
public import LeanVM.Guest.Value.KeccakConst

/-!
# The claim `da_verify` returns is opened

Given `r` rows (`1 ≤ r ≤ LeanDa.maxRows`, padded to `2^L = LeanDa.paddedRowCount r`) and the symbols of
cell `(i, h)` (`syms i h`, `128` symbols of `E`), with every row orthogonal to the dual codeword
of `z` (`Σ_h Σ_e dualAt z (128 h + e) · sym i h e = 0`), `opens_of` builds the witness: the rows the
cells concatenate (`daRows`). It opens the root `daRoot`, the tree over the blob roots
(`blobLeaf`: a row's tree over its cell digests `cellD`, or the padding blob root), and `z`:
LeanDA's commitment (`LeanDa.commitCodewords`, Benedikt Wagner's LeanDA as `lean_da` transcribes
the crate) is computed level by level (`treeRoot_range`), and `dualAt` is LeanDA's dual codeword
(`dualAt_eq`).
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest

@[expose] public section

/-! ## Blocks of a list -/

theorem flatMap_getD {α : Type} (f : ℕ → List α) (m : ℕ) (hf : ∀ j, (f j).length = m) (d : α) :
    ∀ n j e, j < n → e < m → ((List.range n).flatMap f).getD (m * j + e) d = (f j).getD e d
  | 0, _, _, h, _ => absurd h (by omega)
  | n + 1, j, e, hj, he => by
    have hl : ((List.range n).flatMap f).length = m * n := by
      simp [List.length_flatMap, hf, mul_comm]
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rcases Nat.lt_or_ge j n with h | h
    · rw [List.getD_append _ _ _ _ (by rw [hl]; nlinarith), flatMap_getD f m hf d n j e h he]
    · obtain rfl : j = n := by omega
      rw [List.getD_append_right _ _ _ _ (by rw [hl]; omega), hl,
        show m * j + e - m * j = e by omega]

theorem length_flatMap_range {α : Type} (f : ℕ → List α) (m n : ℕ) (hf : ∀ j, (f j).length = m) :
    ((List.range n).flatMap f).length = n * m := by
  simp [List.length_flatMap, hf]

/-- Block `j` of a list of blocks of `m`. -/
theorem block_eq {α : Type} [Inhabited α] (f : ℕ → List α) (m : ℕ) (hf : ∀ j, (f j).length = m)
    {n j : ℕ} (hj : j < n) (d : α) : ((((List.range n).flatMap f).drop (j * m)).take m) = f j := by
  have hl := length_flatMap_range f m n hf
  apply List.ext_getElem
  · rw [List.length_take, List.length_drop, hl, hf]
    have : m ≤ n * m - j * m := by
      rw [← Nat.sub_mul]; exact Nat.le_mul_of_pos_left m (by omega)
    omega
  · intro e h1 h2
    rw [hf] at h2
    rw [List.getElem_take, List.getElem_drop]
    have := flatMap_getD f m hf d n j e hj h2
    have hk : j * m + e < ((List.range n).flatMap f).length := by rw [hl]; nlinarith
    rw [← List.getD_eq_getElem _ d hk, show j * m + e = m * j + e by ring, this,
      List.getD_eq_getElem _ _ (by rw [hf]; exact h2)]

theorem merkleRoot_congr (H : List UInt8 → Common.DigestBytes) :
    ∀ (d : ℕ) {f g : ℕ → Common.DigestBytes}, (∀ i < 2 ^ d, f i = g i) →
      LeanDa.merkleRootWithHash H d f = LeanDa.merkleRootWithHash H d g
  | 0, f, g, h => h 0 (by norm_num)
  | d + 1, f, g, h => by
    rw [LeanDa.merkleRootWithHash, LeanDa.merkleRootWithHash]
    refine merkleRoot_congr H d fun i hi => ?_
    simp only [LeanDa.upWithHash]
    rw [h (2 * i) (by rw [pow_succ]; omega), h (2 * i + 1) (by rw [pow_succ]; omega)]

theorem sum_range_mul (g : ℕ → E) (m : ℕ) : ∀ n,
    ∑ b ∈ Finset.range (n * m), g b = ∑ j ∈ Finset.range n, ∑ e ∈ Finset.range m, g (m * j + e)
  | 0 => by simp
  | n + 1 => by
    rw [Nat.succ_mul, Finset.sum_range_add, sum_range_mul g m n, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [mul_comm m n]

/-! ## The digests -/

section
variable (r L : ℕ) (syms : ℕ → ℕ → List E)

/-- Cell `(i, h)`'s digest. -/
def cellD (i h : ℕ) : Digest := keccak256 ((syms i h).flatMap E.toBytes)

/-- Blob `i`'s root among the padded rows: its tree over its cell digests, or the padding blob's. -/
def blobLeaf (i : ℕ) : Digest := if i < r then mRoot 7 (cellD syms i) else daPadBlobDigest

/-- The root: the tree over the blob roots. -/
def daRoot : Digest := mRoot L (blobLeaf r syms)

/-- The rows: each the concatenation of its `128` cells. -/
def daRows : List (List E) := (List.range r).map fun i => (List.range 128).flatMap (syms i)

end

/-! ## The witness -/

theorem keccak_eq (l : List UInt8) :
    LeanVM.Da.keccak256Bytes l = LeanVM.Protocol.Digest.toBytes (keccak256 l) := rfl

/-- **The witness opens the claim.** -/
theorem opens_of {r L : ℕ} {syms : ℕ → ℕ → List E} {z : E} (hr1 : 1 ≤ r)
    (hr : r ≤ LeanDa.maxRows) (hL : LeanDa.paddedRowCount r = 2 ^ L) (hrL : r ≤ 2 ^ L)
    (hsyms : ∀ i h, (syms i h).length = 128)
    (hdot : ∀ i < r, ∑ h ∈ Finset.range 128, ∑ e ∈ Finset.range 128,
      dualAt z (128 * h + e) * (syms i h).getD e 0 = 0) :
    (⟨daRows r syms⟩ : LeanVM.Da.MatrixWitness).Opens (daRoot r L syms) z := by
  have hrow : ∀ i, ((List.range 128).flatMap (syms i)).length = 2 ^ LeanDa.logM := fun i => by
    rw [length_flatMap_range _ 128 _ (hsyms i)]; rfl
  have hcell : ∀ i, ∀ h < 128, LeanDa.listCell ((List.range 128).flatMap (syms i)) h = syms i h :=
    fun i h hh => block_eq (syms i) 128 (hsyms i) hh 0
  have hlen : (daRows r syms).length = r := by simp [daRows]
  have hrows : ∀ row ∈ daRows r syms, row.length = 2 ^ LeanDa.logM := by
    intro row hrow'
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hrow'
    exact hrow i
  -- a row's blob root
  have hblob : ∀ i < r, LeanDa.listBlobRootWithHash LeanVM.Da.keccak256Bytes
      ((List.range 128).flatMap (syms i)) = LeanVM.Protocol.Digest.toBytes (mRoot 7 (cellD syms i)) := by
    intro i hi
    rw [LeanDa.listBlobRootWithHash, show LeanDa.cellsPerRow = 2 ^ 7 from rfl, treeRoot_range,
      toBytes_mRoot]
    refine merkleRoot_congr _ 7 fun h hh => ?_
    rw [LeanDa.listCellDigestWithHash, hcell i h (by simpa using hh), keccak_eq]
    rfl
  refine ⟨by rw [hlen]; exact hr1, by rw [hlen]; exact hr, hrows, ?_, ?_⟩
  · -- the commitment
    rw [LeanVM.Da.commitCells_keccakF1600 _ hrows, LeanDa.commitCodewordsWithHash, hlen, hL]
    have hlist : (daRows r syms).map (LeanDa.listBlobRootWithHash LeanVM.Da.keccak256Bytes) ++
        List.replicate (2 ^ L - r) (LeanDa.paddingBlobRootWithHash LeanVM.Da.keccak256Bytes) =
        (List.range (2 ^ L)).map (LeanVM.Protocol.Digest.toBytes ∘ blobLeaf r syms) := by
      refine List.ext_getElem (by simp [hlen]; omega) fun i h1 h2 => ?_
      simp only [List.length_map, List.length_range] at h2
      rw [List.getElem_map, List.getElem_range, Function.comp_apply, blobLeaf]
      by_cases hi : i < r
      · rw [List.getElem_append_left (by simp [hlen, hi]), List.getElem_map, ite_pos' hi, ← hblob i hi]
        simp [daRows]
      · rw [List.getElem_append_right (by simp [hlen]; omega), List.getElem_replicate, ite_neg' hi,
          paddingBlobRoot_eq]
    rw [hlist, treeRoot_range, daRoot, toBytes_mRoot]
  · -- orthogonality
    intro row hrow'
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hrow'
    have hi' := List.mem_range.mp hi
    rw [LeanDa.innerProduct]
    have hfun : ∀ b : Fin (2 ^ 14), LeanDa.dualCodewordAt z b *
        ((List.range 128).flatMap (syms i)).getD b 0 =
        dualAt z b * ((List.range 128).flatMap (syms i)).getD b 0 := fun b => by
      rw [dualAt_eq]
    rw [Finset.sum_congr rfl fun b _ => hfun b, Fin.sum_univ_eq_sum_range (fun b => dualAt z b *
      ((List.range 128).flatMap (syms i)).getD b 0) (2 ^ 14),
      show 2 ^ 14 = 128 * 128 by norm_num, sum_range_mul _ 128 128]
    refine (Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun e he => ?_).trans (hdot i hi')
    have hh' := Finset.mem_range.mp hh
    have he' := Finset.mem_range.mp he
    rw [flatMap_getD (syms i) 128 (hsyms i) 0 128 h e hh' he']

end
end LeanVM.Guest.B1.Da
