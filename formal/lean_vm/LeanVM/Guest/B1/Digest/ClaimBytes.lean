/-
  LeanVM.Guest.B1.Digest.ClaimBytes

  A claim as the four canonical cells its list hashes: the cells of `claimBytes`, and the claim
  lists' digests from `claim_list_digest`'s cells.
-/

module

public import LeanVM.Guest.B1.Digest.Common
public import LeanVM.Spec.Node

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Node

@[expose] public section

/-- The canonical cell of a 128-bit value: its low and high 64 bits as the two limbs. -/
def cellOf (v : BitVec 128) : E :=
  E.ofLimbs (BF64.ofBitVec (v.extractLsb' 0 64)) (BF64.ofBitVec (v.extractLsb' 64 64)) 0

/-- The 128-bit value of a cell's two limbs. -/
def bvOf (x : E) : BitVec 128 := (x.limb 1).toBitVec ++ (x.limb 0).toBitVec

theorem cellBytes_cellOf (v : BitVec 128) : cellBytes (cellOf v) = bytes16 v := by
  simp only [cellBytes, cellOf, ofLimbs_limb0, ofLimbs_limb1, kBytes, wordBytes, lowWord,
    highWord, bytes16, LeanXmss.bytesLE, List.ofFn_succ, List.ofFn_zero, List.cons_append,
    List.nil_append, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply UInt8.toBitVec_inj.mp
    simp only [UInt32.toBitVec_toUInt8, UInt32.toBitVec_shiftRight, BF64.toBitVec_ofBitVec]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp (disch := omega)
    all_goals (congr 1; omega)

theorem cellOf_bvOf {x : E} (hx : IsCanonical128 x) : cellOf (bvOf x) = x := by
  rw [eq_ofLimbs_of_canonical hx, cellOf, bvOf, ofLimbs_limb0, ofLimbs_limb1, ofLimbs_inj]
  refine ⟨?_, ?_, rfl⟩ <;> apply BF64.toBitVec_injective <;> rw [BF64.toBitVec_ofBitVec] <;>
    apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;> simp (disch := omega)
  all_goals (rw [BitVec.getElem_append]; split_ifs <;> first | rfl | (exfalso; omega) | (congr 1; omega))

theorem bytesLE_32 (m : BitVec 256) :
    LeanXmss.bytesLE 32 m = bytes16 (m.extractLsb' 0 128) ++ bytes16 (m.extractLsb' 128 128) := by
  apply List.ext_getElem (by simp [LeanXmss.bytesLE, bytes16])
  intro i h1 h2
  simp only [LeanXmss.bytesLE, bytes16, List.length_ofFn, List.length_append] at h1 h2
  simp only [LeanXmss.bytesLE, bytes16, List.getElem_ofFn]
  rw [List.getElem_append]
  split_ifs with h
  · simp only [List.getElem_ofFn]
    congr 1
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp (disch := omega)
    simp only [List.length_ofFn] at h
    intro _
    omega
  · simp only [List.getElem_ofFn, List.length_ofFn]
    congr 1
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp (disch := omega)
    simp only [List.length_ofFn] at h
    congr 1
    omega

/-- The four cells of a claim: the key's root and parameter, the message's halves. -/
def claimCells (root parameter : BitVec 128) (message : BitVec 256) : List E :=
  [cellOf root, cellOf parameter, cellOf (message.extractLsb' 0 128),
   cellOf (message.extractLsb' 128 128)]

theorem flatMap_cellBytes_claimCells (root parameter : BitVec 128) (message : BitVec 256) :
    (claimCells root parameter message).flatMap cellBytes = claimBytes root parameter message := by
  simp [claimCells, claimBytes, cellBytes_cellOf, bytesLE_32, List.append_assoc]

theorem extract_lo (a b : BitVec 128) : (a ++ b).extractLsb' 0 128 = b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp (disch := omega) [hi]

theorem extract_hi (a b : BitVec 128) : (a ++ b).extractLsb' 128 128 = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  simp (disch := omega)
  intro _
  exact hi

/-- The claim of four canonical cells. -/
def tripleOf (c0 c1 c2 c3 : E) : BitVec 128 × BitVec 128 × BitVec 256 :=
  (bvOf c0, bvOf c1, bvOf c3 ++ bvOf c2)

/-- **Canonical cells are claims**: `4n` canonical cells are the cells of `n` claims. -/
theorem cells_eq_claims {cs : List E} {n : ℕ} (hlen : cs.length = 4 * n)
    (hcan : ∀ c ∈ cs, IsCanonical128 c) :
    ∃ ts : List (BitVec 128 × BitVec 128 × BitVec 256), ts.length = n ∧
      cs = ts.flatMap fun t => claimCells t.1 t.2.1 t.2.2 := by
  refine ⟨(List.range n).map fun i => tripleOf (cs.getD (4 * i) 0) (cs.getD (4 * i + 1) 0)
    (cs.getD (4 * i + 2) 0) (cs.getD (4 * i + 3) 0), by simp, ?_⟩
  have hc : ∀ k < 4 * n, IsCanonical128 (cs.getD k 0) := fun k hk => by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact hcan _ (List.getElem_mem _)
  apply List.ext_getElem
  · rw [hlen, List.length_flatMap]
    simp only [claimCells, List.length_cons, List.length_nil, List.map_map, Function.comp_def,
      List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
    ring
  intro k h1 h2
  obtain ⟨i, r, hr, rfl⟩ : ∃ i r, r < 4 ∧ k = 4 * i + r := ⟨k / 4, k % 4, by omega, by omega⟩
  have hi : i < n := by omega
  rw [← List.getD_eq_getElem _ 0 h2, getD_flatMap_four _ (fun t => rfl) 0 _ i r (by simp; omega) hr]
  simp only [List.getElem_map, List.getElem_range, tripleOf, claimCells, extract_lo, extract_hi]
  rw [← List.getD_eq_getElem _ 0 h1]
  interval_cases r
  · simp only [Nat.add_zero]; exact (cellOf_bvOf (hc _ (by omega))).symm
  · exact (cellOf_bvOf (hc _ (by omega))).symm
  · exact (cellOf_bvOf (hc _ (by omega))).symm
  · exact (cellOf_bvOf (hc _ (by omega))).symm

/-- The bytes of the claims' cells are the claims' bytes. -/
theorem flatMap_cellBytes_claims (ts : List (BitVec 128 × BitVec 128 × BitVec 256)) :
    (ts.flatMap fun t => claimCells t.1 t.2.1 t.2.2).flatMap cellBytes =
      ts.flatMap fun t => claimBytes t.1 t.2.1 t.2.2 := by
  rw [List.flatMap_assoc]
  exact List.flatMap_congr fun t _ => flatMap_cellBytes_claimCells _ _ _

/-- **The leanXMSS list digest of a claim list's cells.** -/
theorem xmssListDigest_of_cells {cs : List E} {n : ℕ} (hlen : cs.length = 4 * n)
    (hcan : ∀ c ∈ cs, IsCanonical128 c) :
    ∃ claims : List XmssClaim, claims.length = n ∧
      cs = claims.flatMap (fun c => claimCells c.1.root c.1.parameter c.2) ∧
      blake2sBytes (cs.flatMap cellBytes) = xmssListDigest claims := by
  obtain ⟨ts, hts, rfl⟩ := cells_eq_claims hlen hcan
  refine ⟨ts.map fun t => (⟨t.1, t.2.1⟩, t.2.2), by simp [hts], by simp [List.flatMap_map], ?_⟩
  rw [flatMap_cellBytes_claims, xmssListDigest, List.flatMap_map]

/-- **The leanSPHINCS list digest of a claim list's cells.** -/
theorem sphincsListDigest_of_cells {cs : List E} {n : ℕ} (hlen : cs.length = 4 * n)
    (hcan : ∀ c ∈ cs, IsCanonical128 c) :
    ∃ claims : List SphincsClaim, claims.length = n ∧
      cs = claims.flatMap (fun c => claimCells c.1.root c.1.parameter c.2) ∧
      blake2sBytes (cs.flatMap cellBytes) = sphincsListDigest claims := by
  obtain ⟨ts, hts, rfl⟩ := cells_eq_claims hlen hcan
  refine ⟨ts.map fun t => (⟨t.1, t.2.1⟩, t.2.2), by simp [hts], by simp [List.flatMap_map], ?_⟩
  rw [flatMap_cellBytes_claims, sphincsListDigest, List.flatMap_map]

end
end LeanVM.Guest.B1.Digest
