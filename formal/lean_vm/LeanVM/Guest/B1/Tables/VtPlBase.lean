/-
  LeanVM.Guest.B1.Tables.VtPlBase

  `verify_tables`' placed form: its buffers' regions and words, the blocks' log-heights at `bk`.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesCKids
public import LeanVM.Guest.B1.Tables.VtZcC
public import LeanVM.Guest.B1.Tables.TermAtProof

/-!
# The buffers, placed

Buffer `i` of `verify_tables` lies at `vtPtr b n i`, holds `vtOwnW`'s `i`-th list, of exactly
`vtSizes n`'s `i`-th length (`vtOwnW_lens`), so its region covers every offset below its size
(`vt_own_region`); `bk` holds `g^ks` for the blocks' log-heights `ks = vtKs` (`vt_bk_get`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Sig
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

theorem vt_length_bases (b : ℕ) : ∀ sizes : List ℕ, (bases b sizes).length = sizes.length
  | [] => rfl
  | _ :: ss => by simp [bases, vt_length_bases _ ss]

theorem vt_bufL_mem {b : ℕ} {sizes : List ℕ} {cs : List (List E)} {i : ℕ} (hi : i < sizes.length)
    (hc : i < cs.length) : ((bases b sizes).getD i 0, cs.getD i []) ∈ bufL b sizes cs := by
  have hb : i < (bases b sizes).length := by rw [vt_length_bases]; exact hi
  have hz : i < (bufL b sizes cs).length := by simp [bufL, List.length_zip, vt_length_bases]; omega
  have := List.getElem_mem hz
  simp only [bufL, List.getElem_zip] at this
  rwa [List.getD_eq_getElem _ _ hb, List.getD_eq_getElem _ _ hc]

theorem vtSizes_length (n : ℕ) : (vtSizes n).length = 205 := by simp [vtSizes, selSz]

theorem zcRoundsW_length (cvr : ℕ → Digest) (cur : E) (cl : ℕ → E) (n : ℕ) :
    (zcRoundsW cvr cur cl n).length = 4 * (n + 1) :=
  flatMapK_length 4 _ (n + 1) fun _ _ => rfl

theorem vtOwnW_lens (ks : ℕ → ℕ) (point : List E) (logMem n : ℕ) (cvr : ℕ → Digest) (cur : E)
    (cl ch : ℕ → E) (chis : List E) :
    (vtOwnW ks point logMem n cvr cur cl ch chis).map List.length = vtSizes n := by
  have hsel : ∀ i, (selW ks point i).map List.length = selSz := fun i => by simp [selW, selSz]
  have hfm : ((List.range 62).flatMap fun i => selW ks point (i + 3)).map List.length =
      (List.range 62).flatMap fun _ => selSz := by
    rw [List.map_flatMap]; exact List.flatMap_congr fun i _ => hsel (i + 3)
  simp only [vtOwnW, vtSizes, List.map_append, hsel, hfm]
  simp [sortW, sideW, offW, idxcW, bimW, idxChainW, zcRoundsW_length, zcCprodW, zcPeqW]

theorem vt_own_len {ks : ℕ → ℕ} {point : List E} {logMem n : ℕ} {cvr : ℕ → Digest} {cur : E}
    {cl ch : ℕ → E} {chis : List E} {i : ℕ} (hi : i < 205) :
    ((vtOwnW ks point logMem n cvr cur cl ch chis).getD i []).length = (vtSizes n).getD i 0 := by
  have hl := congrArg List.length (vtOwnW_lens ks point logMem n cvr cur cl ch chis)
  rw [List.length_map, vtSizes_length] at hl
  rw [← vtOwnW_lens ks point logMem n cvr cur cl ch chis, List.getD_eq_getElem _ _ (by omega),
    List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map]

theorem vt_own_region {b : ℕ} {ks : ℕ → ℕ} {point : List E} {logMem n : ℕ} {cvr : ℕ → Digest}
    {cur : E} {cl ch : ℕ → E} {chis : List E} {i off : ℕ} (hi : i < 205)
    (hoff : off < (vtSizes n).getD i 0) :
    RegionL (bufL b (vtSizes n) (vtOwnW ks point logMem n cvr cur cl ch chis))
      ((bases b (vtSizes n)).getD i 0 + off) := by
  have hl := congrArg List.length (vtOwnW_lens ks point logMem n cvr cur cl ch chis)
  rw [List.length_map, vtSizes_length] at hl
  exact region_buf (vt_bufL_mem (by rw [vtSizes_length]; exact hi) (by omega))
    (by rw [vt_own_len hi]; exact hoff)

theorem vt_own_reads {rd : Reader} {b : ℕ} {ks : ℕ → ℕ} {point : List E} {logMem n : ℕ}
    {cvr : ℕ → Digest} {cur : E} {cl ch : ℕ → E} {chis : List E}
    (hB : MemL rd (bufL b (vtSizes n) (vtOwnW ks point logMem n cvr cur cl ch chis))) {i : ℕ}
    (hi : i < 205) : ReadsAt rd (vtPtr b n i) ((vtOwnW ks point logMem n cvr cur cl ch chis).getD i []) := by
  have hl := congrArg List.length (vtOwnW_lens ks point logMem n cvr cur cl ch chis)
  rw [List.length_map, vtSizes_length] at hl
  exact memL_one hB (vt_bufL_mem (by rw [vtSizes_length]; exact hi) (by omega))

theorem vtPtr_addr (b n i e off : ℕ) :
    (vtPtr b n i * gen ^ e).limb 0 * Parameters.gpow off =
      Parameters.gpow ((bases b (vtSizes n)).getD i 0 + (e + off)) := by
  rw [vtPtr, addr_gen, Nat.add_assoc]

theorem vtPtr_addr0 (b n i off : ℕ) :
    (vtPtr b n i).limb 0 * Parameters.gpow off = Parameters.gpow ((bases b (vtSizes n)).getD i 0 + off) := by
  rw [vtPtr, addr_k]

/-- **`bk`'s words**: block `b`'s log-height. -/
theorem vt_bk_get {logMem : ℕ} {rowsN : List ℕ} (hl : rowsN.length = 6) {b : ℕ} (hb : b < 102) :
    (blockKappas (gen ^ logMem) (rowsN.map fun m ↦ gen ^ log2Ceil m)).getD b 0 =
      gen ^ vtKs logMem (fun t => log2Ceil (rowsN.getD t 0)) b := by
  obtain ⟨h8, -⟩ := vt_src_bound b hb
  rw [blockKappas, getD_map_range _ _ hb, vtKs, pow_add]
  congr 1
  generalize blockKappaSrc.getD b 0 = s at h8
  obtain ⟨r0, r1, r2, r3, r4, r5, rfl⟩ : ∃ r0 r1 r2 r3 r4 r5, rowsN = [r0, r1, r2, r3, r4, r5] := by
    match rowsN, hl with
    | [r0, r1, r2, r3, r4, r5], _ => exact ⟨r0, r1, r2, r3, r4, r5, rfl⟩
  interval_cases s <;> simp [kappaBase]

end
end LeanVM.Guest.B1.VerifySub
