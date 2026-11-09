/-
  LeanVM.Prover.Keccak.Product

  The executable prover's coefficients of the product polynomial `G` are the specification's
  `gList (Gpoly …)`.
-/

module

public import LeanVM.Prover.Keccak.States

/-!
# The product polynomial

* `bitE_embedMask`: the embedding of a mask by byte tables is the sum of the embeddings of its
  bits, coefficient by coefficient; `embSum_eq`: so the specification's `Σ_i b_i·emb_i` (`SP`,
  and `kP` at the full mask) is the binary polynomial of `embedMask`;
* `testBit_clmul`: the carry-less product is `mulGF2` on bit lists; `coeff_Gterm`: χ's product
  `Gterm` has the bits of `chiProduct` as coefficients;
* `gCoeffs_eq`: **`gCoeffs` of the masks is `gList (Gpoly T P point w)`**.
-/

namespace LeanVM.Prover.KeccakGkr

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakGkr Finset
open Polynomial

@[expose] public section

/-! ## Embeddings -/

theorem bitE_foldl_xor (p : ℕ → Bool) (v : ℕ → ℕ) (c : ℕ) : ∀ (n a : ℕ),
    bitE (((List.range n).foldl (fun acc t ↦ if p t then acc ^^^ v t else acc) a).testBit c) =
      bitE (a.testBit c) + ∑ t ∈ range n, bitE (p t && (v t).testBit c)
  | 0, a => by simp
  | n + 1, a => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Finset.sum_range_succ, ← add_assoc, ← bitE_foldl_xor p v c n a]
    split_ifs with h
    · rw [Nat.testBit_xor, bitE_xor, h, Bool.true_and]
    · rw [Bool.not_eq_true] at h
      rw [h, Bool.false_and, bitE_false, add_zero]

theorem bitE_embedByte (off b c : ℕ) :
    bitE ((embedByte off b).testBit c) =
      ∑ t ∈ range 8, bitE (b.testBit t && (rmfeEmbed.getD (off + t) 0).testBit c) := by
  rw [embedByte, bitE_foldl_xor, Nat.zero_testBit, bitE_false, zero_add]

/-- **The embedding of a mask**, coefficient by coefficient: `Σ_{i ∈ mask} emb_i`. -/
theorem bitE_embedMask (m c : ℕ) :
    bitE ((embedMask m).testBit c) =
      ∑ i ∈ range 16, bitE (m.testBit i && (rmfeEmbed.getD i 0).testBit c) := by
  rw [embedMask, Nat.testBit_xor, bitE_xor, embedLow, embedHigh,
    array_getD_ofFn_lt _ (Nat.mod_lt _ (by norm_num)),
    array_getD_ofFn_lt _ (Nat.mod_lt _ (by norm_num)), bitE_embedByte, bitE_embedByte,
    show 16 = 8 + 8 from rfl, Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun t ht ↦ ?_
    rw [testBit_mod_256 _ (Finset.mem_range.1 ht), zero_add]
  · refine Finset.sum_congr rfl fun t ht ↦ ?_
    rw [testBit_div_256 _ (Finset.mem_range.1 ht)]

theorem bitE_eq_zero {b : Bool} (h : bitE b = 0) : b = false := by
  cases b
  · rfl
  · exact absurd h one_ne_zero

theorem rmfeEmbed_lt (i : ℕ) : rmfeEmbed.getD i 0 < 2 ^ 24 := by
  rw [rmfeEmbed_eq]
  by_cases hi : i < 16
  · revert i; decide
  · rw [List.getD_eq_default _ _ (by simp [embedLit]; omega)]; norm_num

theorem embedMask_lt (m : ℕ) : embedMask m < 2 ^ 24 := by
  refine Nat.lt_pow_two_of_testBit _ fun c hc ↦ bitE_eq_zero ?_
  rw [bitE_embedMask]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [Nat.testBit_eq_false_of_lt
      ((rmfeEmbed_lt i).trans_le (Nat.pow_le_pow_right (by norm_num) hc)),
    Bool.and_false, bitE_false]

theorem coeff_polyOfBits_bitsFrom (n k c : ℕ) :
    (polyOfBits (bitsFrom n k)).coeff c = bitE (decide (c < k) && n.testBit c) := by
  rw [coeff_polyOfBits, bitsFrom_getD]

/-- **A combination of the embeddings with `0/1` weights** is the binary polynomial of the
mask's embedding. -/
theorem embSum_eq (b : ℕ → Bool) (m : ℕ) (hm : ∀ i < 16, m.testBit i = b i) :
    ∑ i ∈ range 16, C (bitE (b i)) * embP i = polyOfBits (bitsFrom (embedMask m) 24) := by
  refine Polynomial.ext fun c ↦ ?_
  rw [finsetSum_coeff, coeff_polyOfBits_bitsFrom]
  simp only [coeff_C_mul, embP_coeff]
  by_cases hc : c < 24
  · simp only [hc, ite_true, decide_true, Bool.true_and]
    rw [bitE_embedMask]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [hm i (Finset.mem_range.1 hi), bitE_and]
  · simp [hc]

theorem kP_eq : kP = polyOfBits (bitsFrom kappaBits 24) :=
  embSum_eq (fun _ ↦ true) 0xFFFF (by decide)

theorem polyOfBits_bitsFrom_xor (a b k : ℕ) :
    polyOfBits (bitsFrom a k) + polyOfBits (bitsFrom b k) = polyOfBits (bitsFrom (a ^^^ b) k) := by
  refine Polynomial.ext fun c ↦ ?_
  rw [coeff_add, coeff_polyOfBits_bitsFrom, coeff_polyOfBits_bitsFrom, coeff_polyOfBits_bitsFrom,
    Nat.testBit_xor]
  by_cases hc : c < k
  · simp only [hc, decide_true, Bool.true_and, bitE_xor]
  · simp [hc]

/-! ## Carry-less products -/

theorem xorL_getD : ∀ (A B : List Bool) (c : ℕ),
    (xorL A B).getD c false = (A.getD c false ^^ B.getD c false)
  | [], B, c => by simp [xorL]
  | x :: xs, [], c => by simp [xorL]
  | x :: xs, y :: ys, 0 => by simp [xorL]
  | x :: xs, y :: ys, c + 1 => by
    rw [xorL, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, xorL_getD xs ys c]

theorem testBit_clmul (B : List Bool) (b : ℕ) (hB : ∀ c, B.getD c false = b.testBit c) :
    ∀ (k a c : ℕ), (mulGF2 (bitsFrom a k) B).getD c false = (clmul k a b).testBit c
  | 0, a, c => by simp [bitsFrom, mulGF2, clmul]
  | k + 1, a, c => by
    rw [bitsFrom, mulGF2, xorL_getD, clmul, Nat.testBit_xor]
    congr 1
    · split_ifs with h1 h2 h2
      · exact hB c
      · simp at h1; exact absurd h1 h2
      · simp at h1; omega
      · simp
    · cases c with
      | zero => simp
      | succ c =>
        rw [List.getD_cons_succ, testBit_clmul B b hB k (a / 2) c, Nat.testBit_shiftLeft]
        simp

theorem bitsFrom_getD_lt {b k : ℕ} (hb : b < 2 ^ k) (c : ℕ) :
    (bitsFrom b k).getD c false = b.testBit c := by
  rw [bitsFrom_getD]
  by_cases hc : c < k
  · simp [hc]
  · rw [Nat.testBit_eq_false_of_lt (hb.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp

theorem coeff_mul_embed (a b : ℕ) (hb : b < 2 ^ 24) (c : ℕ) :
    (polyOfBits (bitsFrom a 24) * polyOfBits (bitsFrom b 24)).coeff c =
      bitE ((clmul 24 a b).testBit c) := by
  rw [← polyOfBits_mulGF2, coeff_polyOfBits,
    testBit_clmul (bitsFrom b 24) b (bitsFrom_getD_lt hb) 24 a c]

/-- **χ's product** has the bits of `chiProduct` as coefficients. -/
theorem coeff_Gterm {T : States} {P z j : ℕ} {m0 m1 m2 : ℕ}
    (h0 : ∀ i < 16, m0.testBit i = Lb (stAt T P z i) j)
    (h1 : ∀ i < 16, m1.testBit i = Lb (stAt T P z i) (keccakAlong j 1))
    (h2 : ∀ i < 16, m2.testBit i = Lb (stAt T P z i) (keccakAlong j 2)) (c : ℕ) :
    (Gterm T P z j).coeff c =
      bitE ((chiProduct (embedMask m0) (embedMask m1) (embedMask m2)).testBit c) := by
  have hs0 : SP T P z j = polyOfBits (bitsFrom (embedMask m0) 24) := embSum_eq _ _ h0
  have hs1 : SP T P z (keccakAlong j 1) = polyOfBits (bitsFrom (embedMask m1) 24) :=
    embSum_eq _ _ h1
  have hs2 : SP T P z (keccakAlong j 2) = polyOfBits (bitsFrom (embedMask m2) 24) :=
    embSum_eq _ _ h2
  rw [Gterm, hs0, hs1, hs2, kP_eq, polyOfBits_bitsFrom_xor, coeff_add,
    coeff_mul_embed _ _ (embedMask_lt _), coeff_mul_embed _ _ (embedMask_lt _), chiProduct,
    Nat.testBit_xor, bitE_xor]

/-! ## The coefficients -/

/-- A loop of rows: entry `c` of the result is `Σ_z f z c`. -/
theorem foldl_rows (k : ℕ) (f : ℕ → ℕ → E) (step : Array E → ℕ → Array E)
    (hstep : ∀ G z, step G z = Array.ofFn (n := k) fun c ↦ G.getD c.val 0 + f z c.val) :
    ∀ n, ∀ c < k, ((List.range n).foldl step (Array.replicate k 0)).getD c 0 =
      ∑ z ∈ range n, f z c
  | 0, c, hc => by simp [Array.getD_eq_getD_getElem?, hc]
  | n + 1, c, hc => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hstep,
      array_getD_ofFn_lt _ hc, foldl_rows k f step hstep n c hc, Finset.sum_range_succ]

theorem array_getD_map {α : Type} (a : Array α) (f : α → ℕ) {j : ℕ} (hj : j < a.size) (d : α) :
    (a.map f).getD j 0 = f (a.getD j d) := by
  simp [Array.getD_eq_getD_getElem?, hj]

theorem packMasks_size (col : ℕ → K) (P e z : ℕ) : (packMasks col P e z).size = 1600 := by
  simp [packMasks]

theorem gPack_getD (w : Array E) (S : Array ℕ) {c : ℕ} (hc : c < 47) :
    (gPack (weightTabs w) S).getD c 0 = ∑ j ∈ range 1600,
      if (chiProduct (S.getD j 0) (S.getD (keccakAlong j 1) 0)
        (S.getD (keccakAlong j 2) 0)).testBit c then w.getD j 0 else 0 := by
  rw [gPack, array_getD_ofFn_lt _ hc, sumRange_eq, show 1600 = 200 * 8 from rfl, sum_range_mul]
  refine Finset.sum_congr rfl fun q hq ↦ ?_
  have hq' := Finset.mem_range.1 hq
  rw [weightTabs, array_getD_ofFn_lt _ hq', byteSums_getD _ (packBits_lt _ 8)]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  have ht' := Finset.mem_range.1 ht
  rw [testBit_packBits, decide_eq_true ht', Bool.true_and, array_getD_ofFn_lt _ (by omega)]

/-- **`G`'s coefficients.** -/
theorem gCoeffs_eq {P : ℕ} {col' col : ℕ → K} (hcol : ColAgree P col' col) {d : ℕ} (hd : d < 12)
    {point : List E} (hpt : point.length = P + 1) (w : List E) :
    gCoeffs P (layerMasks col' P (11 - d)) point w =
      gList (Gpoly (statesAt (P + 4) col (d + 1)) P point w) := by
  let T := statesAt (P + 4) col (d + 1)
  have hG : ∀ c < 47, ((List.range (2 ^ (P + 1))).foldl (fun G z ↦
      let gz := gPack (weightTabs w.toArray)
        (((layerMasks col' P (11 - d)).getD z #[]).map embedMask)
      let e := (eqTable point).getD z 0
      Array.ofFn (n := 47) fun c ↦ G.getD c.val 0 + e * gz.getD c.val 0)
      (Array.replicate 47 0)).getD c 0 = (Gpoly T P point w).coeff c := by
    intro c hc
    rw [foldl_rows 47 (fun z c ↦ (eqTable point).getD z 0 * (gPack (weightTabs w.toArray)
      (((layerMasks col' P (11 - d)).getD z #[]).map embedMask)).getD c 0) _ (fun _ _ ↦ rfl)
      _ c hc]
    simp only [Gpoly, finsetSum_coeff, coeff_C_mul]
    refine Finset.sum_congr rfl fun z hz ↦ ?_
    have hz' := Finset.mem_range.1 hz
    rw [eqTable_getD_lt _ (by rw [hpt]; exact hz'), gPack_getD _ _ hc]
    refine congrArg (eqAt point z * ·) ?_
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj' := Finset.mem_range.1 hj
    have hrow : ((layerMasks col' P (11 - d)).getD z #[]).size = 1600 := by
      rw [layerMasks, array_getD_ofFn_lt _ hz', packMasks_size]
    have hS : ∀ j' < 1600, (((layerMasks col' P (11 - d)).getD z #[]).map embedMask).getD j' 0 =
        embedMask (((layerMasks col' P (11 - d)).getD z #[]).getD j' 0) :=
      fun j' hj'' ↦ array_getD_map _ _ (by rw [hrow]; exact hj'') 0
    rw [hS j hj', hS _ (keccakAlong_lt 1 hj'), hS _ (keccakAlong_lt 2 hj'), ite_bitE,
      array_getD_toArray, coeff_Gterm (T := T)
        (fun i hi ↦ testBit_layerMasks hcol hd hz' hi hj')
        (fun i hi ↦ testBit_layerMasks hcol hd hz' hi (keccakAlong_lt 1 hj'))
        (fun i hi ↦ testBit_layerMasks hcol hd hz' hi (keccakAlong_lt 2 hj'))]
  refine List.ext_getElem (by rw [gList_length]; simp [gCoeffs]) fun c h₁ h₂ ↦ ?_
  have hc : c < 47 := by simpa [gCoeffs] using h₁
  rw [← List.getD_eq_getElem _ 0 h₂, gList_getD _ hc, ← hG c hc]
  simp [gCoeffs]

end
end LeanVM.Prover.KeccakGkr
