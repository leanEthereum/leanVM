module

public import Quantum.Xmss.Assembly.TrialsOff
public import Quantum.Sphincs.Assembly.PathBad

@[expose] public section

/-!
# No WOTS+C trial block is a `k`-cell of an in-table path

A key's counter search reads, at each trial, the `k` cell of the one-block trial input
`PK.seed ‖ ADRS_enc(K) ‖ m ‖ BE32(c)` (68 bytes, `TrialBlock`). `TrialsOff w h v`: no round of an
in-table slot's honest path (PathBad's `sCellK` at the public data `w = (PK.seed, π, k, k')`, the
key `h` and the values `v`) has a trial block as its `k`-cell, so no trial reads a `k` cell the
template programs on an in-table path (`Quantum.Sphincs.Assembly.TrialHit` adds the `H_msg` cells,
which no trial block meets by its length). Here the data violating it are bounded, with the
generic count of leanXMSS's `Quantum.Xmss.Assembly.TrialsOff` (`frac_pathTrial_le`).

* **First rounds** (`not_inTable_of_trialBlock`): a trial block names an encoding slot (or none),
  while the first `k`-cell of an in-table path is its first block, which names the slot
  (`slotOfBlock_slotBlk`). So a violation is a later round's `k`-cell in `trialSet`
  (`exists_rnd_of_not_trialsOff`), at most `2^326` blocks (`card_trialSet_le`: `2^128` seeds,
  `3 · 2^36` keys, `2^128` values, `2^32` counters).
* `trialsOff_good_frac_le`, `trialsOff_frac_le`: `¬TrialsOff` for at most the bad permutations plus
  `N² / |X| + N² (G + 1) / |Z| + N |trialSet| / |X|`, `N = 8 |xI|`;
  `trialsOff_frac_le_keccak`: at most `2^-400` (`G = 18`: the bad permutations `2^-777`, the
  collisions `2^-407`, the trial blocks `2^-700`).
-/

open scoped ENNReal

open Quantum Quantum.Sponge Sphincs
open HashSig (Digest PublicParameter HashInput littleEndianBytes)
open Quantum.Xmss (X Z blocks blockOf firstBlock head?_blocks)
open Quantum.Xmss.Assembly (rnK famK rnds mem_rnds rnK_zero frac_pathTrial_le XW
  card_filter_le_add_of_imp inv_card_mul_card_filter_comp_fst natCast_div_eq_ofReal rnCard_X
  rnCard_Z permTerm_le_keccak card_prod_four card_publicParameter card_digest)

namespace Quantum.Sphincs.Assembly

/-! ## The trial blocks -/

/-- **The input of a WOTS+C trial** of key `K` on the value `m` at counter `c` under `PK.seed = P`:
`PK.seed ‖ ADRS_enc(K) ‖ m ‖ BE32(c)`. -/
def encTrialIn (P : PublicParameter) (K : Key) (m : Digest) (c : EncodingCounter) : HashInput :=
  addressedHashInput P (hashDomainFields (.encoding K.1 K.2.1 K.2.2))
    (littleEndianBytes 16 m ++ bigEndianBytes 4 c)

/-- **A trial block**: the block of a one-block trial input, at any `PK.seed`, key, signed value and
counter. -/
def TrialBlock (x : X) : Prop :=
  ∃ (P : PublicParameter) (K : Key) (m : Digest) (c : EncodingCounter),
    blocks (encTrialIn P K m c) = [x]

/-- **A trial block names no in-table slot**: its address is an encoding's. -/
theorem not_inTable_of_trialBlock {x : X} (hx : TrialBlock x) (pk : PublicKey) {s : Slot}
    (hs : slotOfBlock pk x = some s) : ¬InTable s := by
  obtain ⟨P, K, m, c, hb⟩ := hx
  have hh := head?_blocks (encTrialIn P K m c)
  rw [hb, List.head?_cons] at hh
  rw [Option.some.inj hh, encTrialIn, slotOfBlock_addressedHashInput] at hs
  split_ifs at hs
  rw [slotOfAddress_hashDomainFields (.encoding K.1 K.2.1 K.2.2) trivial] at hs
  rw [← Option.some.inj hs]
  exact id

/-- The block of the trial input at a seed, key, value and counter. -/
def trialBlkOf (a : PublicParameter × Key × Digest × EncodingCounter) : X :=
  (blocks (encTrialIn a.1 a.2.1 a.2.2.1 a.2.2.2)).getD 0 0

/-- **The trial blocks** as a finite set (irreducible after `mem_trialSet_of`). -/
def trialSet : Finset X :=
  Finset.univ.image trialBlkOf

theorem mem_trialSet_of (a : PublicParameter × Key × Digest × EncodingCounter) :
    trialBlkOf a ∈ trialSet := by
  simp only [trialSet, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨a, rfl⟩

attribute [irreducible] trialSet

theorem mem_trialSet {x : X} (hx : TrialBlock x) : x ∈ trialSet := by
  obtain ⟨P, K, m, c, hb⟩ := hx
  have h := mem_trialSet_of (P, K, m, c)
  have e : trialBlkOf (P, K, m, c) = x := by
    show (blocks (encTrialIn P K m c)).getD 0 0 = x
    rw [hb]
    rfl
  rw [e] at h
  exact h

theorem card_key_le : Fintype.card Key ≤ 2 ^ 38 := by
  simp only [Key, Fintype.card_prod, Fintype.card_fin]
  norm_num [layerCount, indexBits, layerHeight, topLayer]

theorem card_encodingCounter : Fintype.card EncodingCounter = 2 ^ 32 := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]
  rfl

set_option exponentiation.threshold 4096 in
/-- **At most `2^326` trial blocks.** -/
theorem card_trialSet_le : trialSet.card ≤ 2 ^ 326 := by
  unfold trialSet
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_univ, card_prod_four card_publicParameter rfl card_digest card_encodingCounter]
  calc 2 ^ 128 * (Fintype.card Key * (2 ^ 128 * 2 ^ 32)) ≤
        2 ^ 128 * (2 ^ 38 * (2 ^ 128 * 2 ^ 32)) := by gcongr; exact card_key_le
    _ = 2 ^ 326 := by norm_num

/-! ## Trial blocks among the in-table cells -/

/-- **No trial block among the in-table `k`-cells** at the public data `w = (PK.seed, π, k, k')`,
the key `h` and the values `v`: no round of an in-table slot's honest path has a trial block as its
`k`-cell. -/
def TrialsOff (w : XW) (h : Z → X) (v : ValPos → Digest) : Prop :=
  ∀ s, InTable s → ∀ j < nBlk w.1 s, ¬TrialBlock (sCellK w h s v j)

/-- **A trial block among the in-table cells is a later `k`-cell of an in-table path in
`trialSet`**: the first `k`-cells name in-table slots. -/
theorem exists_rnd_of_not_trialsOff {w : XW} {h : Z → X} {v : ValPos → Digest}
    (hb : ¬TrialsOff w h v) :
    ∃ a ∈ rnds xI (xLen w.1), 1 ≤ a.2 ∧
      famK w.2.1 (xBlk w.1 v) h w.2.2.1 w.2.2.2 a ∈ trialSet := by
  simp only [TrialsOff, not_forall, not_not] at hb
  obtain ⟨s, hs, j, hj, hT⟩ := hb
  have hj0 : j ≠ 0 := by
    rintro rfl
    have e : sCellK w h s v 0 = slotBlk w.1 s v 0 := rnK_zero ..
    rw [e] at hT
    exact not_inTable_of_trialBlock hT ⟨w.1, 0⟩ (slotOfBlock_slotBlk w.1 0 v hs) hs
  refine ⟨(slotOutPos s, j), mem_rnds.mpr ⟨mem_xI.mpr (inPos_slotOutPos hs), ?_⟩,
    Nat.one_le_iff_ne_zero.mpr hj0, ?_⟩
  · show j < nBlk w.1 (outSlot (slotOutPos s))
    rw [outSlot_slotOutPos hs]
    exact hj
  · have e : famK w.2.1 (xBlk w.1 v) h w.2.2.1 w.2.2.2 (slotOutPos s, j) = sCellK w h s v j := by
      show rnK w.2.1 h w.2.2.1 w.2.2.2 (slotBlk w.1 (outSlot (slotOutPos s)) v) j = _
      rw [outSlot_slotOutPos hs]
      rfl
    rw [e]
    exact mem_trialSet hT

/-! ## The fraction of the public coordinates -/

open scoped Classical in
/-- **The trial event on good permutations**: `PermGood π G ∧ ¬TrialsOff` for at most a fraction
`N² / |X| + N² (G + 1) / |Z| + N |trialSet| / |X|` of the public coordinates, `N = 8 |xI|`. -/
theorem trialsOff_good_frac_le (G : ℕ) :
    (Fintype.card (((Z → X) × XW) × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
          PermGood y.1.2.2.1 G ∧ ¬TrialsOff y.1.2 y.1.1 y.2).card ≤
      ((8 * xI.card * (8 * xI.card) : ℕ) : ℝ≥0∞) / Fintype.card X +
        ((8 * xI.card * (8 * xI.card) * (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z +
        ((8 * xI.card * trialSet.card : ℕ) : ℝ≥0∞) / Fintype.card X :=
  frac_pathTrial_le rnEquiv (fun q ↦ q.2.1) (fun q ↦ xBlk q.1 q.2.2) (fun q ↦ xLen q.1) xI
    (fun q ↦ xBlk_injOn q.1 q.2.2) G _ (fun q ↦ card_rnds_xI_le q.1) trialSet _ fun q t hb ↦
      ⟨hb.1, exists_rnd_of_not_trialsOff (w := (q.1, q.2.1, t.2.1, t.2.2)) (h := t.1)
        (v := q.2.2) hb.2⟩

open scoped Classical in
/-- **The trial fraction of leanSPHINCS**: `¬TrialsOff` for at most the bad permutations plus
`N² / |X| + N² (G + 1) / |Z| + N |trialSet| / |X|`, `N = 8 |xI|`. -/
theorem trialsOff_frac_le (G : ℕ) :
    (Fintype.card (((Z → X) × XW) × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
          ¬TrialsOff y.1.2 y.1.1 y.2).card ≤
      ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
          Fintype.card (Equiv.Perm (X × Z)) +
        (((8 * xI.card * (8 * xI.card) : ℕ) : ℝ≥0∞) / Fintype.card X +
          ((8 * xI.card * (8 * xI.card) * (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z +
          ((8 * xI.card * trialSet.card : ℕ) : ℝ≥0∞) / Fintype.card X) := by
  set N := Fintype.card (((Z → X) × XW) × (ValPos → Digest))
  have hsub := card_filter_le_add_of_imp
    (fun y : ((Z → X) × XW) × (ValPos → Digest) ↦ ¬TrialsOff y.1.2 y.1.1 y.2)
    (fun y : ((Z → X) × XW) × (ValPos → Digest) ↦ ¬PermGood (permEquiv y).1 G)
    (fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
      PermGood y.1.2.2.1 G ∧ ¬TrialsOff y.1.2 y.1.1 y.2)
    fun y hy ↦ by
      by_cases hG : PermGood y.1.2.2.1 G
      · exact Or.inr ⟨hG, hy⟩
      · exact Or.inl hG
  calc (N : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
        ¬TrialsOff y.1.2 y.1.1 y.2).card
      ≤ (N : ℝ≥0∞)⁻¹ * (((Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
          ¬PermGood (permEquiv y).1 G).card : ℝ≥0∞) +
        (Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
          PermGood y.1.2.2.1 G ∧ ¬TrialsOff y.1.2 y.1.1 y.2).card) := by
        gcongr
        exact_mod_cast hsub
    _ = (N : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
          ¬PermGood (permEquiv y).1 G).card +
        (N : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
          PermGood y.1.2.2.1 G ∧ ¬TrialsOff y.1.2 y.1.1 y.2).card := mul_add _ _ _
    _ ≤ _ := by
        rw [inv_card_mul_card_filter_comp_fst permEquiv fun π ↦ ¬PermGood π G]
        exact add_le_add le_rfl (trialsOff_good_frac_le G)

set_option exponentiation.threshold 4096 in
/-- The trial term at Keccak's sizes, for `n ≤ 2^47` outputs and at most `2^326` trial blocks:
`2^376 / 2^1088`. -/
theorem trialsOffTerm_le {n m cX : ℕ} (hn : n ≤ 2 ^ 47) (hm : m ≤ 2 ^ 326)
    (hX : cX = 2 ^ 1088) : ((8 * n * m : ℕ) : ℝ≥0∞) / cX ≤ ENNReal.ofReal (1 / 2 ^ 700) := by
  subst hX
  have hK : 8 * n * m ≤ 2 ^ 376 :=
    calc 8 * n * m ≤ 8 * 2 ^ 47 * 2 ^ 326 := by gcongr
      _ = 2 ^ 376 := by norm_num
  rw [natCast_div_eq_ofReal _ (2 ^ 1088) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc ((8 * n * m : ℕ) : ℝ) / ((2 ^ 1088 : ℕ) : ℝ) ≤ 2 ^ 376 / 2 ^ 1088 := by
        rw [Nat.cast_pow, Nat.cast_ofNat]
        exact div_le_div_of_nonneg_right (by exact_mod_cast hK) (by positivity)
    _ ≤ 1 / 2 ^ 700 := by norm_num

set_option exponentiation.threshold 4096 in
open scoped Classical in
/-- **The trial fraction at Keccak's sizes**: `¬TrialsOff` for at most `2^-400` of the public
coordinates (with `G = 18`: the bad permutations `2^-777`, the collisions `2^-407`, the trial
blocks `2^-700`). -/
theorem trialsOff_frac_le_keccak :
    (Fintype.card (((Z → X) × XW) × (ValPos → Digest)) : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : ((Z → X) × XW) × (ValPos → Digest) ↦
          ¬TrialsOff y.1.2 y.1.1 y.2).card ≤
      ENNReal.ofReal (1 / 2 ^ 400) := by
  refine ((trialsOff_frac_le 18).trans (add_le_add permTerm_le_keccak
    (add_le_add (collTerms_le card_xI_le rnCard_X rnCard_Z)
      (trialsOffTerm_le card_xI_le card_trialSet_le rnCard_X)))).trans ?_
  rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 407)
      (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 700),
    ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2 ^ 777) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

end Quantum.Sphincs.Assembly

end
