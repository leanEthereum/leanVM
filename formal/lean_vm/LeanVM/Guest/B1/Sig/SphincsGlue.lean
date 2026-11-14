/-
  LeanVM.Guest.B1.Sig.SphincsGlue

  The addresses `verify_sig_lean_sphincs` builds between its stages (`lean_ethereum.py:4219-4220,
  4235-4236, 4239-4240`): each layer's `A0` and its key pair's `A1`, from the
  digest's leaves.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsT
public import LeanVM.Guest.B1.Sig.SphincsSoundDigest
public import LeanVM.Guest.B1.Sig.SphincsHash

/-!
# The layers' addresses

`G` is `lean_ethereum.py`. Layer `l`'s one-time key is `K_l(idx)`: its tree `layerTreeN T l` and its
leaf `layerLeafN T l` (`T` the digest's number, `SphincsSoundDigest`). The guest builds the key's
address cells from the leaves' bytes and their shifts (`lvals`, `tree_mid`):

* `sForsAddrs_vals` (`G:4219-4220`): `a0_b = lvals[8]·2^120 + tree_mid·2^112 + lvals[24]·2^104` is
  `adrsCell0 0 (layerTreeN T 0)`, `key_b = lvals[0]·2^56` is `adrsCell1 0 (layerLeafN T 0) 0 0`;
* `sMidAddrs_vals` (`G:4234-4235`): `a0_m = 2^24 + tree_mid·2^120 + lvals[24]·2^112`, `key_m =
  lvals[8]·2^56`;
* `sTopAddrs_vals` (`G:4238-4239`): `key_t = tree_mid·2^56 + lvals[24]·2^48`, `a0_t = 2^25`;
* `layerAddrs`: all three as `sA0Of l`, `sA1Of l`.

Field addition is XOR, so a sum of words of disjoint bits is the word of their sum
(`eOfNat128_shift_add`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

variable {rd : Reader} {σ : Val}

/-! ## Address cells as words -/

/-- **`A0` as a word**: the layer at bit `24`, the tree's three low bytes reversed at bits `120`,
`112`, `104`. -/
theorem adrsCell0_eq192 {layer t : Nat} (hl : layer < 256) (ht : t < 2 ^ 24) :
    adrsCell0 layer t =
      eOfNat128 (layer * 2 ^ 24 + 2 ^ 104 * (2 ^ 8 * (2 ^ 8 * (t % 256) + t / 256 % 256) + t / 65536)) := by
  unfold adrsCell0
  rw [cellOf128_eq_eOfNat128 (by simp only [beWordAt, Nat.reducePow, Nat.reduceMul]; omega)]
  congr 1
  simp only [beWordAt, Nat.reducePow, Nat.reduceMul]
  omega

/-- **A key pair's `A1` as a word** (type `WOTS_HASH`): its two low bytes reversed at bits `56`,
`48`. -/
theorem adrsCell1_key_eq192 {kp : Nat} (hk : kp < 2 ^ 16) :
    adrsCell1 0 kp 0 0 = eOfNat128 (2 ^ 48 * (2 ^ 8 * (kp % 256) + kp / 256)) := by
  rw [adrsCell1_eq]
  congr 1
  simp only [adrsNat1, beWordAt, Nat.reducePow, Nat.reduceMul]
  omega

/-- A byte value times `2^s`. -/
theorem mul_lit_pow {v s : Nat} (hs : s < 128) (h : 2 ^ (s % 64) * v < 2 ^ 64) (e : lit (2 ^ s) = pw s) :
    eOfNat v * lit (2 ^ s) = eOfNat128 (2 ^ s * v) := by
  rw [e, pw_mul hs h]

theorem lit120 : lit (2 ^ 120) = pw 120 := rfl
theorem lit112 : lit (2 ^ 112) = pw 112 := rfl
theorem lit104 : lit (2 ^ 104) = pw 104 := rfl
theorem lit56 : lit (2 ^ 56) = pw 56 := rfl
theorem lit48 : lit (2 ^ 48) = pw 48 := rfl

/-! ## The leaves' values -/

/-- The leaves' values `sp_leaf_shifts` gives: `lvals[0]`, `lvals[8]`, `lvals[16]`, `lvals[24]`. -/
theorem lvals_four {T : Nat} (hl : LValsAt σ T) :
    σ (sLVal 0) = eOfNat (layerLeafN T 0) ∧ σ (sLVal 8) = eOfNat (layerLeafN T 1) ∧
      σ (sLVal 16) = eOfNat (layerLeafN T 2) ∧ σ (sLVal 24) = eOfNat (layerLeafN T 2 / 256) := by
  have h0 := hl 0 (by norm_num) 0 (by simp [sLeafLen])
  have h1 := hl 1 (by norm_num) 0 (by simp [sLeafLen])
  have h2 := hl 2 (by norm_num) 0 (by simp [sLeafLen])
  have h3 := hl 2 (by norm_num) 8 (by simp [sLeafLen])
  simp only [sLeafOff, Nat.shiftRight_eq_div_pow, Nat.mul_zero, Nat.add_zero, Nat.reduceMul,
    Nat.reduceAdd, pow_zero, Nat.div_one] at h0 h1 h2 h3
  exact ⟨h0, h1, h2, h3⟩

theorem leaves_ltC (T : Nat) : layerLeafN T 0 < 256 ∧ layerLeafN T 1 < 256 ∧ layerLeafN T 2 < 1024 := by
  obtain ⟨a, b, c⟩ := layerLeafN_lt' T
  exact ⟨by simpa using a, by simpa using b, by simpa using c⟩

/-- The tree index's middle byte is the top leaf's low byte. -/
theorem treeMid_eq {T : Nat} (hm : σ sTreeMid = eOfNat (byteN T 31)) :
    σ sTreeMid = eOfNat (layerLeafN T 2 % 256) := by
  rw [hm, ← layerLeaf2_low]
  norm_num

/-! ## The glue -/

/-- **The bottom layer's address** (`G:4219-4220`): `a0_b` is the bottom key's tree's `A0`, `key_b`
its leaf's `A1`. -/
theorem sForsAddrs_vals {T : Nat} (hl : LValsAt σ T) (hm : σ sTreeMid = eOfNat (byteN T 31))
    (h : AtomsHold rd σ sForsAddrs) :
    σ sA0B = adrsCell0 0 (layerTreeN T 0) ∧ σ sKeyB = adrsCell1 0 (layerLeafN T 0) 0 0 := by
  obtain ⟨l0, l1, -, l3⟩ := lvals_four hl
  obtain ⟨b0, b1, b2⟩ := leaves_ltC T
  have tm := treeMid_eq hm
  have c0 : σ (.n 1372) = lit (2 ^ 120) := h.atom (a := .const _ _) (by simp [sForsAddrs, cst])
  have m1 : σ (.n 1373) = σ (sLVal 8) * σ (.n 1372) := h.atom (a := .mul _ _ _) (by simp [sForsAddrs, mulS])
  have c2 : σ (.n 1374) = lit (2 ^ 112) := h.atom (a := .const _ _) (by simp [sForsAddrs, cst])
  have m3 : σ (.n 1375) = σ sTreeMid * σ (.n 1374) := h.atom (a := .mul _ _ _) (by simp [sForsAddrs, mulS])
  have a4 : σ (.n 1376) = σ (.n 1373) + σ (.n 1375) := h.atom (a := .add _ _ _) (by simp [sForsAddrs, addS])
  have c5 : σ (.n 1377) = lit (2 ^ 104) := h.atom (a := .const _ _) (by simp [sForsAddrs, cst])
  have m6 : σ (.n 1378) = σ (sLVal 24) * σ (.n 1377) := h.atom (a := .mul _ _ _) (by simp [sForsAddrs, mulS])
  have a7 : σ sA0B = σ (.n 1376) + σ (.n 1378) := h.atom (a := .add _ _ _) (by simp [sForsAddrs, addS])
  have c8 : σ (.n 1380) = lit (2 ^ 56) := h.atom (a := .const _ _) (by simp [sForsAddrs, cst])
  have m9 : σ sKeyB = σ (sLVal 0) * σ (.n 1380) := h.atom (a := .mul _ _ _) (by simp [sForsAddrs, mulS])
  refine ⟨?_, ?_⟩
  · rw [a7, a4, m1, m3, m6, c0, c2, c5, l1, tm, l3,
      mul_lit_pow (by norm_num) (by norm_num; omega) lit120,
      mul_lit_pow (by norm_num) (by norm_num; omega) lit112,
      mul_lit_pow (by norm_num) (by norm_num; omega) lit104,
      show 2 ^ 120 * layerLeafN T 1 = 2 ^ 112 * (2 ^ 8 * layerLeafN T 1) by ring,
      eOfNat128_shift_add (k := 8) (by omega),
      show 2 ^ 112 * (2 ^ 8 * layerLeafN T 1 + layerLeafN T 2 % 256) =
        2 ^ 104 * (2 ^ 8 * (2 ^ 8 * layerLeafN T 1 + layerLeafN T 2 % 256)) by ring,
      eOfNat128_shift_add (k := 8) (by omega),
      adrsCell0_eq192 (by norm_num) (by simp only [layerTreeN]; norm_num; omega)]
    congr 1
    simp only [layerTreeN, ↓reduceIte]
    have t1 : (layerLeafN T 1 + 2 ^ 8 * layerLeafN T 2) / 256 = layerLeafN T 2 := by omega
    have t2 : (layerLeafN T 1 + 2 ^ 8 * layerLeafN T 2) % 256 = layerLeafN T 1 := by omega
    have t3 : (layerLeafN T 1 + 2 ^ 8 * layerLeafN T 2) / 65536 = layerLeafN T 2 / 256 := by
      rw [show (65536 : Nat) = 256 * 256 by norm_num, ← Nat.div_div_eq_div_mul, t1]
    rw [t1, t2, t3]
    ring
  · rw [m9, c8, l0, mul_lit_pow (by norm_num) (by norm_num; omega) lit56,
      adrsCell1_key_eq192 (by omega)]
    congr 1
    omega

/-- **The middle layer's address** (`G:4234-4235`). -/
theorem sMidAddrs_vals {T : Nat} (hl : LValsAt σ T) (hm : σ sTreeMid = eOfNat (byteN T 31))
    (h : AtomsHold rd σ sMidAddrs) :
    σ (sA0Of 1) = adrsCell0 1 (layerTreeN T 1) ∧ σ (sA1Of 1) = adrsCell1 0 (layerLeafN T 1) 0 0 := by
  obtain ⟨-, l1, -, l3⟩ := lvals_four hl
  obtain ⟨b0, b1, b2⟩ := leaves_ltC T
  have tm := treeMid_eq hm
  have c0 : σ (.n 5398) = lit (2 ^ 24) := h.atom (a := .const _ _) (by simp [sMidAddrs, cst])
  have c1 : σ (.n 5399) = lit (2 ^ 120) := h.atom (a := .const _ _) (by simp [sMidAddrs, cst])
  have m2 : σ (.n 5400) = σ sTreeMid * σ (.n 5399) := h.atom (a := .mul _ _ _) (by simp [sMidAddrs, mulS])
  have a3 : σ (.n 5401) = σ (.n 5398) + σ (.n 5400) := h.atom (a := .add _ _ _) (by simp [sMidAddrs, addS])
  have c4 : σ (.n 5402) = lit (2 ^ 112) := h.atom (a := .const _ _) (by simp [sMidAddrs, cst])
  have m5 : σ (.n 5403) = σ (sLVal 24) * σ (.n 5402) := h.atom (a := .mul _ _ _) (by simp [sMidAddrs, mulS])
  have a6 : σ (sA0Of 1) = σ (.n 5401) + σ (.n 5403) := h.atom (a := .add _ _ _) (by simp [sMidAddrs, addS])
  have c7 : σ (.n 5405) = lit (2 ^ 56) := h.atom (a := .const _ _) (by simp [sMidAddrs, cst])
  have m8 : σ (sA1Of 1) = σ (sLVal 8) * σ (.n 5405) := h.atom (a := .mul _ _ _) (by simp [sMidAddrs, mulS])
  refine ⟨?_, ?_⟩
  · rw [a6, a3, m2, m5, c0, c1, c4, tm, l3,
      mul_lit_pow (by norm_num) (by norm_num; omega) lit120,
      mul_lit_pow (by norm_num) (by norm_num; omega) lit112, add_assoc,
      show 2 ^ 120 * (layerLeafN T 2 % 256) = 2 ^ 112 * (2 ^ 8 * (layerLeafN T 2 % 256)) by ring,
      eOfNat128_shift_add (k := 8) (by omega), lit_eq _ (by norm_num), add_comm, ← eOfNat128_xor,
      two_pow_mul_xor (by norm_num),
      adrsCell0_eq192 (by norm_num) (by simp only [layerTreeN]; norm_num; omega)]
    congr 1
    simp only [layerTreeN, show (1 : Nat) ≠ 0 by decide, ↓reduceIte]
    omega
  · rw [m8, c7, l1, mul_lit_pow (by norm_num) (by norm_num; omega) lit56,
      adrsCell1_key_eq192 (by omega)]
    congr 1
    omega

/-- **The top layer's address** (`G:4238-4239`): its tree is `0`. -/
theorem sTopAddrs_vals {T : Nat} (hl : LValsAt σ T) (hm : σ sTreeMid = eOfNat (byteN T 31))
    (h : AtomsHold rd σ sTopAddrs) :
    σ (sA0Of 2) = adrsCell0 2 (layerTreeN T 2) ∧ σ (sA1Of 2) = adrsCell1 0 (layerLeafN T 2) 0 0 := by
  obtain ⟨-, -, -, l3⟩ := lvals_four hl
  obtain ⟨b0, b1, b2⟩ := leaves_ltC T
  have tm := treeMid_eq hm
  have c0 : σ (.n 5556) = lit (2 ^ 56) := h.atom (a := .const _ _) (by simp [sTopAddrs, cst])
  have m1 : σ (.n 5557) = σ sTreeMid * σ (.n 5556) := h.atom (a := .mul _ _ _) (by simp [sTopAddrs, mulS])
  have c2 : σ (.n 5558) = lit (2 ^ 48) := h.atom (a := .const _ _) (by simp [sTopAddrs, cst])
  have m3 : σ (.n 5559) = σ (sLVal 24) * σ (.n 5558) := h.atom (a := .mul _ _ _) (by simp [sTopAddrs, mulS])
  have a4 : σ (sA1Of 2) = σ (.n 5557) + σ (.n 5559) := h.atom (a := .add _ _ _) (by simp [sTopAddrs, addS])
  have c5 : σ (sA0Of 2) = lit (2 ^ 25) :=
    h.atom (a := .const _ _) (by simp [sTopAddrs, cst, sA0Of])
  refine ⟨?_, ?_⟩
  · rw [c5, lit_eq _ (by norm_num), adrsCell0_eq192 (by norm_num) (by simp [layerTreeN])]
    simp [layerTreeN]
  · rw [a4, m1, m3, c0, c2, tm, l3,
      mul_lit_pow (by norm_num) (by norm_num; omega) lit56,
      mul_lit_pow (by norm_num) (by norm_num; omega) lit48,
      show 2 ^ 56 * (layerLeafN T 2 % 256) = 2 ^ 48 * (2 ^ 8 * (layerLeafN T 2 % 256)) by ring,
      eOfNat128_shift_add (k := 8) (by omega), adrsCell1_key_eq192 (by omega)]

end
end LeanVM.Guest.B1.Sig
