/-
  LeanVM.Guest.B1.Sig.SphincsSoundAddrs

  The hypertree's address cells in `verify_sig_lean_sphincs` (`lean_ethereum.py:4028-4029,
  4044-4045, 4048-4049` at leanVM main 40f877dc) are the statement's: each layer's `a0` is the first
  address cell of its tree, its `a1` the second cell of its one-time key, type `WOTS_HASH`.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsSoundDigest
public import LeanVM.Guest.B1.Sig.SphincsSoundPath
public import LeanVM.Guest.B1.Sig.SphincsHash
public import LeanVM.Guest.B1.Sig.SphincsT

/-!
# The hypertree's addresses, sound

The digest block gives the layers' leaves `L0`, `L1`, `L2` (`layerLeafN T l`), the byte `tree_mid
= L2 mod 2^8` and the shifts `lvals`. From them the guest computes (field addition is `XOR`, the
bits disjoint, so the cells are sums of their numbers):

* `sForsAddrs_sound` (`G:4028-4029`): `a0_b = adrsCell0 0 (L1 + 2^8 L2)`, `key_b = adrsCell1 0 L0 0 0`;
* `sMidAddrs_sound` (`G:4043-4044`): `a0_m = adrsCell0 1 L2`, `key_m = adrsCell1 0 L1 0 0`;
* `sTopAddrs_sound` (`G:4047-4048`): `a0_t = adrsCell0 2 0`, `key_t = adrsCell1 0 L2 0 0`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

/-! ## Products and sums of cells -/

/-- A value times `2^s` in the low limb. -/
theorem eOfNat_mul_lit_lo {a s : Nat} (h : 2 ^ s * a < 2 ^ 64) (hs : s < 64) :
    eOfNat a * lit (2 ^ s) = eOfNat192 (2 ^ s * a) := by
  rw [lit_of_lt (Nat.pow_lt_pow_right (by norm_num) hs), word_eq_eOfNat, mul_comm,
    eOfNat_two_pow_mul h, eOfNat192_of_lt h]

/-- A value times `2^(64 + s)`, in the high limb. -/
theorem eOfNat_mul_lit_hi {a s : Nat} (h : 2 ^ s * a < 2 ^ 64) (hs : s < 64) :
    eOfNat a * lit (2 ^ (64 + s)) = eOfNat192 (2 ^ (64 + s) * a) := by
  rw [pow_add, lit_hi (Nat.pow_lt_pow_right (by norm_num) hs), eOfNat_mul_word_hi' h,
    word_eq192 (by norm_num) h, Nat.zero_add, mul_assoc]

/-- Three shifted values with disjoint bits, a byte apart. -/
theorem e192_three {s a b c : Nat} (ha : a < 2 ^ 8) (hb : b < 2 ^ 8) :
    eOfNat192 (2 ^ (s + 16) * c) + eOfNat192 (2 ^ (s + 8) * b) + eOfNat192 (2 ^ s * a) =
      eOfNat192 (2 ^ s * (a + 2 ^ 8 * b + 2 ^ 16 * c)) := by
  rw [← eOfNat192_xor, ← eOfNat192_xor, pow_add, pow_add, mul_assoc, mul_assoc,
    pow_mul_xor_pow_mul, pow_mul_xor_pow_mul, show (2 : Nat) ^ 16 = 2 ^ 8 * 2 ^ 8 by norm_num,
    mul_assoc, pow_mul_xor_pow_mul, two_pow_mul_xor hb, two_pow_mul_xor ha]
  congr 2
  ring

/-- Two shifted values with disjoint bits, a byte apart. -/
theorem e192_two {s a b : Nat} (ha : a < 2 ^ 8) :
    eOfNat192 (2 ^ (s + 8) * b) + eOfNat192 (2 ^ s * a) = eOfNat192 (2 ^ s * (a + 2 ^ 8 * b)) := by
  rw [← eOfNat192_xor, pow_add, mul_assoc, pow_mul_xor_pow_mul, two_pow_mul_xor ha]
  congr 2
  ring

/-- A big-endian word's slot, digit by digit. -/
theorem beWordAt_digits (k : Nat) {a b c d : Nat} (ha : a < 256) (hb : b < 256) (hc : c < 256)
    (hd : d < 256) :
    beWordAt k (a + 256 * b + 65536 * c + 16777216 * d) =
      2 ^ (32 * k) * (d + 256 * c + 65536 * b + 16777216 * a) := by
  unfold beWordAt
  congr 1
  simp only [Nat.reducePow]
  omega

/-! ## The addresses -/

variable {rd : Reader} {σ : Val}

/-- The leaves' cells the addresses read. -/
theorem lval_cells {T : Nat} (hD : DigestAt σ T) :
    σ (sLVal 0) = eOfNat (layerLeafN T 0) ∧ σ (sLVal 8) = eOfNat (layerLeafN T 1) ∧
      σ (sLVal 24) = eOfNat (layerLeafN T 2 / 256) ∧ σ sTreeMid = eOfNat (layerLeafN T 2 % 256) := by
  have hl := hD.2.2.2.1
  refine ⟨by simpa [sLeafOff] using hl 0 (by norm_num) 0 (by simp [sLeafLen]),
    by simpa [sLeafOff] using hl 1 (by norm_num) 0 (by simp [sLeafLen]), ?_, ?_⟩
  · have := hl 2 (by norm_num) 8 (by simp [sLeafLen])
    simpa [sLeafOff, Nat.shiftRight_eq_div_pow] using this
  · rw [hD.2.2.2.2, ← layerLeaf2_low]
    rfl

/-- The leaves' bounds. -/
theorem leaves_lt (T : Nat) : layerLeafN T 0 < 256 ∧ layerLeafN T 1 < 256 ∧ layerLeafN T 2 < 1024 :=
  layerLeafN_lt' T

/-- **The bottom layer's addresses** (`G:4028-4029`). -/
theorem sForsAddrs_sound {T : Nat} (hD : DigestAt σ T) (h : AtomsHold rd σ sForsAddrs) :
    σ sA0B = adrsCell0 0 (layerTreeN T 0) ∧ σ sKeyB = adrsCell1 0 (layerLeafN T 0) 0 0 := by
  obtain ⟨v0, v8, v24, vm⟩ := lval_cells hD
  obtain ⟨b0, b1, b2⟩ := leaves_lt T
  have c0 : σ (.n 1372) = lit (2 ^ 120) := h.atom (a := .const (.n 1372) _) (by simp [sForsAddrs, cst])
  have m1 : σ (.n 1373) = σ (sLVal 8) * σ (.n 1372) := h.atom (a := .mul (.n 1373) _ _) (by simp [sForsAddrs, mulS])
  have c2 : σ (.n 1374) = lit (2 ^ 112) := h.atom (a := .const (.n 1374) _) (by simp [sForsAddrs, cst])
  have m3 : σ (.n 1375) = σ sTreeMid * σ (.n 1374) := h.atom (a := .mul (.n 1375) _ _) (by simp [sForsAddrs, mulS])
  have a4 : σ (.n 1376) = σ (.n 1373) + σ (.n 1375) := h.atom (a := .add (.n 1376) _ _) (by simp [sForsAddrs, addS])
  have c5 : σ (.n 1377) = lit (2 ^ 104) := h.atom (a := .const (.n 1377) _) (by simp [sForsAddrs, cst])
  have m6 : σ (.n 1378) = σ (sLVal 24) * σ (.n 1377) := h.atom (a := .mul (.n 1378) _ _) (by simp [sForsAddrs, mulS])
  have a7 : σ sA0B = σ (.n 1376) + σ (.n 1378) := h.atom (a := .add sA0B _ _) (by simp [sForsAddrs, addS])
  have c8 : σ (.n 1380) = lit (2 ^ 56) := h.atom (a := .const (.n 1380) _) (by simp [sForsAddrs, cst])
  have m9 : σ sKeyB = σ (sLVal 0) * σ (.n 1380) := h.atom (a := .mul sKeyB _ _) (by simp [sForsAddrs, mulS])
  obtain ⟨m, hm, q, hq, e2⟩ : ∃ m < 256, ∃ q < 4, layerLeafN T 2 = m + 256 * q :=
    ⟨layerLeafN T 2 % 256, by omega, layerLeafN T 2 / 256, by omega, by omega⟩
  have hm' : layerLeafN T 2 % 256 = m := by omega
  have hq' : layerLeafN T 2 / 256 = q := by omega
  have p1 : σ (.n 1373) = eOfNat192 (2 ^ (104 + 16) * layerLeafN T 1) := by
    rw [m1, v8, c0, show (2 : Nat) ^ 120 = 2 ^ (64 + 56) by norm_num,
      eOfNat_mul_lit_hi (by omega) (by norm_num)]
  have p3 : σ (.n 1375) = eOfNat192 (2 ^ (104 + 8) * m) := by
    rw [m3, vm, hm', c2, show (2 : Nat) ^ 112 = 2 ^ (64 + 48) by norm_num,
      eOfNat_mul_lit_hi (by omega) (by norm_num)]
  have p6 : σ (.n 1378) = eOfNat192 (2 ^ 104 * q) := by
    rw [m6, v24, hq', c5, show (2 : Nat) ^ 104 = 2 ^ (64 + 40) by norm_num,
      eOfNat_mul_lit_hi (by omega) (by norm_num)]
  have hN : beWordAt 0 0 + beWordAt 2 (layerTreeN T 0 / 2 ^ 32) + beWordAt 3 (layerTreeN T 0) =
      2 ^ 104 * (q + 2 ^ 8 * m + 2 ^ 16 * layerLeafN T 1) := by
    have et : layerTreeN T 0 = layerLeafN T 1 + 256 * m + 65536 * q + 16777216 * 0 := by
      simp only [layerTreeN, ite_true, e2]; ring
    rw [et, beWordAt_digits 3 b1 hm (by omega) (by norm_num),
      show (layerLeafN T 1 + 256 * m + 65536 * q + 16777216 * 0) / 2 ^ 32 = 0 by omega]
    simp only [beWordAt, Nat.zero_div, Nat.zero_mod]
    ring
  constructor
  · rw [a7, a4, p1, p3, p6, e192_three (by omega) (by omega), adrsCell0, hN,
      cellOf128_eq_eOfNat192 (by omega)]
  · rw [m9, c8, v0, eOfNat_mul_lit_lo (by omega) (by norm_num), adrsCell1_eq]
    congr 1
    rw [adrsNat1, show layerLeafN T 0 = layerLeafN T 0 + 256 * 0 + 65536 * 0 + 16777216 * 0 by ring,
      beWordAt_digits 1 b0 (by norm_num) (by norm_num) (by norm_num)]
    simp only [beWordAt, Nat.zero_div, Nat.zero_mod]
    ring

/-- A one-time key's second address cell, its leaf `L < 2^16` the key pair, type `WOTS_HASH`: the
leaf's two low bytes at bits `56` and `48`. -/
theorem keyCell_eq {m q : Nat} (hm : m < 256) (hq : q < 256) :
    eOfNat192 (2 ^ 48 * (q + 2 ^ 8 * m)) = adrsCell1 0 (m + 256 * q) 0 0 := by
  rw [adrsCell1_eq]
  congr 1
  rw [adrsNat1, show m + 256 * q = m + 256 * q + 65536 * 0 + 16777216 * 0 by ring,
    beWordAt_digits 1 hm hq (by norm_num) (by norm_num)]
  simp only [beWordAt, Nat.zero_div, Nat.zero_mod]
  ring

/-- **The middle layer's addresses** (`G:4043-4044`). -/
theorem sMidAddrs_sound {T : Nat} (hD : DigestAt σ T) (h : AtomsHold rd σ sMidAddrs) :
    σ (sA0Of 1) = adrsCell0 1 (layerTreeN T 1) ∧ σ (sA1Of 1) = adrsCell1 0 (layerLeafN T 1) 0 0 := by
  obtain ⟨-, v8, v24, vm⟩ := lval_cells hD
  obtain ⟨-, b1, b2⟩ := leaves_lt T
  have c0 : σ (.n 5398) = lit (2 ^ 24) := h.atom (a := .const (.n 5398) _) (by simp [sMidAddrs, cst])
  have c1 : σ (.n 5399) = lit (2 ^ 120) := h.atom (a := .const (.n 5399) _) (by simp [sMidAddrs, cst])
  have m2 : σ (.n 5400) = σ sTreeMid * σ (.n 5399) := h.atom (a := .mul (.n 5400) _ _) (by simp [sMidAddrs, mulS])
  have a3 : σ (.n 5401) = σ (.n 5398) + σ (.n 5400) := h.atom (a := .add (.n 5401) _ _) (by simp [sMidAddrs, addS])
  have c4 : σ (.n 5402) = lit (2 ^ 112) := h.atom (a := .const (.n 5402) _) (by simp [sMidAddrs, cst])
  have m5 : σ (.n 5403) = σ (sLVal 24) * σ (.n 5402) := h.atom (a := .mul (.n 5403) _ _) (by simp [sMidAddrs, mulS])
  have a6 : σ (sA0Of 1) = σ (.n 5401) + σ (.n 5403) := h.atom (a := .add (sA0Of 1) _ _) (by simp [sMidAddrs, addS])
  have c7 : σ (.n 5405) = lit (2 ^ 56) := h.atom (a := .const (.n 5405) _) (by simp [sMidAddrs, cst])
  have m8 : σ (sA1Of 1) = σ (sLVal 8) * σ (.n 5405) := h.atom (a := .mul (sA1Of 1) _ _) (by simp [sMidAddrs, mulS])
  obtain ⟨m, hm, q, hq, e2⟩ : ∃ m < 256, ∃ q < 4, layerLeafN T 2 = m + 256 * q :=
    ⟨layerLeafN T 2 % 256, by omega, layerLeafN T 2 / 256, by omega, by omega⟩
  have hm' : layerLeafN T 2 % 256 = m := by omega
  have hq' : layerLeafN T 2 / 256 = q := by omega
  have p2 : σ (.n 5400) = eOfNat192 (2 ^ (112 + 8) * m) := by
    rw [m2, vm, hm', c1, show (2 : Nat) ^ 120 = 2 ^ (64 + 56) by norm_num,
      eOfNat_mul_lit_hi (by omega) (by norm_num)]
  have p5 : σ (.n 5403) = eOfNat192 (2 ^ 112 * q) := by
    rw [m5, v24, hq', c4, show (2 : Nat) ^ 112 = 2 ^ (64 + 48) by norm_num,
      eOfNat_mul_lit_hi (by omega) (by norm_num)]
  have hN : beWordAt 0 1 + beWordAt 2 (layerTreeN T 1 / 2 ^ 32) + beWordAt 3 (layerTreeN T 1) =
      2 ^ 24 + 2 ^ 112 * (q + 2 ^ 8 * m) := by
    have et : layerTreeN T 1 = m + 256 * q + 65536 * 0 + 16777216 * 0 := by
      simp only [layerTreeN, e2]; simp
    rw [et, beWordAt_digits 3 hm (by omega) (by norm_num) (by norm_num),
      show (m + 256 * q + 65536 * 0 + 16777216 * 0) / 2 ^ 32 = 0 by omega]
    simp only [beWordAt, Nat.zero_div, Nat.zero_mod]
    ring
  constructor
  · rw [a6, a3, add_assoc, p2, p5, e192_two (by omega), c0, lit_eq _ (by norm_num),
      eOfNat192_add_shift (by norm_num), adrsCell0, hN, cellOf128_eq_eOfNat192 (by omega)]
  · rw [m8, c7, v8, eOfNat_mul_lit_lo (by omega) (by norm_num),
      show 2 ^ 56 * layerLeafN T 1 = 2 ^ 48 * (0 + 2 ^ 8 * layerLeafN T 1) by ring,
      keyCell_eq b1 (by norm_num)]
    simp

/-- **The top layer's addresses** (`G:4047-4048`). -/
theorem sTopAddrs_sound {T : Nat} (hD : DigestAt σ T) (h : AtomsHold rd σ sTopAddrs) :
    σ (sA0Of 2) = adrsCell0 2 (layerTreeN T 2) ∧ σ (sA1Of 2) = adrsCell1 0 (layerLeafN T 2) 0 0 := by
  obtain ⟨-, -, v24, vm⟩ := lval_cells hD
  obtain ⟨-, -, b2⟩ := leaves_lt T
  have c0 : σ (.n 5556) = lit (2 ^ 56) := h.atom (a := .const (.n 5556) _) (by simp [sTopAddrs, cst])
  have m1 : σ (.n 5557) = σ sTreeMid * σ (.n 5556) := h.atom (a := .mul (.n 5557) _ _) (by simp [sTopAddrs, mulS])
  have c2 : σ (.n 5558) = lit (2 ^ 48) := h.atom (a := .const (.n 5558) _) (by simp [sTopAddrs, cst])
  have m3 : σ (.n 5559) = σ (sLVal 24) * σ (.n 5558) := h.atom (a := .mul (.n 5559) _ _) (by simp [sTopAddrs, mulS])
  have a4 : σ (sA1Of 2) = σ (.n 5557) + σ (.n 5559) := h.atom (a := .add (sA1Of 2) _ _) (by simp [sTopAddrs, addS])
  have c5 : σ (sA0Of 2) = lit (2 ^ 25) := h.atom (a := .const (sA0Of 2) _) (by simp [sTopAddrs, cst, sA0Of])
  obtain ⟨m, hm, q, hq, e2⟩ : ∃ m < 256, ∃ q < 4, layerLeafN T 2 = m + 256 * q :=
    ⟨layerLeafN T 2 % 256, by omega, layerLeafN T 2 / 256, by omega, by omega⟩
  have hm' : layerLeafN T 2 % 256 = m := by omega
  have hq' : layerLeafN T 2 / 256 = q := by omega
  have p1 : σ (.n 5557) = eOfNat192 (2 ^ (48 + 8) * m) := by
    rw [m1, vm, hm', c0, eOfNat_mul_lit_lo (by omega) (by norm_num)]
  have p3 : σ (.n 5559) = eOfNat192 (2 ^ 48 * q) := by
    rw [m3, v24, hq', c2, eOfNat_mul_lit_lo (by omega) (by norm_num)]
  constructor
  · rw [c5, lit_eq _ (by norm_num), adrsCell0, cellOf128_eq_eOfNat192 (by
      simp only [layerTreeN, beWordAt]; norm_num)]
    congr 1
    simp only [layerTreeN, beWordAt]
    norm_num
  · rw [a4, p1, p3, e192_two (by omega), keyCell_eq hm (by omega), e2]

end
end LeanVM.Guest.B1.Sig
