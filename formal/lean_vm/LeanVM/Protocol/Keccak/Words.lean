/-
  LeanVM.Protocol.Keccak.Words

  A `K` word as the sum of its bits times the powers `x^z`: the reading of the first claim's
  weights `x^z` (`crates/verifier/src/keccak.rs:251`) and of the committed words' bit slices.
-/

module

public import LeanVM.Protocol.Keccak.Linear
public import LeanVM.Parameters.Field

/-!
# Words and their bits

`K = GF(2^64)` is CompPoly's `BF64`, a `BitVec 64` whose bit `z` is the coefficient of `x^z`,
and its addition is XOR. Hence a word is the sum of its bits times the powers of `x`, the powers
being the words `K.ofBits (2^z)` (`word_eq_sum`); lifted to `E`, the verifier's `E(1 << z)`
(`eOfNat (2^z)`) are those powers (`ofK_ofLane`).
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Verifier Finset

@[expose] public section

theorem toBitVec_add (a b : K) : (a + b).toBitVec = a.toBitVec ^^^ b.toBitVec := rfl

theorem toBitVec_sum_getLsbD (bv : BitVec 64) :
    ∀ n, n ≤ 64 → ∀ i < 64,
      (∑ z ∈ range n, (if bv.getLsbD z then K.ofBits (2 ^ z) else 0)).toBitVec.getLsbD i =
        (decide (i < n) && bv.getLsbD i)
  | 0, _, i, _ => by simp
  | n + 1, hn, i, hi => by
    rw [Finset.sum_range_succ, toBitVec_add, BitVec.getLsbD_xor,
      toBitVec_sum_getLsbD bv n (by omega) i hi]
    have hpow : (K.ofBits (2 ^ n)).toBitVec.getLsbD i = decide (n = i) := by
      rw [K.ofBits, BF64.toBitVec_ofBitVec, BitVec.getLsbD_ofNat, Nat.testBit_two_pow]
      simp [hi]
    by_cases hb : bv.getLsbD n
    · rw [ite_eq_left hb, hpow]
      by_cases hin : n = i
      · subst hin; simp [hb]
      · have : (i < n + 1) = (i < n) := by apply propext; omega
        simp [hin, this]
    · rw [ite_eq_right hb]
      by_cases hin : n = i
      · subst hin; simp [hb]
      · have : (i < n + 1) = (i < n) := by apply propext; omega
        simp [this]

/-- **A word is the sum of its bits times the powers of `x`.** -/
theorem word_eq_sum (bv : BitVec 64) :
    BF64.ofBitVec bv = ∑ z ∈ range 64, (if bv.getLsbD z then K.ofBits (2 ^ z) else 0) := by
  refine BF64.ext (BitVec.eq_of_getLsbD_eq fun i hi ↦ ?_)
  rw [toBitVec_sum_getLsbD bv 64 le_rfl i hi]
  simp [hi]

/-- A 64-bit lane in `E`: its bits times `K(1 << z)` (`keccak.rs:251`). -/
theorem ofK_ofLane (w : UInt64) :
    ofK (K.ofLane w) = ∑ z ∈ range 64, bitE (w.toBitVec.getLsbD z) * eOfNat (2 ^ z) := by
  rw [K.ofLane, word_eq_sum, show ofK = algebraMap K E from rfl, map_sum]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  cases w.toBitVec.getLsbD z <;> simp [eOfNat, bitE]

theorem eOfNat_one : eOfNat 1 = 1 := by
  rw [eOfNat, show K.ofBits 1 = 1 from rfl, show ofK = algebraMap K E from rfl, map_one]

theorem ofLane_lane (a : K) : K.ofLane (K.lane a) = a := rfl

end
end LeanVM.Protocol.KeccakGkr
