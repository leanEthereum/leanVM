module

public import NativeVm.Transcript.Layout

/-!
# Word addresses and layout bounds
-/

@[expose] public section

namespace NativeVm.Transcript

open Native.Keccak

theorem toNat_toUInt64 {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  omega

theorem toUInt64_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    a.toUInt64 = b.toUInt64 ↔ a = b := by
  rw [← UInt64.toNat_inj, toNat_toUInt64 ha, toNat_toUInt64 hb]

theorem toUInt64_lt {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    a.toUInt64 < b.toUInt64 ↔ a < b := by
  rw [UInt64.lt_iff_toNat_lt, toNat_toUInt64 ha, toNat_toUInt64 hb]

theorem toUInt64_le {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    a.toUInt64 ≤ b.toUInt64 ↔ a ≤ b := by
  rw [UInt64.le_iff_toNat_le, toNat_toUInt64 ha, toNat_toUInt64 hb]

theorem toUInt64_succ (n : Nat) : n.toUInt64 + 1 = (n + 1).toUInt64 := by
  simp [Nat.toUInt64_eq, UInt64.ofNat_add]

theorem toUInt64_add (a b : Nat) : a.toUInt64 + b.toUInt64 = (a + b).toUInt64 := by
  simp [Nat.toUInt64_eq, UInt64.ofNat_add]

theorem toUInt64_shl (c n : Nat) (hn : n < 64) :
    c.toUInt64 <<< n.toUInt64 = (2 ^ n * c).toUInt64 := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_shiftLeft, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show n % 2 ^ 64 < 64 by omega), Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]
  rw [Nat.mul_comm (2 ^ n), Nat.mod_mul_mod]

theorem wd_add (b : UInt64) (k j : Nat) : wd b k + (8 * j).toUInt64 = wd b (k + j) := by
  simp only [wd, Nat.toUInt64_eq, Nat.mul_add, UInt64.ofNat_add, UInt64.add_assoc]

theorem wd_zero (b : UInt64) : wd b 0 = b := by simp [wd]

theorem wd_inj {b : UInt64} {k k' : Nat} (hk : k < 2 ^ 61) (hk' : k' < 2 ^ 61) :
    wd b k = wd b k' ↔ k = k' := by
  unfold wd
  rw [UInt64.add_right_inj, toUInt64_inj (by omega) (by omega)]
  omega

theorem wd_toNat {b : UInt64} {n k : Nat} (h : Fits b n) (hk : k < n) :
    (wd b k).toNat = b.toNat + 8 * k := by
  unfold Fits at h
  unfold wd
  rw [UInt64.toNat_add, toNat_toUInt64 (by omega)]
  omega

/-- Words of disjoint areas differ. -/
theorem wd_ne_of_disj {b c : UInt64} {n m i j : Nat} (hb : Fits b n) (hc : Fits c m)
    (hd : Disj b n c m) (hi : i < n) (hj : j < m) : wd b i ≠ wd c j := fun e ↦ by
  have := congrArg UInt64.toNat e
  rw [wd_toNat hb hi, wd_toNat hc hj] at this
  unfold Disj at hd
  omega

theorem Disj.symm {b c : UInt64} {n m : Nat} (h : Disj b n c m) : Disj c m b n := Or.symm h

theorem scratchW_val : scratchW = 32 := (rfl)
theorem laneW_val : laneW = 116 := (rfl)
theorem rateW_val : rateW = 141 := (rfl)
theorem countW_val : countW = 157 := (rfl)
theorem groundW_val : groundW = 158 := (rfl)
theorem climbW_val : climbW = 161 := (rfl)
theorem qRootW_val : qRootW = 169 := (rfl)
theorem ctxEnd_val : ctxEnd = 175 := (rfl)
theorem scratchWords_val : scratchWords = 84 := (rfl)
theorem workWords_val : workWords = 69 := (rfl)
theorem workRoots_val : workRoots = 5 := (rfl)
theorem rootStride_val : rootStride = 8 := (rfl)
theorem maxRoots_val : maxRoots = 8 := (rfl)

end NativeVm.Transcript
