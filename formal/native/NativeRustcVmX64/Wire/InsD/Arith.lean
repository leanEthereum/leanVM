module

public import NativeRustcVmX64.Wire.InsD.Basic

/-!
# The arithmetic of `ins_d`'s indices (x86-64)

What the blocks compute of the scan's and the shift's indices, all below `256`: `min n 255`
(`b7`), the remainder's count `(n - i) % 4` (`b8`), the steps down (`b10`, `b13`), the test of
four or more to move (`b11`).
-/

namespace NativeRustcVmX64.Wire.InsD

open NativeRustcX64 NativeRustcX64.Sym

public section

theorem toNat_addLit (x : BitVec 64) (c : Nat) :
    (BinOp.apply .add .W64 x (BitVec.ofNat 64 c)).toNat = (x.toNat + c) % 2 ^ 64 := by
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem toNat_litAdd (x : BitVec 64) (c : Nat) :
    (BinOp.apply .add .W64 (BitVec.ofNat 64 c) x).toNat = (c + x.toNat) % 2 ^ 64 := by
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem toNat_subLit (x : BitVec 64) (c : Nat) (h : c ≤ x.toNat) :
    (BinOp.apply .sub .W64 x (BitVec.ofNat 64 c)).toNat = x.toNat - c := by
  have := x.isLt
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- `x - k` for `k ≤ x < 256`, in 64 bits. -/
theorem dec64 {x : BitVec 64} {k : Nat} (hk : k ≤ x.toNat) (hk' : k ≤ 2 ^ 64) :
    (BinOp.apply .add .W64 x (BitVec.ofNat 64 (2 ^ 64 - k))).toNat = x.toNat - k := by
  rw [toNat_addLit]
  have := x.isLt
  omega

/-- `x - k` in 64 bits, the literal first. -/
theorem dec64' {x : BitVec 64} {k : Nat} (hk : k ≤ x.toNat) (hk' : k ≤ 2 ^ 64) :
    (BinOp.apply .add .W64 (BitVec.ofNat 64 (2 ^ 64 - k)) x).toNat = x.toNat - k := by
  rw [toNat_litAdd]
  have := x.isLt
  omega

/-- `leal -k(%rsi)`: `x - k` for `k ≤ x < 2 ^ 32`. -/
theorem dec32 {x : BitVec 64} {k : Nat} (hk : k ≤ x.toNat) (hx : x.toNat < 2 ^ 32) (hk' : k ≤ 2 ^ 64) :
    (UnOp.apply .trunc .W32 (BinOp.apply .add .W64 x (BitVec.ofNat 64 (2 ^ 64 - k)))).toNat =
      x.toNat - k := by
  have h := dec64 hk hk'
  simp only [UnOp.apply, ext, low, BitVec.toNat_setWidth, Width.bits, h]
  omega

/-- `cmpq $255, %rax; cmovbq`: `min n 255`, `n` itself for `n < 256`. -/
theorem min255 {x : BitVec 64} (hx : x.toNat < 256) :
    (if CmpOp.apply .ult .W64 x (BitVec.ofNat 64 255) = true then x else BitVec.ofNat 64 255) =
      x := by
  simp only [CmpOp.apply, low_W64, BitVec.ult, BitVec.toNat_ofNat]
  split
  · rfl
  · apply BitVec.eq_of_toNat_eq
    rename_i h
    simp only [decide_eq_true_eq] at h
    rw [BitVec.toNat_ofNat]
    simp only [Width.bits] at h ⊢
    omega

/-- `(r8d - ecx) & 3`: the remainder's count. -/
theorem rem4 {n i : BitVec 64} (hn : n.toNat < 256) (hi : i.toNat < n.toNat) :
    (BinOp.apply .and .W32 (BinOp.apply .sub .W32 (UnOp.apply .trunc .W32 n) i)
      (BitVec.ofNat 64 3)).toNat = (n.toNat - i.toNat) % 4 := by
  simp only [BinOp.apply, UnOp.apply, ext, low, BitVec.toNat_setWidth, BitVec.toNat_and,
    BitVec.toNat_sub, BitVec.toNat_ofNat, Width.bits]
  rw [show (3 : Nat) % 2 ^ 64 % 2 ^ 32 = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- `cmpq $-4` after `rcx - r8`: more than three to move. -/
theorem ge4 {n i : BitVec 64} (hn : n.toNat < 256) (hi : i.toNat < n.toNat) :
    (!CmpOp.apply .ult .W64 (BinOp.apply .sub .W64 i n) (BitVec.ofNat 64 (2 ^ 64 - 4)) &&
      !CmpOp.apply .eq .W64 (BinOp.apply .sub .W64 i n) (BitVec.ofNat 64 (2 ^ 64 - 4))) =
      decide (n.toNat - i.toNat < 4) := by
  have hs : (BinOp.apply .sub .W64 i n).toNat = 2 ^ 64 - (n.toNat - i.toNat) := by
    simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_sub]
    omega
  simp only [CmpOp.apply, low_W64, BitVec.ult]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_eq_false_iff_ne,
    decide_eq_true_eq, ne_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have h2' : (BinOp.apply .sub .W64 i n).toNat ≠ 2 ^ 64 - 4 := fun h ↦ h2 (BitVec.eq_of_toNat_eq
      (by rw [h]; rfl))
    rw [BitVec.toNat_ofNat] at h1
    simp only [Width.bits] at h1
    omega
  · intro h
    refine ⟨by rw [BitVec.toNat_ofNat]; simp only [Width.bits]; omega, fun h' ↦ ?_⟩
    have := congrArg BitVec.toNat h'
    rw [hs, BitVec.toNat_ofNat] at this
    omega

end

end NativeRustcVmX64.Wire.InsD
