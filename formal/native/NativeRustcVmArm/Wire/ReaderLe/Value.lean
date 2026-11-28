module

public import NativeRustcVmArm.Wire.Common
public import NativeVm.Wire.Model
import NativeVm.Wire.Read

/-!
# `Reader::le`'s word and branch

The word `Reader::le` assembles from the bytes it loads, highest first, is `leNat` of them
(`quad_toNat`, `horner_toNat`, `leNat_cons`); its first branch is taken exactly when the read
fits (`fits_eval`).
-/

namespace NativeRustcVmArm.Wire.ReaderLe

open NativeRustcArm NativeRustcArm.Sym NativeVm.Wire

public section

/-- `leNat` by Horner's rule, from the lowest byte. -/
theorem leNat_cons (B : List UInt8) (p n : Nat) :
    leNat B p (n + 1) = (B.getD p 0).toNat + 256 * leNat B (p + 1) n := by
  unfold leNat
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [Nat.add_zero, pow_zero, mul_one]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun k _ ↦ by
    rw [show p + (k + 1) = p + 1 + k by omega, pow_succ]
    ring

theorem leNat_zero (B : List UInt8) (p : Nat) : leNat B p 0 = 0 := by
  simp [leNat]

/-- One step of the assembly: a byte below the word shifted by 8. -/
theorem horner_toNat {y v : BitVec 64} (hy : y.toNat < 256) (hv : v.toNat < 2 ^ 56) :
    (y ||| v <<< 8).toNat = y.toNat + 256 * v.toNat := by
  have hs : (v <<< 8).toNat = v.toNat * 2 ^ 8 := toNat_shl (by omega)
  rw [toNat_or_add (k := 8) (by omega) (by rw [hs]; exact Nat.dvd_mul_left _ _), hs]
  omega

/-- The first three bytes the assembly ors: `(y2 << 8 | y3 << 16) | y1`. -/
theorem quad_toNat {y1 y2 y3 : BitVec 64} (h1 : y1.toNat < 256) (h2 : y2.toNat < 256)
    (h3 : y3.toNat < 256) :
    ((y2 <<< 8 ||| y3 <<< 16) ||| y1).toNat = y1.toNat + 256 * (y2.toNat + 256 * y3.toNat) := by
  have hs2 : (y2 <<< 8).toNat = y2.toNat * 2 ^ 8 := toNat_shl (by omega)
  have hs3 : (y3 <<< 16).toNat = y3.toNat * 2 ^ 16 := toNat_shl (by omega)
  have hi : (y2 <<< 8 ||| y3 <<< 16).toNat = y2.toNat * 2 ^ 8 + y3.toNat * 2 ^ 16 := by
    rw [toNat_or_add (k := 16) (by rw [hs2]; omega)
      (by rw [hs3]; exact Nat.dvd_mul_left _ _), hs2, hs3]
  rw [BitVec.or_comm, toNat_or_add (k := 8) h1 (by
    rw [hi]
    exact Nat.dvd_add (Nat.dvd_mul_left _ _)
      ⟨y3.toNat * 2 ^ 8, by rw [show (2 : Nat) ^ 16 = 2 ^ 8 * 2 ^ 8 from rfl]; ring⟩), hi]
  omega

/-- The four bytes from `o` as the assembly ors them: `y0 | ((y2 << 8 | y3 << 16) | y1) << 8`. -/
@[expose] def quadSym (o : Nat) : Sym :=
  .bin .orr .W64 (.load 1 o 1) (.un (.shift .LSL 8) .W64
    (.bin .orr .W64 (.bin .orr .W64 (.un (.ubfm 56 55) .W64 (.load 1 (o + 2) 1))
      (.un (.shift .LSL 16) .W64 (.load 1 (o + 3) 1))) (.load 1 (o + 1) 1)))

/-- The `j + 4` bytes from `o`, the last four by `quadSym`, each lower one ored below. -/
@[expose] def hornerSym : Nat → Nat → Sym
  | o, 0 => quadSym o
  | o, j + 1 => .bin .orr .W64 (.load 1 o 1) (.un (.shift .LSL 8) .W64 (hornerSym (o + 1) j))

theorem eval_quad [Labels] (env : Env) (B : List UInt8) (c o : Nat)
    (hy : ∀ i < 4, (env.load 1 (o + i) 1).toNat = (B.getD (c + o + i) 0).toNat) :
    ((quadSym o).eval env).toNat = leNat B (c + o) 4 := by
  have hb : ∀ i < 4, (env.load 1 (o + i) 1).toNat < 256 := fun i hi ↦ by
    rw [hy i hi]; exact (B.getD _ 0).toNat_lt
  have h0 := hy 0 (by omega); have h1 := hy 1 (by omega)
  have h2 := hy 2 (by omega); have h3 := hy 3 (by omega)
  have b0 := hb 0 (by omega); have b1 := hb 1 (by omega)
  have b2 := hb 2 (by omega); have b3 := hb 3 (by omega)
  simp only [Nat.add_zero] at h0 b0
  simp only [quadSym, Sym.eval, ubfm_lsl8]
  sym_simp
  rw [horner_toNat b0 (by rw [quad_toNat b1 b2 b3]; omega), quad_toNat b1 b2 b3, h0, h1, h2, h3,
    leNat_cons, leNat_cons, leNat_cons, leNat_cons, leNat_zero]
  simp only [Nat.add_assoc, Nat.mul_zero, Nat.add_zero]

theorem eval_horner [Labels] (env : Env) (B : List UInt8) (c : Nat) :
    ∀ (j o : Nat), j ≤ 4 →
      (∀ i < j + 4, (env.load 1 (o + i) 1).toNat = (B.getD (c + o + i) 0).toNat) →
      ((hornerSym o j).eval env).toNat = leNat B (c + o) (j + 4)
  | 0, o, _, hy => eval_quad env B c o hy
  | j + 1, o, hj, hy => by
    have ih := eval_horner env B c j (o + 1) (by omega) fun i hi ↦ by
      rw [show o + 1 + i = o + (i + 1) by omega, hy (i + 1) (by omega)]
      congr 2
      omega
    have h0 := hy 0 (by omega)
    simp only [Nat.add_zero] at h0
    have hlt := leNat_lt B (c + (o + 1)) (j + 4)
    have hp : 256 ^ (j + 4) ≤ 2 ^ 56 :=
      (Nat.pow_le_pow_right (by omega) (show j + 4 ≤ 7 by omega)).trans (by norm_num)
    simp only [hornerSym, Sym.eval]
    sym_simp
    rw [horner_toNat (by rw [h0]; exact (B.getD _ 0).toNat_lt) (by rw [ih]; omega), ih, h0,
      show j + 1 + 4 = (j + 4) + 1 by omega, leNat_cons B (c + o) (j + 4),
      show c + o + 1 = c + (o + 1) by omega]

end

end NativeRustcVmArm.Wire.ReaderLe
