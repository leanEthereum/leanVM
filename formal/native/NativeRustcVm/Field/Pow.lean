module

public import NativeRustcVm.Field.Clmul
import NativeVm.Equiv.Field

/-!
# Powers in `K`

Through `BF64.ofBitVec` (the model's `K.ofLane`): `kmul` is the product (`ofBitVec_kmul`),
`kpowLoop base acc n` is `acc · base^n` (`ofBitVec_kpowLoop`), `sq v n` is `v^(2^n)`
(`ofBitVec_sq`), and the Itoh-Tsujii chain of `kinv` is `a^(2^64 - 2)` (`ofBitVec_kinv`), each the
model's power (`kpow_eq`, `kinv_eq`).
-/

namespace NativeRustcVm.Field

public section

theorem ofBitVec_kmul (x y : BitVec 64) :
    BF64.ofBitVec (kmul x y) = BF64.ofBitVec x * BF64.ofBitVec y := by
  rw [kmul_eq_mul]
  rfl

theorem and_one_eq_one_iff (n : BitVec 64) : n &&& 1#64 = 1#64 ↔ n.toNat % 2 = 1 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_and]
  simp [Nat.and_one_is_mod]

/-- **`kpow`'s loop** is `acc · base^n`. -/
theorem ofBitVec_kpowLoop : ∀ (m : ℕ) (base acc n : BitVec 64), n.toNat = m →
    BF64.ofBitVec (kpowLoop base acc n) = BF64.ofBitVec acc * BF64.ofBitVec base ^ m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro base acc n hn
    rw [kpowLoop]
    split
    · next h =>
      subst h
      rw [← hn]
      simp
    · next h =>
      have h0 : m ≠ 0 := fun h0 ↦ h (BitVec.eq_of_toNat_eq (by simp [hn, h0]))
      have hs : (n >>> 1).toNat = m / 2 := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hn, Nat.pow_one]
      rw [ih (m / 2) (by omega) _ _ _ hs, ofBitVec_kmul]
      by_cases hb : m % 2 = 1
      · rw [ite_eq_left ((and_one_eq_one_iff n).2 (by omega)), ofBitVec_kmul]
        conv_rhs => rw [show m = 2 * (m / 2) + 1 by omega]
        rw [pow_succ, pow_mul, pow_two]
        ring
      · rw [ite_eq_right fun h' ↦ hb (by have := (and_one_eq_one_iff n).1 h'; omega)]
        conv_rhs => rw [show m = 2 * (m / 2) by omega]
        rw [pow_mul, pow_two]

/-- **`kpow` is the model's.** -/
theorem kpow_eq (a n : BitVec 64) :
    kpow a n = (NativeVm.Model.kpow (.ofBitVec a) n.toNat).toBitVec := by
  have h := ofBitVec_kpowLoop n.toNat a 1#64 n rfl
  have hm := NativeVm.Equiv.K_ofLane_kpow (.ofBitVec a) n.toNat
  show (BF64.ofBitVec (kpow a n)).toBitVec = _
  rw [kpow, h, show BF64.ofBitVec 1#64 = 1 from rfl, one_mul]
  exact congrArg BF64.toBitVec hm.symm

/-- `n` squarings. -/
theorem ofBitVec_sq : ∀ (v : BitVec 64) (n : ℕ), BF64.ofBitVec (sq v n) = BF64.ofBitVec v ^ 2 ^ n
  | v, 0 => by rw [sq, pow_zero, pow_one]
  | v, n + 1 => by
    rw [sq, ofBitVec_sq _ n, ksquare, ofBitVec_kmul, ← pow_two, ← pow_mul, ← pow_succ']

/-- A link of the chain: `y^(2^k) · z`. -/
theorem ofBitVec_link {x : BF64} {y z : BitVec 64} {p q : ℕ} (k : ℕ) (hy : BF64.ofBitVec y = x ^ p)
    (hz : BF64.ofBitVec z = x ^ q) : BF64.ofBitVec (kmul (sq y k) z) = x ^ (p * 2 ^ k + q) := by
  rw [ofBitVec_kmul, ofBitVec_sq, hy, hz, ← pow_mul, ← pow_add]

/-- **The Itoh-Tsujii chain** is the power `2^64 - 2`. -/
theorem ofBitVec_kinv (a : BitVec 64) : BF64.ofBitVec (kinv a) = BF64.ofBitVec a ^ (2 ^ 64 - 2) := by
  have t1 : BF64.ofBitVec a = BF64.ofBitVec a ^ 1 := (pow_one _).symm
  have t2 := ofBitVec_link 1 t1 t1
  have t3 := ofBitVec_link 1 t2 t1
  have t6 := ofBitVec_link 3 t3 t3
  have t12 := ofBitVec_link 6 t6 t6
  have t24 := ofBitVec_link 12 t12 t12
  have t48 := ofBitVec_link 24 t24 t24
  have t60 := ofBitVec_link 12 t48 t12
  have t63 := ofBitVec_link 3 t60 t3
  simp only [kinv]
  rw [ofBitVec_sq, t63, ← pow_mul]
  norm_num

/-- **`kinv` is the model's.** -/
theorem kinv_eq (a : BitVec 64) : kinv a = (NativeVm.Model.kinv (.ofBitVec a)).toBitVec := by
  have hm := NativeVm.Equiv.K_ofLane_kpow (.ofBitVec a) (2 ^ 64 - 2)
  show (BF64.ofBitVec (kinv a)).toBitVec = _
  rw [ofBitVec_kinv]
  exact congrArg BF64.toBitVec hm.symm

end

end NativeRustcVm.Field
