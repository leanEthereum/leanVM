import Rv64Verifier.Model.Ext
import Statement.LeanVmVerifier

/-!
# The field algorithms of `field.rs`

Mirrors of `crates/verifier/src/field.rs` over `BitVec 64` limbs, each shaped like the Rust (the
same loops, in the same order, through the same intermediate values), and each proved equal to
the specification's operation: `K::square` (`kSquare_eq`), `E::square` (`esquare_eq`), `K::inv`
(`kInv_eq`), `E::pow` (`epow_eq`), `powers` (`powersM_eq`), `Scaled::new` and `Scaled::mul`
(`scaledMul_eq`), and `E::inv` (`einv_eq`). An `E` product inside a mirror is `emul`, the Rust's
Karatsuba of `Model.Ext`.
-/

namespace Rv64Verifier.Model

open CompPoly.Extension LeanVM.Parameters BinaryField

/-! ## Limbs -/

/-- An `E` as the Rust holds it: `c0`, `c1`, `c2`. -/
abbrev Limbs : Type := BitVec 64 × BitVec 64 × BitVec 64

/-- `E * E` on limbs. -/
def lmul (a b : Limbs) : Limbs := emul a.1 a.2.1 a.2.2 b.1 b.2.1 b.2.2

/-- `E + E` on limbs. -/
def ladd (a b : Limbs) : Limbs := (a.1 ^^^ b.1, a.2.1 ^^^ b.2.1, a.2.2 ^^^ b.2.2)

/-- `ZERO`. -/
def lzero : Limbs := (0#64, 0#64, 0#64)

/-- `ONE`. -/
def lone : Limbs := (1#64, 0#64, 0#64)

theorem lmul_eq (x y : E) : lmul (limbs x) (limbs y) = limbs (x * y) := emul_eq x y

theorem ladd_eq (x y : E) : ladd (limbs x) (limbs y) = limbs (x + y) := rfl

theorem limbs_zero : limbs (0 : E) = lzero := rfl

theorem limbs_one : limbs (1 : E) = lone := rfl

theorem limbs_ofK (a : K) : limbs (ofK a) = (a.toBitVec, 0#64, 0#64) := rfl

theorem limbs_gen : limbs (Ext.gen : E) = (0#64, 1#64, 0#64) := rfl

theorem limbs_inj {x y : E} (h : limbs x = limbs y) : x = y := by
  simp only [limbs, Prod.mk.injEq] at h
  obtain ⟨h0, h1, h2⟩ := h
  apply Ext.ext
  rintro ⟨i, hi⟩
  have hd : BF64.ext3Params.d = 3 := rfl
  have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases this with rfl | rfl | rfl
  · rw [← Ext.coeffNat_of_lt _ (by omega), ← Ext.coeffNat_of_lt _ (by omega)]
    exact BF64.toBitVec_injective h0
  · rw [← Ext.coeffNat_of_lt _ (by omega), ← Ext.coeffNat_of_lt _ (by omega)]
    exact BF64.toBitVec_injective h1
  · rw [← Ext.coeffNat_of_lt _ (by omega), ← Ext.coeffNat_of_lt _ (by omega)]
    exact BF64.toBitVec_injective h2

/-! ## `spread` and `reduce` -/

/-- `spread`: the bits of `a` to the even positions of a 128-bit word. -/
def spread (a : BitVec 64) : BitVec 128 :=
  let x := a.setWidth 128
  let x := (x ||| x <<< 32) &&& 0x00000000FFFFFFFF00000000FFFFFFFF#128
  let x := (x ||| x <<< 16) &&& 0x0000FFFF0000FFFF0000FFFF0000FFFF#128
  let x := (x ||| x <<< 8) &&& 0x00FF00FF00FF00FF00FF00FF00FF00FF#128
  let x := (x ||| x <<< 4) &&& 0x0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F#128
  let x := (x ||| x <<< 2) &&& 0x33333333333333333333333333333333#128
  (x ||| x <<< 1) &&& 0x55555555555555555555555555555555#128

/-- `reduce`: the 128-bit word's high and low words to `reduceWords`. -/
def reduce128 (p : BitVec 128) : BitVec 64 := reduceWords (p.extractLsb' 64 64) (p.extractLsb' 0 64)

theorem reduce128_eq (p : BitVec 128) : reduce128 p = BF64.reduce p := by
  rw [reduce128, reduceWords_eq, ← split128]

/-- After the step of shift `s`, bit `k` (with `k % 2s < s`) holds bit `(k / 2s) s + k % 2s` of
`a`, and the other bits are clear. -/
def Spread (a : BitVec 64) (s : ℕ) (x : BitVec 128) : Prop :=
  ∀ k, x.getLsbD k =
    (decide (k < 128) && decide (k % (2 * s) < s) && a.getLsbD (k / (2 * s) * s + k % (2 * s)))

theorem spread_start (a : BitVec 64) : Spread a 64 (a.setWidth 128) := by
  intro k
  rw [BitVec.getLsbD_setWidth]
  by_cases hk : k < 128
  · rw [show k % (2 * 64) = k by omega, show k / (2 * 64) = 0 by omega]
    by_cases h : k < 64
    · simp [hk, h]
    · simp [hk, h, BitVec.getLsbD_of_ge a k (by omega)]
  · simp [hk, BitVec.getLsbD_of_ge a k (by omega)]

theorem spread_step (a : BitVec 64) (s : ℕ) (x m : BitVec 128)
    (hs : s = 32 ∨ s = 16 ∨ s = 8 ∨ s = 4 ∨ s = 2 ∨ s = 1)
    (hm : ∀ k : Fin 128, m.getLsbD k = decide (k.val % (2 * s) < s)) (hx : Spread a (2 * s) x) :
    Spread a s ((x ||| x <<< s) &&& m) := by
  intro k
  by_cases hk : k < 128
  · have hmk := hm ⟨k, hk⟩
    simp only at hmk
    rw [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hx, hx, hmk]
    by_cases h1 : k % (2 * s) < s <;> by_cases h2 : k % (2 * (2 * s)) < 2 * s <;>
      by_cases h3 : k < s <;> simp [h1, h2, h3, hk]
    · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> (congr 1; omega)
    · have h4 : ¬ (k - s) % (2 * (2 * s)) < 2 * s := by
        rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      simp only [h4, decide_false, Bool.and_false, Bool.false_and, Bool.or_false]
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> (congr 1; omega)
    · exfalso; rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · have h4 : (k - s) % (2 * (2 * s)) < 2 * s := by
        rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      simp only [h4, decide_true, show k - s < 128 by omega, Bool.true_and]
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> (congr 1; omega)
  · rw [BitVec.getLsbD_of_ge _ k (by omega)]; simp [hk]

theorem mask32 : ∀ k : Fin 128, (0x00000000FFFFFFFF00000000FFFFFFFF#128).getLsbD k =
    decide (k.val % (2 * 32) < 32) := by decide +kernel

theorem mask16 : ∀ k : Fin 128, (0x0000FFFF0000FFFF0000FFFF0000FFFF#128).getLsbD k =
    decide (k.val % (2 * 16) < 16) := by decide +kernel

theorem mask8 : ∀ k : Fin 128, (0x00FF00FF00FF00FF00FF00FF00FF00FF#128).getLsbD k =
    decide (k.val % (2 * 8) < 8) := by decide +kernel

theorem mask4 : ∀ k : Fin 128, (0x0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F#128).getLsbD k =
    decide (k.val % (2 * 4) < 4) := by decide +kernel

theorem mask2 : ∀ k : Fin 128, (0x33333333333333333333333333333333#128).getLsbD k =
    decide (k.val % (2 * 2) < 2) := by decide +kernel

theorem mask1 : ∀ k : Fin 128, (0x55555555555555555555555555555555#128).getLsbD k =
    decide (k.val % (2 * 1) < 1) := by decide +kernel

theorem spread_spread (a : BitVec 64) : Spread a 1 (spread a) :=
  spread_step a 1 _ _ (by simp) mask1 <| spread_step a 2 _ _ (by simp) mask2 <|
    spread_step a 4 _ _ (by simp) mask4 <| spread_step a 8 _ _ (by simp) mask8 <|
    spread_step a 16 _ _ (by simp) mask16 <| spread_step a 32 _ _ (by simp) mask32 <|
    spread_start a

/-- **`spread` is the carry-less square.** -/
theorem spread_eq (a : BitVec 64) : spread a = cl a a := by
  have h := spread_spread a
  have hbit : ∀ k, (spread a).getLsbD k =
      (decide (k < 128) && decide (k % 2 = 0) && a.getLsbD (k / 2)) := by
    intro k
    rw [h k]
    by_cases hk : k % 2 = 0
    · simp [hk]
    · simp [hk, show ¬ k % (2 * 1) < 1 by omega]
  apply BF64.bitVec_toPoly_injective
  rw [cl, toPoly_carryLessMul _ _ (by norm_num), ← sq, ← ZMod.expand_card]
  ext n
  rw [toPoly_coeff, coeff_bit, Polynomial.coeff_expand (by norm_num), toPoly_coeff, coeff_bit,
    hbit n]
  by_cases hn : n % 2 = 0
  · have h2 : 2 ∣ n := Nat.dvd_of_mod_eq_zero hn
    by_cases hk : n < 128
    · simp [hn, hk, h2]
    · simp [hk, h2, BitVec.getLsbD_of_ge a (n / 2) (by omega)]
  · have h2 : ¬ 2 ∣ n := fun h ↦ hn (Nat.mod_eq_zero_of_dvd h)
    simp [hn, h2]

/-! ## Squares -/

/-- `K::square`. -/
def kSquare (a : BitVec 64) : BitVec 64 := reduce128 (spread a)

/-- **`K::square` is the square.** -/
theorem kSquare_eq (a : K) : kSquare a.toBitVec = (a * a).toBitVec := by
  rw [kSquare, reduce128_eq, spread_eq, reduce_cl]

/-- `E::square`: three carry-less squares, `y^4 = y^2 + y` folding them into three limbs. -/
def esquare (x : Limbs) : Limbs :=
  let s0 := spread x.1
  let s1 := spread x.2.1
  let s2 := spread x.2.2
  (reduce128 s0, reduce128 s2, reduce128 (s1 ^^^ s2))

/-- **`E::square` is the square.** -/
theorem esquare_eq (x : E) : esquare (limbs x) = limbs (x * x) := by
  rw [← lmul_eq]
  unfold limbs
  generalize Ext.coeffNat x 0 = x0, Ext.coeffNat x 1 = x1, Ext.coeffNat x 2 = x2
  simp only [esquare, lmul, emul, reduce128_eq, spread_eq, cl_xor_left, cl_xor_right, reduce_xor,
    reduce_cl, mul_comm x1 x0, mul_comm x2 x0, mul_comm x2 x1, Prod.mk.injEq]
  generalize (x0 * x0).toBitVec = p00, (x0 * x1).toBitVec = p01, (x0 * x2).toBitVec = p02,
    (x1 * x1).toBitVec = p11, (x1 * x2).toBitVec = p12, (x2 * x2).toBitVec = p22
  refine ⟨?_, ?_, ?_⟩ <;> xor_cancel

/-! ## `K::inv` -/

/-- The closure `sq(v, n)`: `n` squarings. -/
def kSq (v : BitVec 64) : ℕ → BitVec 64
  | 0 => v
  | n + 1 => kSq (kSquare v) n

/-- `K::inv`: `a^(2^64 - 2)` by Itoh-Tsujii, each `t_k = a^(2^k - 1)`. -/
def kInv (a : BitVec 64) : BitVec 64 :=
  let t1 := a
  let t2 := baseMul (kSq t1 1) t1
  let t3 := baseMul (kSq t2 1) t1
  let t6 := baseMul (kSq t3 3) t3
  let t12 := baseMul (kSq t6 6) t6
  let t24 := baseMul (kSq t12 12) t12
  let t48 := baseMul (kSq t24 24) t24
  let t60 := baseMul (kSq t48 12) t12
  let t63 := baseMul (kSq t60 3) t3
  kSq t63 1

theorem kSq_eq (a : K) (n : ℕ) : kSq a.toBitVec n = (a ^ 2 ^ n).toBitVec := by
  induction n generalizing a with
  | zero => simp [kSq]
  | succ n ih => rw [kSq, kSquare_eq, ih, ← sq, ← pow_mul, pow_succ, mul_comm]

theorem chain_step {a x y : K} {n m k : ℕ} (hx : x = a ^ (2 ^ n - 1)) (hy : y = a ^ (2 ^ m - 1))
    (hk : n + m = k) : x ^ 2 ^ m * y = a ^ (2 ^ k - 1) := by
  subst hx hy hk
  rw [← pow_mul, ← pow_add]
  congr 1
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  rw [pow_add]
  generalize 2 ^ n = A at *
  generalize 2 ^ m = B at *
  obtain ⟨A, rfl⟩ := Nat.exists_eq_add_of_le' h1
  obtain ⟨B, rfl⟩ := Nat.exists_eq_add_of_le' h2
  simp only [Nat.add_sub_cancel]
  ring_nf
  omega

/-- **`K::inv` is the inverse**, zero to zero. -/
theorem kInv_eq (a : K) : kInv a.toBitVec = a⁻¹.toBitVec := by
  simp only [kInv, kSq_eq, baseMul_eq]
  congr 1
  have e1 : a = a ^ (2 ^ 1 - 1) := by norm_num
  have e2 := chain_step e1 e1 (k := 2) rfl
  have e3 := chain_step e2 e1 (k := 3) rfl
  have e6 := chain_step e3 e3 (k := 6) rfl
  have e12 := chain_step e6 e6 (k := 12) rfl
  have e24 := chain_step e12 e12 (k := 24) rfl
  have e48 := chain_step e24 e24 (k := 48) rfl
  have e60 := chain_step e48 e12 (k := 60) rfl
  have e63 := chain_step e60 e3 (k := 63) rfl
  rw [e63, ← pow_mul]
  by_cases ha : a = 0
  · subst ha
    rw [inv_zero, zero_pow (by norm_num)]
  · apply eq_inv_of_mul_eq_one_right
    have : Fintype K := Fintype.ofFinite K
    have h := FiniteField.pow_card_sub_one_eq_one a ha
    rw [BF64.card_bf64] at h
    rw [← pow_succ', ← h]
    norm_num

/-! ## `E::pow` -/

/-- `E::pow`'s loop: `out *= base` on a set low bit, then `base` squared and the exponent
shifted. -/
def epowLoop (base out : Limbs) (n : BitVec 64) : Limbs :=
  if n = 0 then out
  else
    let out := if n &&& 1 = 1 then lmul out base else out
    epowLoop (esquare base) out (n >>> 1)
termination_by n.toNat
decreasing_by
  rename_i h
  have : n.toNat ≠ 0 := fun h0 ↦ h (BitVec.eq_of_toNat_eq (by simpa using h0))
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

/-- `E::pow`. -/
def epow (x : Limbs) (exponent : BitVec 64) : Limbs := epowLoop x lone exponent

theorem epowLoop_eq (b o : E) (n : BitVec 64) :
    epowLoop (limbs b) (limbs o) n = limbs (o * b ^ n.toNat) := by
  induction h : n.toNat using Nat.strong_induction_on generalizing n b o with
  | _ N ih =>
  subst h
  rw [epowLoop]
  by_cases h0 : n = 0
  · subst h0
    simp
  · rw [ite_eq_right h0]
    have hbit : (if n &&& 1 = 1 then lmul (limbs o) (limbs b) else limbs o) =
        limbs (o * b ^ (n.toNat % 2)) := by
      have hand : (n &&& 1).toNat = n.toNat % 2 := by
        rw [BitVec.toNat_and]; simp [Nat.and_one_is_mod]
      by_cases h1 : n.toNat % 2 = 1
      · rw [ite_eq_left (BitVec.eq_of_toNat_eq (by rw [hand, h1]; rfl)), lmul_eq, h1, pow_one]
      · have h1' : n.toNat % 2 = 0 := by omega
        rw [ite_eq_right (fun h ↦ h1 (by rw [← hand, h]; rfl)), h1', pow_zero, mul_one]
    have hlt : (n >>> 1).toNat < n.toNat := by
      have : n.toNat ≠ 0 := fun h ↦ h0 (BitVec.eq_of_toNat_eq (by simpa using h))
      simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      omega
    simp only
    have hdiv : (n >>> 1).toNat = n.toNat / 2 := by
      simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [hbit, esquare_eq, ih _ hlt _ _ _ rfl, hdiv, mul_assoc, ← sq, ← pow_mul, ← pow_add,
      show n.toNat % 2 + 2 * (n.toNat / 2) = n.toNat by omega]

/-- **`E::pow` is the power.** -/
theorem epow_eq (x : E) (exponent : BitVec 64) :
    epow (limbs x) exponent = limbs (x ^ exponent.toNat) := by
  rw [epow, ← limbs_one, epowLoop_eq, one_mul]

/-! ## `powers` -/

/-- `powers`' loop: push `power`, then multiply it by `base`. -/
def powersLoop (base : Limbs) : ℕ → Limbs → List Limbs → List Limbs
  | 0, _, out => out
  | n + 1, power, out => powersLoop base n (lmul power base) (out ++ [power])

/-- `powers(base, count)`. -/
def powersM (base : Limbs) (count : ℕ) : List Limbs := powersLoop base count lone []

theorem powersLoop_eq (b p : E) (n : ℕ) (out : List Limbs) :
    powersLoop (limbs b) n (limbs p) out =
      out ++ (LeanVM.Protocol.Verifier.powersFrom p b n).map limbs := by
  induction n generalizing p out with
  | zero => simp [powersLoop, LeanVM.Protocol.Verifier.powersFrom]
  | succ n ih =>
    rw [powersLoop, lmul_eq, ih, LeanVM.Protocol.Verifier.powersFrom]
    simp

/-- **`powers` is the specification's `powers`.** -/
theorem powersM_eq (base : E) (count : ℕ) :
    powersM (limbs base) count = (LeanVM.Protocol.Verifier.powers base count).map limbs := by
  rw [powersM, ← limbs_one, powersLoop_eq, List.nil_append]
  rfl

/-! ## `Scaled` -/

/-- `x`, the generator `g` of `K`, in `E`. -/
abbrev ex : E := ofK g

/-- `y`. -/
abbrev ey : E := Ext.gen

/-- `times_x`: a limb times `x`. -/
def timesX (v : BitVec 64) : BitVec 64 := v <<< 1 ^^^ ((0 - (v >>> 63)) &&& 0x1B#64)

theorem cl_two (a : BitVec 64) : cl a 2#64 = (a >>> 63) ++ (a <<< 1) := by
  have h : (a >>> 63) ++ (a <<< 1) = zeroExtendTo (w := 128) a <<< 1 := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp only [BitVec.getLsbD_append, zeroExtendTo, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
    rcases (show k < 64 ∨ k = 64 ∨ 64 < k by omega) with h1 | h1 | h1
    · simp [h1, hk, show k - 1 < 128 by omega]
    · subst h1; simp
    · simp [show ¬ k < 64 by omega, hk, show ¬ k < 1 by omega,
        BitVec.getLsbD_of_ge a (63 + (k - 64)) (by omega), BitVec.getLsbD_of_ge a (k - 1) (by omega)]
  rw [h]
  apply BF64.bitVec_toPoly_injective
  have hlt : (zeroExtendTo (w := 128) a).toNat < 2 ^ 64 := by
    rw [toNat_zeroExtendTo _ (by omega)]; exact a.isLt
  rw [cl, toPoly_carryLessMul _ _ (by norm_num), toPoly_shiftLeft_no_overflow _ hlt (by norm_num),
    toPoly_zeroExtendTo _ (by norm_num),
    show toPoly 2#64 = Polynomial.X ^ 1 from toPoly_one_shiftLeft (w := 64) 1 (by norm_num)]

theorem timesX_eq (a : K) : timesX a.toBitVec = (a * g).toBitVec := by
  rw [← reduce_cl, show g.toBitVec = 2#64 from rfl, cl_two, ← reduceWords_eq]
  generalize a.toBitVec = v
  have hlt : (v >>> 63).toNat < 2 := by
    have := v.isLt
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  have hh : v >>> 63 = 0#64 ∨ v >>> 63 = 1#64 := by
    rcases (show (v >>> 63).toNat = 0 ∨ (v >>> 63).toNat = 1 by omega) with h | h
    · exact Or.inl (BitVec.eq_of_toNat_eq (by simp [h]))
    · exact Or.inr (BitVec.eq_of_toNat_eq (by simp [h]))
  unfold reduceWords timesX
  rcases hh with h | h <;> rw [h] <;> simp only [BitVec.xor_assoc] <;> rfl

/-- `times_x` on each limb. -/
def ltimesX (p : Limbs) : Limbs := (timesX p.1, timesX p.2.1, timesX p.2.2)

/-- `monomial` times `y`, with `y^3 = y + 1`. -/
def ltimesY (m : Limbs) : Limbs := (m.2.2, m.1 ^^^ m.2.2, m.2.1)

/-- XOR identities between atoms, already associated to the left. -/
macro "xor_cancel'" : tactic => `(tactic| (
  ac_nf <;> simp only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor, BitVec.xor_zero]))

theorem ltimesX_eq (z : E) : ltimesX (limbs z) = limbs (z * ex) := by
  rw [← lmul_eq, limbs_ofK, ← BF64.toBitVec_zero]
  unfold limbs
  generalize Ext.coeffNat z 0 = z0, Ext.coeffNat z 1 = z1, Ext.coeffNat z 2 = z2
  simp only [ltimesX, lmul, emul, timesX_eq, cl_xor_left, cl_xor_right, reduce_xor, reduce_cl]
  simp only [mul_zero, BF64.toBitVec_zero, BitVec.xor_zero, Prod.mk.injEq]
  refine ⟨trivial, ?_, ?_⟩ <;> xor_cancel'

theorem ltimesY_eq (z : E) : ltimesY (limbs z) = limbs (z * ey) := by
  rw [← lmul_eq, limbs_gen, ← BF64.toBitVec_zero, ← BF64.toBitVec_one]
  unfold limbs
  generalize Ext.coeffNat z 0 = z0, Ext.coeffNat z 1 = z1, Ext.coeffNat z 2 = z2
  simp only [ltimesY, lmul, emul, cl_xor_left, cl_xor_right, reduce_xor, reduce_cl]
  simp only [mul_zero, mul_one, BF64.toBitVec_zero, BitVec.xor_zero, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> xor_cancel'

/-- A word of `K` is the sum of the powers of `x` at its set bits. -/
theorem sum_bits (c : BitVec 64) :
    ∑ k ∈ Finset.range 64, (if c.getLsbD k then g ^ k else 0) = BF64.ofBitVec c := by
  apply BF64.toQuot_injective
  let φ : K →+ BF64.BF64Quot := AddMonoidHom.mk' BF64.toQuot BF64.toQuot_add
  have hsum : ∀ f : ℕ → K, BF64.toQuot (∑ k ∈ Finset.range 64, f k) =
      ∑ k ∈ Finset.range 64, BF64.toQuot (f k) := fun f ↦ map_sum φ f _
  have hg : BF64.toQuot g = AdjoinRoot.mk BF64.basePoly Polynomial.X := by
    rw [BF64.toQuot, BF64.toPolyBF64,
      show toPoly g.toBitVec = Polynomial.X ^ 1 from toPoly_one_shiftLeft (w := 64) 1 (by norm_num),
      pow_one]
  rw [hsum, BF64.toQuot, BF64.toPolyBF64, BF64.toBitVec_ofBitVec, toPoly, map_sum,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [apply_ite BF64.toQuot, BF64.toQuot_npow, BF64.toQuot_zero, hg, apply_ite (AdjoinRoot.mk _),
    map_pow, map_zero]
  rfl

theorem ofK_sum_bits (c : BitVec 64) :
    ∑ k ∈ Finset.range 64, (if c.getLsbD k then ex ^ k else 0) = ofK (BF64.ofBitVec c) := by
  rw [← sum_bits c]
  change _ = algebraMap K E _
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  split <;> simp [map_pow]

/-- An `E` from its limbs. -/
theorem eq_of_limbs_sum (a : E) :
    a = ofK (BF64.ofBitVec (limbs a).1) + ofK (BF64.ofBitVec (limbs a).2.1) * ey +
      ofK (BF64.ofBitVec (limbs a).2.2) * ey * ey := by
  apply limbs_inj
  rw [← ladd_eq, ← ladd_eq, ← ltimesY_eq, ← ltimesY_eq, ← ltimesY_eq, limbs_ofK, limbs_ofK,
    limbs_ofK]
  rcases limbs a with ⟨a0, a1, a2⟩
  simp [ladd, ltimesY]

/-! ### The tables -/

/-- `table[1 << bit | low] = table[low] + power`, the table at `base` of the flat run. -/
def fillStep (base bit : ℕ) (power : Limbs) (tables : List Limbs) (low : ℕ) : List Limbs :=
  tables.set (base + (1 <<< bit ||| low)) (ladd (tables.getD (base + low) lzero) power)

/-- `for low in 0..1 << bit`. -/
def fillBit (base bit : ℕ) (power : Limbs) (tables : List Limbs) : List Limbs :=
  (List.range (1 <<< bit)).foldl (fillStep base bit power) tables

/-- One table: `for bit in 0..WINDOW`, `power` times `x` after each bit. -/
def fillTable (base : ℕ) (state : List Limbs × Limbs) : List Limbs × Limbs :=
  (List.range 6).foldl (fun state bit ↦ (fillBit base bit state.2 state.1, ltimesX state.2)) state

/-- One limb's `WINDOWS_PER_LIMB` tables, `power` starting at `monomial`. -/
def fillLimb (t : ℕ) (state : List Limbs × Limbs) : List Limbs × Limbs :=
  (List.range 11).foldl (fun state j ↦ fillTable ((t * 11 + j) * 64) state) state

/-- `Scaled::new(r)`: the flat run of `3 * WINDOWS_PER_LIMB` tables of `1 << WINDOW` entries,
`monomial` times `y` after each limb. -/
def scaledTable (r : Limbs) : List Limbs :=
  ((List.range 3).foldl
    (fun state t ↦ ((fillLimb t (state.1, state.2)).1, ltimesY state.2))
    (List.replicate ((3 * 11) <<< 6) lzero, r)).1

/-- Entry `i` of the tables: table `i / 64` is window `j = i % 704 / 64` of limb `t = i / 704`,
and its entry `n = i % 64` is the sum of `r y^t x^(6j + b)` over the set bits `b` of `n`. -/
def entry (r : E) (i : ℕ) : E :=
  ∑ b ∈ Finset.range 6,
    if (i % 64).testBit b then r * ey ^ (i / 704) * ex ^ (6 * (i % 704 / 64) + b) else 0

/-- The tables hold `entry` below `p`, and zero from `p` on. -/
def Filled (r : E) (p : ℕ) (tables : List Limbs) : Prop :=
  tables.length = 2112 ∧ ∀ i, tables.getD i lzero = if i < p then limbs (entry r i) else lzero

theorem getD_set (l : List Limbs) (i j : ℕ) (a d : Limbs) :
    (l.set i a).getD j d = if i = j ∧ i < l.length then a else l.getD j d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h1 : i = j
  · subst h1
    by_cases h2 : i < l.length
    · simp [h2]
    · simp [h2]
  · simp [h1]

theorem testBit_two_pow_add (k m b : ℕ) (hm : m < 2 ^ k) :
    (2 ^ k + m).testBit b = (m.testBit b || decide (b = k)) := by
  rcases (show b < k ∨ b = k ∨ k < b by omega) with h | h | h
  · rw [Nat.testBit_two_pow_add_gt h]; simp [show b ≠ k by omega]
  · subst h; rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hm]; simp
  · have hb : 2 ^ (k + 1) ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h
    rw [Nat.testBit_lt_two_pow (by rw [pow_succ] at hb; omega),
      Nat.testBit_lt_two_pow (by rw [pow_succ] at hb; omega)]
    simp [show b ≠ k by omega]

theorem sum_bits_add (f : ℕ → E) (k m : ℕ) (hk : k < 6) (hm : m < 2 ^ k) :
    ∑ b ∈ Finset.range 6, (if (2 ^ k + m).testBit b then f b else 0) =
      ∑ b ∈ Finset.range 6, (if m.testBit b then f b else 0) + f k := by
  have hk' : m.testBit k = false := Nat.testBit_lt_two_pow hm
  have hf : ∑ b ∈ Finset.range 6, (if b = k then f b else 0) = f k := by simp [hk]
  rw [← hf, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [testBit_two_pow_add k m b hm]
  by_cases hb : b = k
  · subst hb; simp [hk']
  · simp [hb]

theorem entry_add (r : E) (t j k m : ℕ) (hj : j < 11) (hk : k < 6) (hm : m < 2 ^ k) :
    entry r ((t * 11 + j) * 64 + 2 ^ k + m) =
      entry r ((t * 11 + j) * 64 + m) + r * ey ^ t * ex ^ (6 * j + k) := by
  have hP : 2 ^ k ≤ 32 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show k ≤ 5 by omega); simpa using this
  unfold entry
  generalize hP' : 2 ^ k = P at hm hP
  have e1 : ((t * 11 + j) * 64 + P + m) % 64 = P + m := by omega
  have e2 : ((t * 11 + j) * 64 + P + m) / 704 = t := by omega
  have e3 : ((t * 11 + j) * 64 + P + m) % 704 / 64 = j := by omega
  have e4 : ((t * 11 + j) * 64 + m) % 64 = m := by omega
  have e5 : ((t * 11 + j) * 64 + m) / 704 = t := by omega
  have e6 : ((t * 11 + j) * 64 + m) % 704 / 64 = j := by omega
  rw [e1, e2, e3, e4, e5, e6, ← hP']
  exact sum_bits_add (fun b ↦ r * ey ^ t * ex ^ (6 * j + b)) k m hk (hP' ▸ hm)

theorem fillBit_prefix (base bit : ℕ) (power : Limbs) (l : List Limbs)
    (hlen : base + 2 ^ (bit + 1) ≤ l.length) (m : ℕ) (hm : m ≤ 2 ^ bit) :
    ((List.range m).foldl (fillStep base bit power) l).length = l.length ∧
      ∀ i, ((List.range m).foldl (fillStep base bit power) l).getD i lzero =
        if base + 2 ^ bit ≤ i ∧ i < base + 2 ^ bit + m then ladd (l.getD (i - 2 ^ bit) lzero) power
        else l.getD i lzero := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨ihl, ihg⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, fillStep]
    have hor : 1 <<< bit ||| m = 2 ^ bit + m := by
      rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.one_shiftLeft]
    rw [hor]
    rw [pow_succ] at hlen
    refine ⟨by rw [List.length_set, ihl], fun i ↦ ?_⟩
    rw [getD_set, ihl, ihg (base + m)]
    have hbm : ¬ (base + 2 ^ bit ≤ base + m ∧ base + m < base + 2 ^ bit + m) := by omega
    rw [ite_eq_right hbm, ihg i]
    by_cases hi : base + (2 ^ bit + m) = i
    · subst hi
      rw [ite_eq_left ⟨rfl, by omega⟩, ite_eq_left ⟨by omega, by omega⟩,
        show base + (2 ^ bit + m) - 2 ^ bit = base + m by omega]
    · rw [ite_eq_right (fun h ↦ hi h.1)]
      by_cases hr : base + 2 ^ bit ≤ i ∧ i < base + 2 ^ bit + m
      · rw [ite_eq_left hr, ite_eq_left ⟨hr.1, by omega⟩]
      · rw [ite_eq_right hr, ite_eq_right (by omega)]

theorem fillBit_filled (r : E) (t j k : ℕ) (ht : t < 3) (hj : j < 11) (hk : k < 6)
    (l : List Limbs) (hl : Filled r ((t * 11 + j) * 64 + 2 ^ k) l) :
    Filled r ((t * 11 + j) * 64 + 2 ^ (k + 1))
      (fillBit ((t * 11 + j) * 64) k (limbs (r * ey ^ t * ex ^ (6 * j + k))) l) := by
  have hP : 2 ^ k ≤ 32 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show k ≤ 5 by omega); simpa using this
  have hP1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  obtain ⟨hlen, hget⟩ := hl
  obtain ⟨hl', hg'⟩ := fillBit_prefix ((t * 11 + j) * 64) k
    (limbs (r * ey ^ t * ex ^ (6 * j + k))) l (by omega) (2 ^ k) le_rfl
  rw [fillBit, Nat.one_shiftLeft]
  refine ⟨by rw [hl', hlen], fun i ↦ ?_⟩
  rw [hg' i]
  by_cases hr : (t * 11 + j) * 64 + 2 ^ k ≤ i ∧ i < (t * 11 + j) * 64 + 2 ^ k + 2 ^ k
  · rw [ite_eq_left hr, ite_eq_left (by omega), hget, ite_eq_left (by omega), ladd_eq]
    obtain ⟨m, rfl⟩ : ∃ m, i = (t * 11 + j) * 64 + 2 ^ k + m := ⟨i - ((t * 11 + j) * 64 + 2 ^ k), by omega⟩
    rw [entry_add r t j k m hj hk (by omega), show (t * 11 + j) * 64 + 2 ^ k + m - 2 ^ k =
      (t * 11 + j) * 64 + m by omega]
  · rw [ite_eq_right hr, hget]
    by_cases h1 : i < (t * 11 + j) * 64 + 2 ^ k
    · rw [ite_eq_left h1, ite_eq_left (by omega)]
    · rw [ite_eq_right h1, ite_eq_right (by omega)]

theorem entry_base (r : E) (t j : ℕ) : entry r ((t * 11 + j) * 64) = 0 := by
  unfold entry
  rw [show (t * 11 + j) * 64 % 64 = 0 by omega]
  simp

theorem fillTable_filled (r : E) (t j : ℕ) (ht : t < 3) (hj : j < 11) (l : List Limbs)
    (hl : Filled r ((t * 11 + j) * 64) l) :
    Filled r ((t * 11 + j) * 64 + 64)
        (fillTable ((t * 11 + j) * 64) (l, limbs (r * ey ^ t * ex ^ (6 * j)))).1 ∧
      (fillTable ((t * 11 + j) * 64) (l, limbs (r * ey ^ t * ex ^ (6 * j)))).2 =
        limbs (r * ey ^ t * ex ^ (6 * (j + 1))) := by
  have key : ∀ k ≤ 6,
      Filled r ((t * 11 + j) * 64 + 2 ^ k)
          ((List.range k).foldl (fun state bit ↦ (fillBit ((t * 11 + j) * 64) bit state.2 state.1,
            ltimesX state.2)) (l, limbs (r * ey ^ t * ex ^ (6 * j)))).1 ∧
        ((List.range k).foldl (fun state bit ↦ (fillBit ((t * 11 + j) * 64) bit state.2 state.1,
            ltimesX state.2)) (l, limbs (r * ey ^ t * ex ^ (6 * j)))).2 =
          limbs (r * ey ^ t * ex ^ (6 * j + k)) := by
    intro k hk
    induction k with
    | zero =>
      simp only [List.range_zero, List.foldl_nil]
      refine ⟨⟨hl.1, fun i ↦ ?_⟩, by rw [Nat.add_zero]⟩
      rw [hl.2 i]
      by_cases h1 : i < (t * 11 + j) * 64
      · rw [ite_eq_left h1, ite_eq_left (by simp; omega)]
      · rw [ite_eq_right h1]
        by_cases h2 : i = (t * 11 + j) * 64
        · subst h2; rw [ite_eq_left (by simp), entry_base, limbs_zero]
        · rw [ite_eq_right (by simp; omega)]
    | succ k ih =>
      obtain ⟨h1, h2⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      simp only
      rw [h2]
      refine ⟨fillBit_filled r t j k ht hj (by omega) _ h1, ?_⟩
      rw [ltimesX_eq, mul_assoc, ← pow_succ, Nat.add_assoc]
  obtain ⟨h1, h2⟩ := key 6 le_rfl
  exact ⟨h1, by rw [fillTable, h2]; ring_nf⟩

theorem fillLimb_filled (r : E) (t : ℕ) (ht : t < 3) (l : List Limbs)
    (hl : Filled r (t * 11 * 64) l) :
    Filled r ((t + 1) * 704) (fillLimb t (l, limbs (r * ey ^ t))).1 := by
  have key : ∀ w ≤ 11,
      Filled r ((t * 11 + w) * 64)
          ((List.range w).foldl (fun state j ↦ fillTable ((t * 11 + j) * 64) state)
            (l, limbs (r * ey ^ t))).1 ∧
        ((List.range w).foldl (fun state j ↦ fillTable ((t * 11 + j) * 64) state)
            (l, limbs (r * ey ^ t))).2 = limbs (r * ey ^ t * ex ^ (6 * w)) := by
    intro w hw
    induction w with
    | zero => exact ⟨by simpa using hl, by simp⟩
    | succ w ih =>
      obtain ⟨h1, h2⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      generalize hs : (List.range w).foldl (fun state j ↦ fillTable ((t * 11 + j) * 64) state)
        (l, limbs (r * ey ^ t)) = s at h1 h2
      obtain ⟨s1, s2⟩ := s
      simp only at h1 h2
      subst h2
      obtain ⟨h3, h4⟩ := fillTable_filled r t w ht (by omega) s1 h1
      exact ⟨by rw [show (t * 11 + (w + 1)) * 64 = (t * 11 + w) * 64 + 64 by ring]; exact h3, h4⟩
  have := (key 11 le_rfl).1
  rw [show (t * 11 + 11) * 64 = (t + 1) * 704 by ring] at this
  exact this

theorem scaledTable_filled (r : E) : Filled r 2112 (scaledTable (limbs r)) := by
  have key : ∀ u ≤ 3,
      Filled r (u * 704)
          ((List.range u).foldl
            (fun state t ↦ ((fillLimb t (state.1, state.2)).1, ltimesY state.2))
            (List.replicate ((3 * 11) <<< 6) lzero, limbs r)).1 ∧
        ((List.range u).foldl
            (fun state t ↦ ((fillLimb t (state.1, state.2)).1, ltimesY state.2))
            (List.replicate ((3 * 11) <<< 6) lzero, limbs r)).2 = limbs (r * ey ^ u) := by
    intro u hu
    induction u with
    | zero =>
      simp only [List.range_zero, List.foldl_nil]
      refine ⟨⟨List.length_replicate, fun i ↦ ?_⟩, by rw [pow_zero, mul_one]⟩
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split <;> simp
    | succ u ih =>
      obtain ⟨h1, h2⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      simp only
      rw [h2, ltimesY_eq, mul_assoc, ← pow_succ]
      refine ⟨?_, rfl⟩
      exact fillLimb_filled r u (by omega) _ (by rw [show u * 11 * 64 = u * 704 by ring]; exact h1)
  exact (key 3 le_rfl).1

/-! ### The product -/

/-- One lookup: `product += table[(table << WINDOW) | window value]`, then the next table. -/
def mulStep (tables : List Limbs) (limb : BitVec 64) (state : Limbs × ℕ) (window : ℕ) :
    Limbs × ℕ :=
  (ladd state.1 (tables.getD (state.2 <<< 6 ||| (limb >>> (6 * window)).toNat % (1 <<< 6)) lzero),
    state.2 + 1)

/-- `Scaled::mul(a)`: for each limb, `WINDOWS_PER_LIMB` lookups. -/
def scaledMul (tables : List Limbs) (a : Limbs) : Limbs :=
  ([a.1, a.2.1, a.2.2].foldl
    (fun state limb ↦ (List.range 11).foldl (mulStep tables limb) state) (lzero, 0)).1

theorem sum_range_six_mul (f : ℕ → E) (n : ℕ) :
    ∑ k ∈ Finset.range (6 * n), f k = ∑ j ∈ Finset.range n, ∑ b ∈ Finset.range 6, f (6 * j + b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 6 * (n + 1) = 6 * n + 6 by ring, Finset.sum_range_add, ih,
      Finset.sum_range_succ (fun j ↦ ∑ b ∈ Finset.range 6, f (6 * j + b)) n]

theorem windows_sum (r : E) (t : ℕ) (c : BitVec 64) :
    ∑ j ∈ Finset.range 11, entry r ((t * 11 + j) * 64 + (c >>> (6 * j)).toNat % 64) =
      r * ey ^ t * ofK (BF64.ofBitVec c) := by
  rw [← ofK_sum_bits, Finset.mul_sum]
  have h66 : ∑ k ∈ Finset.range 64, r * ey ^ t * (if c.getLsbD k then ex ^ k else 0) =
      ∑ k ∈ Finset.range (6 * 11), (if c.getLsbD k then r * ey ^ t * ex ^ k else 0) := by
    rw [show 6 * 11 = 64 + 2 by rfl, Finset.sum_range_add]
    simp [mul_ite]
  rw [h66, sum_range_six_mul]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj := Finset.mem_range.1 hj
  unfold entry
  have hn : (c >>> (6 * j)).toNat % 64 < 64 := Nat.mod_lt _ (by norm_num)
  generalize hN : (c >>> (6 * j)).toNat % 64 = n at hn
  rw [show ((t * 11 + j) * 64 + n) % 64 = n by omega, show ((t * 11 + j) * 64 + n) / 704 = t by omega,
    show ((t * 11 + j) * 64 + n) % 704 / 64 = j by omega]
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  have hb := Finset.mem_range.1 hb
  have : n.testBit b = c.getLsbD (6 * j + b) := by
    rw [← hN, show (c >>> (6 * j)).toNat % 64 = (c >>> (6 * j)).toNat % 2 ^ 6 by norm_num,
      Nat.testBit_mod_two_pow, BitVec.toNat_ushiftRight,
      Nat.testBit_shiftRight, BitVec.testBit_toNat]
    simp [hb]
  rw [this]

theorem mulStep_fold (r : E) (tables : List Limbs) (htab : Filled r 2112 tables) (t : ℕ) (ht : t < 3)
    (c : BitVec 64) (p : E) :
    (List.range 11).foldl (mulStep tables c) (limbs p, t * 11) =
      (limbs (p + r * ey ^ t * ofK (BF64.ofBitVec c)), (t + 1) * 11) := by
  have key : ∀ w ≤ 11, (List.range w).foldl (mulStep tables c) (limbs p, t * 11) =
      (limbs (p + ∑ j ∈ Finset.range w, entry r ((t * 11 + j) * 64 + (c >>> (6 * j)).toNat % 64)),
        t * 11 + w) := by
    intro w hw
    induction w with
    | zero => simp
    | succ w ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega),
        mulStep]
      have hn : (c >>> (6 * w)).toNat % 64 < 64 := Nat.mod_lt _ (by norm_num)
      rw [show (1 <<< 6 : ℕ) = 64 by rfl, ← Nat.shiftLeft_add_eq_or_of_lt (by simpa using hn),
        Nat.shiftLeft_eq, htab.2, ite_eq_left (by omega), ladd_eq, Finset.sum_range_succ, add_assoc,
        show (t * 11 + w) * 2 ^ 6 = (t * 11 + w) * 64 by rfl]
      rfl
  rw [key 11 le_rfl, windows_sum r t c, show t * 11 + 11 = (t + 1) * 11 by ring]

/-- **`Scaled::mul` of `Scaled::new(r)` is the product by `r`.** -/
theorem scaledMul_eq (r a : E) : scaledMul (scaledTable (limbs r)) (limbs a) = limbs (r * a) := by
  have htab := scaledTable_filled r
  unfold scaledMul
  rw [List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_nil,
    show (lzero, 0) = (limbs 0, 0 * 11) from rfl, mulStep_fold r _ htab 0 (by norm_num),
    mulStep_fold r _ htab 1 (by norm_num), mulStep_fold r _ htab 2 (by norm_num)]
  conv_rhs => rw [eq_of_limbs_sum a]
  exact congrArg limbs (by ring)

/-! ## `E::inv` -/

/-- `E::frobenius`: `x^(2^64)`, `y` to `y^2`. -/
def frobenius (x : Limbs) : Limbs := (x.1, x.2.2, x.2.1 ^^^ x.2.2)

/-- `E::inv`: `m` the product of the two conjugates, `x * m` in `K`, and `m` times its inverse. -/
def einv (x : Limbs) : Limbs :=
  let m := lmul (frobenius x) (frobenius (frobenius x))
  let norm := lmul x m
  lmul m (kInv norm.1, 0#64, 0#64)

/-- The word `a + b y + c y^2`. -/
def ofParts (a b c : K) : E := ofK a + ofK b * ey + ofK c * ey * ey

theorem limbs_ofParts (a b c : K) : limbs (ofParts a b c) = (a.toBitVec, b.toBitVec, c.toBitVec) := by
  rw [ofParts, ← ladd_eq, ← ladd_eq, ← ltimesY_eq, ← ltimesY_eq, ← ltimesY_eq, limbs_ofK, limbs_ofK,
    limbs_ofK]
  simp [ladd, ltimesY]

theorem ofParts_eq_zero {a b c : K} (h : ofParts a b c = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have h' := congrArg limbs h
  rw [limbs_ofParts, limbs_zero, lzero, Prod.mk.injEq, Prod.mk.injEq] at h'
  exact ⟨BF64.toBitVec_injective h'.1, BF64.toBitVec_injective h'.2.1,
    BF64.toBitVec_injective h'.2.2⟩

theorem frobenius_ofParts (a b c : K) :
    frobenius (limbs (ofParts a b c)) = limbs (ofParts a c (b + c)) := by
  rw [limbs_ofParts, limbs_ofParts]
  rfl

theorem ey_cube : ey ^ 3 = ey + 1 := by
  apply limbs_inj
  rw [pow_succ, pow_two, ← ltimesY_eq, ← ltimesY_eq, ← ladd_eq, limbs_gen, limbs_one]
  rfl

/-- The norm: `x` times its two conjugates lies in `K`. -/
theorem norm_ofParts (a b c : K) :
    ofParts a b c * (ofParts a c (b + c) * ofParts a (b + c) (c + (b + c))) =
      ofK (c ^ 3 + b * c ^ 2 + b ^ 3 + a * c ^ 2 + a * b * c + a * b ^ 2 + a ^ 3) := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  unfold ofParts
  rw [show (ofK : K → E) = algebraMap K E from rfl]
  simp only [map_add, map_mul, map_pow]
  generalize algebraMap K E a = A, algebraMap K E b = B, algebraMap K E c = C
  generalize hY : ey = Y
  have hY3 : Y ^ 3 = Y + 1 := hY ▸ ey_cube
  linear_combination (5 * C ^ 3 + 3 * C ^ 3 * Y + 3 * C ^ 3 * Y ^ 2 + 2 * C ^ 3 * Y ^ 3 + 9 * B * C ^ 2 + 7 * B * C ^ 2 * Y + 5 * B * C ^ 2 * Y ^ 2 + 3 * B * C ^ 2 * Y ^ 3 + 6 * B ^ 2 * C + 4 * B ^ 2 * C * Y + 4 * B ^ 2 * C * Y ^ 2 + B ^ 2 * C * Y ^ 3 + B ^ 3 + B ^ 3 * Y + B ^ 3 * Y ^ 2 + 5 * A * C ^ 2 + 5 * A * C ^ 2 * Y + 7 * A * B * C + 5 * A * B * C * Y + 3 * A * B ^ 2 + A * B ^ 2 * Y) * hY3 + (2 * C ^ 3 + 4 * C ^ 3 * Y + 3 * C ^ 3 * Y ^ 2 + 4 * B * C ^ 2 + 8 * B * C ^ 2 * Y + 6 * B * C ^ 2 * Y ^ 2 + 3 * B ^ 2 * C + 5 * B ^ 2 * C * Y + 4 * B ^ 2 * C * Y ^ 2 + B ^ 3 * Y + B ^ 3 * Y ^ 2 + 2 * A * C ^ 2 + 5 * A * C ^ 2 * Y + 3 * A * C ^ 2 * Y ^ 2 + 3 * A * B * C + 6 * A * B * C * Y + 4 * A * B * C * Y ^ 2 + A * B ^ 2 + 2 * A * B ^ 2 * Y + A * B ^ 2 * Y ^ 2 + A ^ 2 * C * Y + 2 * A ^ 2 * C * Y ^ 2 + A ^ 2 * B * Y + A ^ 2 * B * Y ^ 2) * h2

/-- The verifier inverts in `K` (`whir.rs`, `induced_weight`) where the specification inverts in
`E`. -/
theorem ofK_inv (a : K) : ofK a⁻¹ = (ofK a)⁻¹ := map_inv₀ (algebraMap K E) a

/-- **`E::inv` is the inverse**, zero to zero. -/
theorem einv_eq (x : E) : einv (limbs x) = limbs x⁻¹ := by
  rw [eq_of_limbs_sum x]
  generalize BF64.ofBitVec (limbs x).1 = a, BF64.ofBitVec (limbs x).2.1 = b,
    BF64.ofBitVec (limbs x).2.2 = c
  rw [show ofK a + ofK b * ey + ofK c * ey * ey = ofParts a b c from rfl]
  unfold einv
  dsimp only
  rw [frobenius_ofParts, frobenius_ofParts, lmul_eq, lmul_eq, norm_ofParts, limbs_ofK, kInv_eq, ← limbs_ofK, lmul_eq]
  refine congrArg limbs ?_
  generalize hn : c ^ 3 + b * c ^ 2 + b ^ 3 + a * c ^ 2 + a * b * c + a * b ^ 2 + a ^ 3 = n
  have hN := norm_ofParts a b c
  rw [hn] at hN
  by_cases hx : ofParts a b c = 0
  · obtain ⟨rfl, rfl, rfl⟩ := ofParts_eq_zero hx
    rw [hx, inv_zero, add_zero]
    have : ofParts 0 0 0 = 0 := hx
    rw [this, zero_mul, zero_mul]
  · have hn0 : n ≠ 0 := by
      rintro rfl
      simp only [ofK, Ext.ofBase_zero] at hN
      rcases mul_eq_zero.1 hN with h | h
      · exact hx h
      · rcases mul_eq_zero.1 h with h | h
        · obtain ⟨rfl, rfl, h3⟩ := ofParts_eq_zero h
          rw [add_zero] at h3
          exact hx (by rw [h3]; simp [ofParts, ofK])
        · obtain ⟨rfl, h1, h3⟩ := ofParts_eq_zero h
          rw [h1, add_zero] at h3
          rw [h3, add_zero] at h1
          exact hx (by rw [h1, h3]; simp [ofParts, ofK])
    apply eq_inv_of_mul_eq_one_right
    rw [← mul_assoc, hN]
    change algebraMap K E n * algebraMap K E n⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hn0, map_one]

end Rv64Verifier.Model
