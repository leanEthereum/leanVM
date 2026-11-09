import Statement.Field
import Mathlib.Tactic.Ring

/-!
# Products in `E` on machine words

`E`'s product compiles generically (`Statement.Fast.QuadExt`: `Ext.mulCubic`, each coefficient
product a call of `BF64.mul`), and a `K` word that is no small number is a big natural number at
run time, so every product of `K` words converts its factors to machine words and its result back,
each conversion of a big number a few allocations. Here the product of two elements of `E`
converts its six limbs once, computes the nine coefficient products and the reduction by
`y^3 = y + 1` on machine words, and converts the three limbs of the result back (`mulEW`,
`mulE_eq_mulEW`); a power is computed on words throughout, by squaring (`powEW`, `powE_eq_powEW`).

`mulE` and `powE` are `E`'s product and power, monomorphic: the copies of the prover
(`LeanVM.Prover.Fast.Copy`) call them where the statement's prover multiplies in `E`, and they
compile as the word-level computations.
-/

namespace LeanVM.Prover.Fast

open LeanVM.Parameters CompPoly.Extension

/-- The product in `E`. -/
def mulE (x y : E) : E := x * y

/-- A power in `E`. -/
def powE (x : E) (n : ℕ) : E := x ^ n

/-! ## Words -/

/-- A `K` word as a machine word. -/
@[inline] def wOf (a : K) : UInt64 := UInt64.ofBitVec a.toBitVec

/-- A machine word as a `K` word. -/
@[inline] def kOf (u : UInt64) : K := BF64.ofBitVec u.toBitVec

theorem kOf_wOf (a : K) : kOf (wOf a) = a := rfl

theorem kOf_xor (a b : UInt64) : kOf (a ^^^ b) = kOf a + kOf b := by
  apply BF64.ext
  simp [kOf, UInt64.toBitVec_xor]
  rfl

/-- The product of two words of `K`, reduced: the loop over the bits of the smaller one
(`BF64.mulWords`). -/
@[inline] def mulW (a b : UInt64) : UInt64 :=
  if a ≤ b then BF64.mulShift a 0 b 0 0 else BF64.mulShift b 0 a 0 0

theorem kOf_mulW (a b : UInt64) : kOf (mulW a b) = kOf a * kOf b := by
  have h := congrFun (congrFun BF64.mul_eq_mulWords (kOf a)) (kOf b)
  rw [BF64.mul_def, h]
  rfl

/-! ## Triples of words -/

/-- An element of `E` as its three limbs' machine words. -/
structure W3 where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64

/-- The element of `E` of three words. -/
@[inline] def W3.toE (a : W3) : E := E.ofLimbs (kOf a.w0) (kOf a.w1) (kOf a.w2)

/-- The three words of an element of `E`. -/
@[inline] def W3.ofE (x : E) : W3 := ⟨wOf (x.limb 0), wOf (x.limb 1), wOf (x.limb 2)⟩

theorem W3.toE_ofE (x : E) : (W3.ofE x).toE = x := by
  apply Ext.ext
  intro i
  fin_cases i <;> rfl

/-- The product on words: the nine coefficient products, then `y^3 = y + 1`, `y^4 = y^2 + y`. -/
@[inline] def W3.mul9 (a b : W3) : W3 :=
  let c3 := mulW a.w1 b.w2 ^^^ mulW a.w2 b.w1
  let c4 := mulW a.w2 b.w2
  ⟨mulW a.w0 b.w0 ^^^ c3,
    mulW a.w0 b.w1 ^^^ mulW a.w1 b.w0 ^^^ c3 ^^^ c4,
    mulW a.w0 b.w2 ^^^ mulW a.w1 b.w1 ^^^ mulW a.w2 b.w0 ^^^ c4⟩

/-- The reduced monomials of `E`: `y^3 = 1 + y`, `y^4 = y + y^2`. -/
theorem monomialMod_three : (Ext.monomialMod 3 : E) = E.ofLimbs 1 1 0 := by
  apply Ext.ext
  intro i
  rw [Ext.monomialMod_succ', Ext.coeff_shiftReduce]
  have h2 : ∀ m, m < 3 → Ext.coeffNat (Ext.monomialMod 2 : E) m = if 2 = m then 1 else 0 :=
    fun m hm ↦ Ext.coeffNat_monomialMod_of_lt (by decide) hm
  fin_cases i <;> simp [h2] <;> rfl

theorem monomialMod_four : (Ext.monomialMod 4 : E) = E.ofLimbs 0 1 1 := by
  apply Ext.ext
  intro i
  rw [Ext.monomialMod_succ', Ext.coeff_shiftReduce]
  have h3 : ∀ m, m < 3 →
      Ext.coeffNat (Ext.monomialMod 3 : E) m = Ext.coeffNat (E.ofLimbs 1 1 0) m := by
    rw [monomialMod_three]; intros; rfl
  fin_cases i <;> simp [h3] <;> decide +kernel

/-- **The schoolbook product on words is `E`'s product.** -/
theorem W3.toE_mul9 (a b : W3) : (W3.mul9 a b).toE = a.toE * b.toE := by
  have t30 : Ext.coeffNat (Ext.monomialMod 3 : E) 0 = 1 := by rw [monomialMod_three]; rfl
  have t31 : Ext.coeffNat (Ext.monomialMod 3 : E) 1 = 1 := by rw [monomialMod_three]; rfl
  have t32 : Ext.coeffNat (Ext.monomialMod 3 : E) 2 = 0 := by rw [monomialMod_three]; rfl
  have t40 : Ext.coeffNat (Ext.monomialMod 4 : E) 0 = 0 := by rw [monomialMod_four]; rfl
  have t41 : Ext.coeffNat (Ext.monomialMod 4 : E) 1 = 1 := by rw [monomialMod_four]; rfl
  have t42 : Ext.coeffNat (Ext.monomialMod 4 : E) 2 = 1 := by rw [monomialMod_four]; rfl
  rw [show a.toE * b.toE = Ext.mul a.toE b.toE from rfl, Ext.mul_eq_mulCubic (h := BF64.ext3Params_d)]
  apply Ext.ext
  rintro ⟨m, hm⟩
  have hm3 : m < 3 := hm
  set x0 := kOf a.w0
  set x1 := kOf a.w1
  set x2 := kOf a.w2
  set y0 := kOf b.w0
  set y1 := kOf b.w1
  set y2 := kOf b.w2
  interval_cases m
  · show kOf (mulW a.w0 b.w0 ^^^ (mulW a.w1 b.w2 ^^^ mulW a.w2 b.w1)) =
      x0 * y0 + (x1 * y2 + x2 * y1) * Ext.coeffNat (Ext.monomialMod 3 : E) 0 +
        x2 * y2 * Ext.coeffNat (Ext.monomialMod 4 : E) 0
    rw [t30, t40]; simp only [kOf_xor, kOf_mulW]; ring
  · show kOf (mulW a.w0 b.w1 ^^^ mulW a.w1 b.w0 ^^^ (mulW a.w1 b.w2 ^^^ mulW a.w2 b.w1) ^^^
        mulW a.w2 b.w2) =
      x0 * y1 + x1 * y0 + (x1 * y2 + x2 * y1) * Ext.coeffNat (Ext.monomialMod 3 : E) 1 +
        x2 * y2 * Ext.coeffNat (Ext.monomialMod 4 : E) 1
    rw [t31, t41]; simp only [kOf_xor, kOf_mulW]; ring
  · show kOf (mulW a.w0 b.w2 ^^^ mulW a.w1 b.w1 ^^^ mulW a.w2 b.w0 ^^^ mulW a.w2 b.w2) =
      x0 * y2 + x1 * y1 + x2 * y0 + (x1 * y2 + x2 * y1) * Ext.coeffNat (Ext.monomialMod 3 : E) 2 +
        x2 * y2 * Ext.coeffNat (Ext.monomialMod 4 : E) 2
    rw [t32, t42]; simp only [kOf_xor, kOf_mulW]; ring

/-- In characteristic two a sum of equals vanishes. -/
theorem K.add_self (z : K) : z + z = 0 := by
  apply BF64.ext
  show z.toBitVec ^^^ z.toBitVec = 0#64
  simp

/-- The product on words by Karatsuba: six coefficient products, `p_ij = (a_i + a_j)(b_i + b_j)`,
then the reduction. -/
@[inline] def W3.mul (a b : W3) : W3 :=
  let p00 := mulW a.w0 b.w0
  let p11 := mulW a.w1 b.w1
  let p22 := mulW a.w2 b.w2
  let p12 := mulW (a.w1 ^^^ a.w2) (b.w1 ^^^ b.w2)
  ⟨p00 ^^^ p11 ^^^ p22 ^^^ p12,
    p00 ^^^ mulW (a.w0 ^^^ a.w1) (b.w0 ^^^ b.w1) ^^^ p12,
    p00 ^^^ mulW (a.w0 ^^^ a.w2) (b.w0 ^^^ b.w2) ^^^ p11⟩

/-- **The product on words is `E`'s product.** -/
theorem W3.toE_mul (a b : W3) : (W3.mul a b).toE = a.toE * b.toE := by
  rw [← W3.toE_mul9]
  simp only [W3.mul, W3.mul9, W3.toE, kOf_xor, kOf_mulW]
  congr 1
  · linear_combination K.add_self (kOf a.w1 * kOf b.w1) + K.add_self (kOf a.w2 * kOf b.w2)
  · linear_combination K.add_self (kOf a.w0 * kOf b.w0) + K.add_self (kOf a.w1 * kOf b.w1)
  · linear_combination K.add_self (kOf a.w0 * kOf b.w0)

/-- The square on words: in characteristic two `(x_0 + x_1 y + x_2 y^2)^2 = x_0^2 + x_1^2 y^2 +
x_2^2 y^4`, and `y^4 = y^2 + y`. -/
@[inline] def W3.sq (a : W3) : W3 :=
  let s2 := mulW a.w2 a.w2
  ⟨mulW a.w0 a.w0, s2, mulW a.w1 a.w1 ^^^ s2⟩

/-- **The square on words is `E`'s square.** -/
theorem W3.toE_sq (a : W3) : (W3.sq a).toE = a.toE * a.toE := by
  rw [← W3.toE_mul9]
  simp only [W3.sq, W3.mul9, W3.toE, kOf_xor, kOf_mulW]
  congr 1
  · linear_combination -K.add_self (kOf a.w1 * kOf a.w2)
  · linear_combination -K.add_self (kOf a.w0 * kOf a.w1) - K.add_self (kOf a.w1 * kOf a.w2)
  · linear_combination -K.add_self (kOf a.w0 * kOf a.w2)

/-! ## The product and the power -/

/-- `E`'s product on words. -/
def mulEW (x y : E) : E := (W3.mul (W3.ofE x) (W3.ofE y)).toE

/-- **`E`'s product compiles on words.** -/
@[csimp] theorem mulE_eq_mulEW : @mulE = @mulEW := by
  funext x y
  rw [mulE, mulEW, W3.toE_mul, W3.toE_ofE, W3.toE_ofE]

/-- `acc · a^n` on words, by squaring. -/
def W3.powAcc (a acc : W3) (n : ℕ) : W3 :=
  if h : n = 0 then acc
  else W3.powAcc (W3.sq a) (if n % 2 = 1 then W3.mul acc a else acc) (n / 2)
termination_by n
decreasing_by omega

theorem W3.toE_powAcc (a acc : W3) (n : ℕ) :
    (W3.powAcc a acc n).toE = acc.toE * a.toE ^ n := by
  induction n using Nat.strong_induction_on generalizing a acc with
  | _ n ih =>
    rw [W3.powAcc]
    split
    · subst_vars; simp
    · rename_i h
      rw [ih (n / 2) (by omega)]
      have hn : n = 2 * (n / 2) + n % 2 := (Nat.div_add_mod n 2).symm
      split
      · rename_i h1
        rw [W3.toE_sq, W3.toE_mul]
        conv_rhs => rw [hn, h1, pow_add, pow_mul]
        ring
      · rename_i h1
        have h0 : n % 2 = 0 := by omega
        rw [W3.toE_sq]
        conv_rhs => rw [hn, h0, Nat.add_zero, pow_mul]
        ring

/-- The one of `E` on words. -/
def W3.one : W3 := ⟨1, 0, 0⟩

theorem W3.toE_one : W3.one.toE = 1 := by
  apply Ext.ext
  intro i
  fin_cases i <;> rfl

/-- A power in `E` on words. -/
def powEW (x : E) (n : ℕ) : E := (W3.powAcc (W3.ofE x) W3.one n).toE

/-- **A power in `E` compiles on words.** -/
@[csimp] theorem powE_eq_powEW : @powE = @powEW := by
  funext x n
  rw [powE, powEW, W3.toE_powAcc, W3.toE_one, W3.toE_ofE, one_mul]

end LeanVM.Prover.Fast
