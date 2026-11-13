import Statement.Field
import Statement.Fast.QuadExt
import Mathlib.Tactic.Ring

/-!
# Products in `E` on machine words

`E`'s product compiles generically (`Statement.Fast.QuadExt`: `Ext.mulQuad`, each coefficient
product a call of `BF64.mul`), and a `K` word that is no small number is a big natural number at
run time, so every product of `K` words converts its factors to machine words and its result back,
each conversion of a big number a few allocations. Here the product of two elements of `E`
converts its four limbs once, computes three coefficient products (Karatsuba) and the reduction by
`y^2 = x·y + 1` on machine words, and converts the two limbs of the result back (`mulEW`,
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

/-! ## Pairs of words -/

/-- An element of `E` as its two limbs' machine words. -/
structure W2 where
  w0 : UInt64
  w1 : UInt64

/-- The element of `E` of two words. -/
@[inline] def W2.toE (a : W2) : E := E.ofLimbs (kOf a.w0) (kOf a.w1)

/-- The two words of an element of `E`. -/
@[inline] def W2.ofE (x : E) : W2 := ⟨wOf (x.limb 0), wOf (x.limb 1)⟩

theorem W2.toE_ofE (x : E) : (W2.ofE x).toE = x := by
  apply Ext.ext
  intro i
  fin_cases i <;> rfl

/-- `x` as a machine word. -/
def gW : UInt64 := 2

theorem kOf_gW : kOf gW = g := rfl

/-- The product on words: the four coefficient products, then `y^2 = x·y + 1`. -/
@[inline] def W2.mul4 (a b : W2) : W2 :=
  let c2 := mulW a.w1 b.w1
  ⟨mulW a.w0 b.w0 ^^^ c2, mulW a.w0 b.w1 ^^^ mulW a.w1 b.w0 ^^^ mulW gW c2⟩

/-- The reduced monomial of `E`: `y^2 = 1 + x·y`. -/
theorem monomialMod_two_coeff :
    Ext.coeffNat (Ext.monomialMod 2 : E) 0 = 1 ∧ Ext.coeffNat (Ext.monomialMod 2 : E) 1 = g := by
  decide +kernel

/-- **The schoolbook product on words is `E`'s product.** -/
theorem W2.toE_mul4 (a b : W2) : (W2.mul4 a b).toE = a.toE * b.toE := by
  obtain ⟨t0, t1⟩ := monomialMod_two_coeff
  rw [show a.toE * b.toE = Ext.mul a.toE b.toE from rfl, Ext.mul_eq_mulQuad (h := rfl)]
  apply Ext.ext
  rintro ⟨m, hm⟩
  have hm2 : m < 2 := hm
  interval_cases m
  · show kOf (mulW a.w0 b.w0 ^^^ mulW a.w1 b.w1) =
      kOf a.w0 * kOf b.w0 + kOf a.w1 * kOf b.w1 * Ext.coeffNat (Ext.monomialMod 2 : E) 0
    rw [t0]; simp only [kOf_xor, kOf_mulW]; ring
  · show kOf (mulW a.w0 b.w1 ^^^ mulW a.w1 b.w0 ^^^ mulW gW (mulW a.w1 b.w1)) =
      kOf a.w0 * kOf b.w1 + kOf a.w1 * kOf b.w0 +
        kOf a.w1 * kOf b.w1 * Ext.coeffNat (Ext.monomialMod 2 : E) 1
    rw [t1]; simp only [kOf_xor, kOf_mulW, kOf_gW]; ring

/-- In characteristic two a sum of equals vanishes. -/
theorem K.add_self (z : K) : z + z = 0 := by
  apply BF64.ext
  show z.toBitVec ^^^ z.toBitVec = 0#64
  simp

/-- The product on words by Karatsuba: three coefficient products, `p_m = (a_0 + a_1)(b_0 + b_1)`,
then the reduction. -/
@[inline] def W2.mul (a b : W2) : W2 :=
  let p00 := mulW a.w0 b.w0
  let p11 := mulW a.w1 b.w1
  let pm := mulW (a.w0 ^^^ a.w1) (b.w0 ^^^ b.w1)
  ⟨p00 ^^^ p11, pm ^^^ p00 ^^^ p11 ^^^ mulW gW p11⟩

/-- **The product on words is `E`'s product.** -/
theorem W2.toE_mul (a b : W2) : (W2.mul a b).toE = a.toE * b.toE := by
  rw [← W2.toE_mul4]
  simp only [W2.mul, W2.mul4, W2.toE, kOf_xor, kOf_mulW]
  congr 1
  linear_combination K.add_self (kOf a.w0 * kOf b.w0) + K.add_self (kOf a.w1 * kOf b.w1)

/-- The square on words: in characteristic two `(x_0 + x_1 y)^2 = x_0^2 + x_1^2 y^2`, and
`y^2 = x·y + 1`. -/
@[inline] def W2.sq (a : W2) : W2 :=
  let s1 := mulW a.w1 a.w1
  ⟨mulW a.w0 a.w0 ^^^ s1, mulW gW s1⟩

/-- **The square on words is `E`'s square.** -/
theorem W2.toE_sq (a : W2) : (W2.sq a).toE = a.toE * a.toE := by
  rw [← W2.toE_mul4]
  simp only [W2.sq, W2.mul4, W2.toE, kOf_xor, kOf_mulW]
  congr 1
  linear_combination -K.add_self (kOf a.w0 * kOf a.w1)

/-! ## The product and the power -/

/-- `E`'s product on words. -/
def mulEW (x y : E) : E := (W2.mul (W2.ofE x) (W2.ofE y)).toE

/-- **`E`'s product compiles on words.** -/
@[csimp] theorem mulE_eq_mulEW : @mulE = @mulEW := by
  funext x y
  rw [mulE, mulEW, W2.toE_mul, W2.toE_ofE, W2.toE_ofE]

/-- `acc · a^n` on words, by squaring. -/
def W2.powAcc (a acc : W2) (n : ℕ) : W2 :=
  if h : n = 0 then acc
  else W2.powAcc (W2.sq a) (if n % 2 = 1 then W2.mul acc a else acc) (n / 2)
termination_by n
decreasing_by omega

theorem W2.toE_powAcc (a acc : W2) (n : ℕ) :
    (W2.powAcc a acc n).toE = acc.toE * a.toE ^ n := by
  induction n using Nat.strong_induction_on generalizing a acc with
  | _ n ih =>
    rw [W2.powAcc]
    split
    · subst_vars; simp
    · rename_i h
      rw [ih (n / 2) (by omega)]
      have hn : n = 2 * (n / 2) + n % 2 := (Nat.div_add_mod n 2).symm
      split
      · rename_i h1
        rw [W2.toE_sq, W2.toE_mul]
        conv_rhs => rw [hn, h1, pow_add, pow_mul]
        ring
      · rename_i h1
        have h0 : n % 2 = 0 := by omega
        rw [W2.toE_sq]
        conv_rhs => rw [hn, h0, Nat.add_zero, pow_mul]
        ring

/-- The one of `E` on words. -/
def W2.one : W2 := ⟨1, 0⟩

theorem W2.toE_one : W2.one.toE = 1 := by
  apply Ext.ext
  intro i
  fin_cases i <;> rfl

/-- A power in `E` on words. -/
def powEW (x : E) (n : ℕ) : E := (W2.powAcc (W2.ofE x) W2.one n).toE

/-- **A power in `E` compiles on words.** -/
@[csimp] theorem powE_eq_powEW : @powE = @powEW := by
  funext x n
  rw [powE, powEW, W2.toE_powAcc, W2.toE_one, W2.toE_ofE, one_mul]

end LeanVM.Prover.Fast
