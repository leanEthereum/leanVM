/-
  LeanVM.Spec.Fast.CubicExt

  The product of CompPoly's extension fields of degree three, unrolled: the nine coefficient
  products and the two reduced monomials, proved equal to `Ext.mul` and swapped in for
  compilation together with the instances that use it. Candidate for CompPoly.
-/

module

public import CompPoly.Fields.Extension

/-!
# Degree-three extensions, unrolled

`Ext.mul` compiles to `Ext.mulTbl`: the `2d - 1` convolution coefficients and their contraction
against the table of reduced monomials, each a loop over a closure. At `d = 3` this module
computes the same product directly (`mulCubic`): the coefficients
`c_k = Σ_{i + j = k} x_i y_j` of the unreduced product, of which `c_0, c_1, c_2` stand and
`c_3, c_4` enter through the reduced monomials `X^3 mod f`, `X^4 mod f`
(`mul_eq_mulCubic`). `mulFast` takes it at `d = 3` and `Ext.mul` otherwise; `addFast` adds the
three coefficients directly at `d = 3`.

The `@[csimp]` lemmas swap the instances `Ext.instMul`, `Ext.instAdd`, `Ext.instPowNat`,
`Ext.instInv` and `Ext.instDiv` for restatements compiled here, the last three word for word
(`rfl`), so that their products are `mulFast`. Nothing here transcribes a source.

This is a candidate for CompPoly, in `Parameters` for the reason given in
`LeanVM.Spec.Fast.FieldWords`.
-/

namespace CompPoly.Extension.Ext

@[expose] public section

variable {F : Type*} [Ring F] {P : ExtensionParams F}

/-! ## The reduced monomials below the degree -/

/-- `X^(k + 1) mod f` is `X · (X^k mod f)`, reduced. -/
theorem monomialMod_succ' (k : ℕ) :
    (monomialMod (k + 1) : Ext P) = shiftReduce (monomialMod k) := by
  rw [monomialMod, monomialMod, Function.iterate_succ_apply']

/-- Below the degree, `X^k mod f` is `X^k`. -/
theorem coeffNat_monomialMod_of_lt {k m : ℕ} (hk : k < P.d) (hm : m < P.d) :
    coeffNat (monomialMod k : Ext P) m = if k = m then 1 else 0 := by
  induction k generalizing m with
  | zero =>
    rw [coeffNat_of_lt _ hm, show (monomialMod 0 : Ext P) = 1 from rfl, coeff_one]
    simp [eq_comm]
  | succ k ih =>
    rw [monomialMod_succ', coeffNat_of_lt _ hm, coeff_shiftReduce,
      ih (by omega) (show P.d - 1 < P.d by omega), ite_eq_right (show k ≠ P.d - 1 by omega),
      zero_mul, sub_zero]
    by_cases h1 : m = 0
    · simp [h1]
    · simp only [h1, ↓reduceIte]
      rw [ih (by omega) (by omega)]
      by_cases h2 : k + 1 = m
      · rw [ite_eq_left (show k = m - 1 by omega), ite_eq_left h2]
      · simp [h2, show k ≠ m - 1 by omega]

/-! ## The product -/

/-- The product at `d = 3`: `x_0, x_1, x_2` times `y_0, y_1, y_2`, the coefficients of `X^3` and
`X^4` reduced by `monomialMod`. -/
@[specialize P]
def mulCubic (h : P.d = 3) (x y : Ext P) : Ext P :=
  let x0 := coeffNat x 0
  let x1 := coeffNat x 1
  let x2 := coeffNat x 2
  let y0 := coeffNat y 0
  let y1 := coeffNat y 1
  let y2 := coeffNat y 2
  let c3 := x1 * y2 + x2 * y1
  let c4 := x2 * y2
  let t3 : Ext P := monomialMod 3
  let t4 : Ext P := monomialMod 4
  ofVector ⟨#[x0 * y0 + c3 * coeffNat t3 0 + c4 * coeffNat t4 0,
      x0 * y1 + x1 * y0 + c3 * coeffNat t3 1 + c4 * coeffNat t4 1,
      x0 * y2 + x1 * y1 + x2 * y0 + c3 * coeffNat t3 2 + c4 * coeffNat t4 2], by simp [h]⟩

/-- **`mulCubic` is the product.** -/
theorem mul_eq_mulCubic (h : P.d = 3) (x y : Ext P) : mul x y = mulCubic h x y := by
  apply Ext.ext
  rintro ⟨m, hm⟩
  have hm3 : m < 3 := h ▸ hm
  have he : ∀ k, k < 3 → coeffNat (monomialMod k : Ext P) m = if k = m then 1 else 0 :=
    fun k hk ↦ coeffNat_monomialMod_of_lt (by omega) hm
  have hsum : coeffNat (mul x y) m = ∑ i ∈ Finset.range P.d, ∑ j ∈ Finset.range P.d,
      coeffNat x i * coeffNat y j * coeffNat (monomialMod (i + j) : Ext P) m := by
    rw [coeffNat_of_lt _ hm, show mul x y = x * y from rfl, coeff_mul,
      ← Fin.sum_univ_eq_sum_range (fun i ↦ ∑ j ∈ Finset.range P.d,
        coeffNat x i * coeffNat y j * coeffNat (monomialMod (i + j) : Ext P) m)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Fin.sum_univ_eq_sum_range (fun j ↦
        coeffNat x i * coeffNat y j * coeffNat (monomialMod (i + j) : Ext P) m)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [coeffNat_coe, coeffNat_coe, coeffNat_of_lt _ hm]
  rw [← coeffNat_of_lt _ hm, ← coeffNat_of_lt _ hm, hsum, h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.reduceAdd]
  rw [he 0 (by omega), he 1 (by omega), he 2 (by omega)]
  interval_cases m <;>
    simp [mulCubic, coeffNat, h, coeff, ofVector, add_mul] <;> abel

/-- The product, unrolled at `d = 3`. Specialised at the modulus, so that at a constant modulus
the reduced monomials are constants, computed once. -/
@[specialize P]
def mulFast (x y : Ext P) : Ext P := if h : P.d = 3 then mulCubic h x y else mul x y

/-- `mulFast` is the product. -/
theorem mul_eq_mulFast : @mul F _ P = mulFast := by
  funext x y
  unfold mulFast
  split
  · exact mul_eq_mulCubic _ x y
  · rfl

/-! ## The sum -/

/-- The sum, unrolled at `d = 3`. -/
def addFast (x y : Ext P) : Ext P :=
  if h : P.d = 3 then
    ofVector ⟨#[coeffNat x 0 + coeffNat y 0, coeffNat x 1 + coeffNat y 1,
      coeffNat x 2 + coeffNat y 2], by simp [h]⟩
  else x + y

/-- `addFast` is the sum. -/
theorem add_eq_addFast (x y : Ext P) : x + y = addFast x y := by
  unfold addFast
  split
  · rename_i h
    apply Ext.ext
    intro m
    obtain ⟨m, hm⟩ := m
    have hm3 : m < 3 := h ▸ hm
    rw [coeff_add]
    interval_cases m <;> simp [coeffNat, h, coeff, ofVector]
  · rfl

/-! ## The instances, compiled with the unrolled operations -/

/-- `Ext.instMul`, compiled as `mulFast`. -/
@[instance_reducible] def instMulFast : Mul (Ext P) := ⟨mulFast⟩

/-- `Ext.instMul` compiles as `instMulFast`. -/
@[csimp] theorem instMul_eq_instMulFast : @instMul = @instMulFast := by
  funext F _ P
  simp only [instMul, instMulFast, mul_eq_mulFast]

/-- `Ext.instAdd`, compiled as `addFast`. -/
@[instance_reducible] def instAddFast : Add (Ext P) := ⟨addFast⟩

/-- `Ext.instAdd` compiles as `instAddFast`. -/
@[csimp] theorem instAdd_eq_instAddFast : @instAdd = @instAddFast := by
  funext F _ P
  have : (fun x y : Ext P ↦ x + y) = addFast := funext fun x ↦ funext (add_eq_addFast x)
  simp only [instAddFast, ← this]
  rfl

/-- `Ext.instPowNat`, restated. -/
@[instance_reducible] def instPowNatFast : Pow (Ext P) ℕ := ⟨fun x n ↦ npowBinRec n x⟩

/-- `Ext.instPowNat` compiles as its restatement. -/
@[csimp] theorem instPowNat_eq_instPowNatFast : @instPowNat = @instPowNatFast := rfl

/-- `Ext.instInv`, restated. -/
@[instance_reducible] def instInvFast : Inv (Ext P) := ⟨fun x ↦ x ^ (P.q ^ P.d - 2)⟩

/-- `Ext.instInv` compiles as its restatement. -/
@[csimp] theorem instInv_eq_instInvFast : @instInv = @instInvFast := rfl

/-- `Ext.instDiv`, restated. -/
@[instance_reducible] def instDivFast : Div (Ext P) := ⟨fun x y ↦ x * y.inv⟩

/-- `Ext.instDiv` compiles as its restatement. -/
@[csimp] theorem instDiv_eq_instDivFast : @instDiv = @instDivFast := rfl

end

end CompPoly.Extension.Ext
