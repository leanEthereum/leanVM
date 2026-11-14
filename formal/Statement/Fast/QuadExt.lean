/-
  Statement.Fast.QuadExt

  The product of CompPoly's extension fields of degree two, unrolled: the four coefficient
  products and the reduced monomial, proved equal to `Ext.mul` and swapped in for compilation
  together with the instances that use it. Candidate for CompPoly.

  Speed only: `@[csimp]` lemmas, each proved, that change how the statement's definitions are
  compiled and nothing they mean. Not part of what a reviewer of `Statement/` must read.
-/

module

public import CompPoly.Fields.Extension

/-!
# Degree-two extensions, unrolled

`Ext.mul` compiles to `Ext.mulTbl`: the `2d - 1` convolution coefficients and their contraction
against the table of reduced monomials, each a loop over a closure. At `d = 2` this module
computes the same product directly (`mulQuad`): the coefficients
`c_k = Σ_{i + j = k} x_i y_j` of the unreduced product, of which `c_0, c_1` stand and `c_2`
enters through the reduced monomial `X^2 mod f` (`mul_eq_mulQuad`). `mulFast` takes it at
`d = 2` and `Ext.mul` otherwise; `addFast` adds the two coefficients directly at `d = 2`.

The `@[csimp]` lemmas swap the instances `Ext.instMul`, `Ext.instAdd`, `Ext.instPowNat`,
`Ext.instInv` and `Ext.instDiv` for restatements compiled here, the last three word for word
(`rfl`), so that their products are `mulFast`. Nothing here transcribes a source.

This is a candidate for CompPoly, in `Statement/Fast/` for the reason given in
`Statement.Fast.FieldWords`.
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

/-- The product at `d = 2`: `x_0, x_1` times `y_0, y_1`, the coefficient of `X^2` reduced by
`monomialMod`. -/
@[specialize P]
def mulQuad (h : P.d = 2) (x y : Ext P) : Ext P :=
  let x0 := coeffNat x 0
  let x1 := coeffNat x 1
  let y0 := coeffNat y 0
  let y1 := coeffNat y 1
  let c2 := x1 * y1
  let t2 : Ext P := monomialMod 2
  ofVector ⟨#[x0 * y0 + c2 * coeffNat t2 0, x0 * y1 + x1 * y0 + c2 * coeffNat t2 1], by simp [h]⟩

/-- **`mulQuad` is the product.** -/
theorem mul_eq_mulQuad (h : P.d = 2) (x y : Ext P) : mul x y = mulQuad h x y := by
  apply Ext.ext
  rintro ⟨m, hm⟩
  have hm2 : m < 2 := h ▸ hm
  have he : ∀ k, k < 2 → coeffNat (monomialMod k : Ext P) m = if k = m then 1 else 0 :=
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
  rw [he 0 (by omega), he 1 (by omega)]
  interval_cases m <;> simp [mulQuad, coeffNat, h, coeff, ofVector, add_assoc]

/-- The product, unrolled at `d = 2`. Specialised at the modulus, so that at a constant modulus
the reduced monomial is a constant, computed once. -/
@[specialize P]
def mulFast (x y : Ext P) : Ext P := if h : P.d = 2 then mulQuad h x y else mul x y

/-- `mulFast` is the product. -/
theorem mul_eq_mulFast : @mul F _ P = mulFast := by
  funext x y
  unfold mulFast
  split
  · exact mul_eq_mulQuad _ x y
  · rfl

/-! ## The sum -/

/-- The sum, unrolled at `d = 2`. -/
def addFast (x y : Ext P) : Ext P :=
  if h : P.d = 2 then
    ofVector ⟨#[coeffNat x 0 + coeffNat y 0, coeffNat x 1 + coeffNat y 1], by simp [h]⟩
  else x + y

/-- `addFast` is the sum. -/
theorem add_eq_addFast (x y : Ext P) : x + y = addFast x y := by
  unfold addFast
  split
  · rename_i h
    apply Ext.ext
    intro m
    obtain ⟨m, hm⟩ := m
    have hm2 : m < 2 := h ▸ hm
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

/-! ## The ring and the field, compiled with the unrolled operations

CompPoly's `Ext.instAddCommGroup`, `Ext.instCommRing` and `Ext.instField` were compiled before
the lemmas above existed: code generic in a ring or a field (a sum, a power through `Monoid.npow`,
an inverse through `Field`) multiplies through them by the table-driven `Ext.mulTbl`. Each is
restated here, its sum, product, power and inverse the restated ones, and the lemma equating
them, by `rfl`, compiles the CompPoly one as the restatement. -/

section Instances

variable {F : Type*} [Field F] {P : ExtensionParams F}

@[expose] public section

/-- `Ext.instAddCommGroup`, restated: its sum is `Ext.instAdd`. -/
@[instance_reducible] def instAddCommGroupFast : AddCommGroup (Ext P) :=
  { instAddCommGroup with toAdd := instAdd }

/-- `Ext.instAddCommGroup` compiles as its restatement. -/
@[csimp] theorem instAddCommGroup_eq_instAddCommGroupFast :
    @instAddCommGroup = @instAddCommGroupFast := rfl

/-- `Ext.instCommRing`, restated: its sum, product and power are `Ext.instAdd`, `Ext.instMul`
and `Ext.instPowNat`. -/
@[instance_reducible] def instCommRingFast : CommRing (Ext P) :=
  { instCommRing with toAdd := instAdd, toMul := instMul, npow := fun n x ↦ x ^ n }

/-- `Ext.instCommRing` compiles as its restatement. -/
@[csimp] theorem instCommRing_eq_instCommRingFast : @instCommRing = @instCommRingFast := rfl

section Irreducible

variable [Finite F] [Fact (Nat.card F = P.q)] [Fact (Irreducible P.poly)]

/-- `Ext.instField`, restated: its ring is `Ext.instCommRing` and its inverse and quotient
`Ext.instInv`'s and `Ext.instDiv`'s. -/
@[instance_reducible] def instFieldFast : Field (Ext P) :=
  { instField with
    toCommRing := instCommRing
    inv := fun x ↦ x⁻¹
    div := fun x y ↦ x / y }

/-- `Ext.instField` compiles as its restatement. -/
@[csimp] theorem instField_eq_instFieldFast : @instField = @instFieldFast := rfl

end Irreducible

end

end Instances

end CompPoly.Extension.Ext
