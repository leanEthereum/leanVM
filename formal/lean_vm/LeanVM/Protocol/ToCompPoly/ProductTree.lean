/-
  LeanVM.Protocol.ToCompPoly.ProductTree

  The product tree over a hypercube table: each layer multiplies adjacent entries of the layer
  below it, and the root is the product of the leaves. The layer identities a grand-product
  argument reduces along. Candidate for CompPoly.
-/

module

public import LeanVM.Protocol.ToCompPoly.Multilinear

/-!
# Product trees

The product tree of a table `t` of `2 ^ μ` leaves has, one level up, the table `contract t` of
`2 ^ (μ - 1)` entries, entry `x` being `t[2x] * t[2x + 1]`, and so on up to the root, the product
of every leaf. `layerTable t m` is the level on `m` variables, for every `m ≤ μ`: `t` itself at
`m = μ`, the root at `m = 0`. Over an arbitrary commutative ring. Candidate for CompPoly, beside
`CompPoly.Multilinear.Basic`. Nothing here transcribes a source.

Contracting `ρ` levels at once, node `x` is the product of its `2 ^ ρ` descendants
`childIndex ρ c x = c + 2 ^ ρ · x` (`contractPow_getElem`), whose Boolean points are
`childPoint ρ c (boolVec x) = (bits of c, bits of x)`: the descendants occupy the low
coordinates. The layer identity a grand-product argument runs sumcheck on,
`Ṽ_i(r) = Σ_x eq(r, x) ∏_c Ṽ_{i - ρ}(c, x)`, is `evalMle_contractPow`.

## Wrong readings excluded

* The descendants of a node are at the low bits of the index, so the point of a descendant is
  `(bits of c, x)` and not `(x, bits of c)`; a `childPoint` with the bits high evaluates a
  different node.
* `layerTable t m` for `m > μ` is a table of ones, so that the definition is total; every
  identity about it takes `m ≤ μ`.
-/

namespace LeanVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {R : Type*} [CommRing R]

/-! ## One level -/

/-- The level above a table: entry `x` is the product of entries `2x` and `2x + 1`. -/
def contract {n : ℕ} (t : CMlPolynomialEval R (n + 1)) : CMlPolynomialEval R n :=
  Vector.ofFn fun x ↦
    t[2 * x.val]'(by have := x.isLt; rw [pow_succ]; omega) *
      t[2 * x.val + 1]'(by have := x.isLt; rw [pow_succ]; omega)

/-- Entry `x` of the level above is the product of entries `2x` and `2x + 1`. -/
theorem contract_getElem {n : ℕ} (t : CMlPolynomialEval R (n + 1)) {x : ℕ} (hx : x < 2 ^ n) :
    (contract t)[x] =
      t[2 * x]'(by rw [pow_succ]; omega) * t[2 * x + 1]'(by rw [pow_succ]; omega) := by
  simp [contract]

/-! ## Several levels at once -/

/-- `ρ` levels up. -/
def contractPow : (ρ : ℕ) → {n : ℕ} → CMlPolynomialEval R (n + ρ) → CMlPolynomialEval R n
  | 0, _, t => t
  | ρ + 1, _, t => contractPow ρ (contract t)

/-- The index of descendant `c` of node `x`, `ρ` levels down: `c + 2 ^ ρ · x`. -/
def childIndex (ρ : ℕ) {n : ℕ} (c : Fin (2 ^ ρ)) (x : Fin (2 ^ n)) : Fin (2 ^ (n + ρ)) :=
  ⟨c.val + 2 ^ ρ * x.val, by
    have h := (cubeIndex c x).isLt
    rw [cubeIndex_val, pow_add] at h
    rw [pow_add, Nat.mul_comm (2 ^ n) (2 ^ ρ)]
    exact h⟩

/-- The descendant's index as a number. -/
@[simp] theorem childIndex_val (ρ : ℕ) {n : ℕ} (c : Fin (2 ^ ρ)) (x : Fin (2 ^ n)) :
    (childIndex ρ c x).val = c.val + 2 ^ ρ * x.val := rfl

/-- The point of descendant `c` of the point `y`, `ρ` levels down: the bits of `c` in the low
coordinates, `y` in the high ones. -/
def childPoint (ρ : ℕ) {n : ℕ} (c : Fin (2 ^ ρ)) (y : Vector R n) : Vector R (n + ρ) :=
  Vector.cast (Nat.add_comm ρ n) ((boolVec c : Vector R ρ) ++ y)

/-- Bit `a` of a descendant index is bit `a` of the descendant below `ρ` and bit `a - ρ` of the
node above. -/
theorem testBit_childIndex (ρ : ℕ) {n : ℕ} (c : Fin (2 ^ ρ)) (x : Fin (2 ^ n)) (a : ℕ) :
    (childIndex ρ c x).val.testBit a =
      if a < ρ then c.val.testBit a else x.val.testBit (a - ρ) := by
  rw [childIndex_val, add_comm]
  exact Nat.testBit_two_pow_mul_add x.val c.isLt a

/-- The descendant of a Boolean point is the Boolean point of the descendant index. -/
theorem childPoint_boolVec (ρ : ℕ) {n : ℕ} (c : Fin (2 ^ ρ)) (x : Fin (2 ^ n)) :
    childPoint ρ c (boolVec x : Vector R n) = boolVec (childIndex ρ c x) := by
  apply Vector.ext
  intro a ha
  rw [childPoint, Vector.getElem_cast, Vector.getElem_append]
  simp only [boolVec, Vector.getElem_ofFn, testBit_childIndex]
  by_cases h : a < ρ <;> simp [h]

/-- Evaluating at the descendant of a Boolean point reads the descendant's entry. -/
theorem evalMle_childPoint_boolVec (ρ : ℕ) {n : ℕ} (t : CMlPolynomialEval R (n + ρ))
    (c : Fin (2 ^ ρ)) (x : Fin (2 ^ n)) :
    evalMle t (childPoint ρ c (boolVec x)) = t[childIndex ρ c x] := by
  rw [childPoint_boolVec, evalMle_boolVec]

/-- Setting a coordinate of `y` sets the coordinate `ρ` further of the descendant point. -/
theorem childPoint_set (ρ : ℕ) {n : ℕ} (c : Fin (2 ^ ρ)) (y : Vector R n) {k : ℕ} (hk : k < n)
    (X : R) :
    childPoint ρ c (y.set k X hk) = (childPoint ρ c y).set (ρ + k) X (by omega) := by
  apply Vector.ext
  intro i hi
  simp only [childPoint, Vector.getElem_cast, Vector.getElem_append, Vector.getElem_set]
  by_cases h : i < ρ
  · simp [h, show ρ + k ≠ i by omega]
  · by_cases hik : ρ + k = i
    · subst hik
      simp [h]
    · simp [h, hik, show k ≠ i - ρ by omega]

/-- Evaluating at a point whose low coordinates are `u`: the extension, at `u`, of the table of
the evaluations at the descendant points of `y`. -/
theorem evalMle_cast_append (ρ : ℕ) {n : ℕ} (t : CMlPolynomialEval R (n + ρ)) (u : Vector R ρ)
    (y : Vector R n) :
    evalMle t (Vector.cast (Nat.add_comm ρ n) (u ++ y)) =
      evalMle (Vector.ofFn fun c ↦ evalMle t (childPoint ρ c y)) u := by
  have h : ρ + n = n + ρ := Nat.add_comm ρ n
  have ht : t = Vector.cast (congrArg (2 ^ ·) h) (Vector.cast (congrArg (2 ^ ·) h.symm) t) := by
    simp
  conv_lhs => rw [ht, evalMle_cast h, evalMle_split_low]
  rw [evalMle_eq_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  rw [mul_comm]
  congr 1
  rw [childPoint]
  conv_rhs => rw [ht, evalMle_cast h]

/-- A node `ρ` levels up is the product of its `2 ^ ρ` descendants. -/
theorem contractPow_getElem (ρ : ℕ) {n : ℕ} (t : CMlPolynomialEval R (n + ρ)) (x : Fin (2 ^ n)) :
    (contractPow ρ t)[x] = ∏ c : Fin (2 ^ ρ), t[childIndex ρ c x] := by
  induction ρ generalizing n with
  | zero =>
    show t[x.val] = ∏ c : Fin 1, t[(childIndex 0 c x).val]
    rw [Fin.prod_univ_one]
    exact getElem_congr_idx (by simp [childIndex_val])
  | succ ρ ih =>
    simp only [contractPow]
    rw [ih, ← (finProdFinEquiv.trans (finCongr (pow_succ 2 ρ).symm)).prod_comp,
      Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun c _ ↦ ?_
    rw [Fin.prod_univ_two]
    simp only [Fin.getElem_fin, childIndex_val, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
      finProdFinEquiv_apply_val, Fin.val_zero, Fin.val_one, contract_getElem]
    rw [getElem_congr_idx (show 2 * (c.val + 2 ^ ρ * x.val) = 0 + 2 * c.val + 2 ^ (ρ + 1) * x.val
      by ring), getElem_congr_idx (show 2 * (c.val + 2 ^ ρ * x.val) + 1 =
        1 + 2 * c.val + 2 ^ (ρ + 1) * x.val by ring)]

/-! ## The layers of a tree -/

/-- The level of the tree of `t` on `m` variables: `t` at `m = μ`, the root at `m = 0`, and a
table of ones past the leaves. -/
def layerTable : {μ : ℕ} → CMlPolynomialEval R μ → (m : ℕ) → CMlPolynomialEval R m
  | 0, t, m =>
    if h : m = 0 then Vector.cast (congrArg (2 ^ ·) h.symm) t else Vector.replicate (2 ^ m) 1
  | μ + 1, t, m =>
    if h : m = μ + 1 then Vector.cast (congrArg (2 ^ ·) h.symm) t else layerTable (contract t) m

/-- The leaves are their own level. -/
@[simp] theorem layerTable_self {μ : ℕ} (t : CMlPolynomialEval R μ) : layerTable t μ = t := by
  cases μ <;> simp [layerTable]

/-- Each level is the contraction of the one below. -/
theorem layerTable_contract {μ : ℕ} (t : CMlPolynomialEval R μ) {m : ℕ} (h : m + 1 ≤ μ) :
    layerTable t m = contract (layerTable t (m + 1)) := by
  induction μ generalizing m with
  | zero => omega
  | succ μ ih =>
    have hm : m ≠ μ + 1 := by omega
    rw [layerTable, dite_eq_right hm]
    by_cases hm1 : m + 1 = μ + 1
    · have hmμ : m = μ := by omega
      subst hmμ
      rw [layerTable, dite_eq_left rfl, Vector.cast_rfl, layerTable_self]
    · rw [layerTable, dite_eq_right hm1, ih (contract t) (by omega)]

/-- A level is `ρ` contractions of the level `ρ` below. -/
theorem layerTable_contractPow {μ : ℕ} (t : CMlPolynomialEval R μ) (ρ : ℕ) {m : ℕ}
    (h : m + ρ ≤ μ) : layerTable t m = contractPow ρ (layerTable t (m + ρ)) := by
  induction ρ generalizing m with
  | zero => rfl
  | succ ρ ih =>
    show layerTable t m = contractPow ρ (contract (layerTable t (m + ρ + 1)))
    rw [← layerTable_contract t (by omega)]
    exact ih (by omega)

/-- The level of the leaves, reached at any number equal to `μ`. -/
theorem layerTable_of_eq {μ : ℕ} (t : CMlPolynomialEval R μ) {m : ℕ} (h : m = μ) :
    layerTable t m = Vector.cast (congrArg (2 ^ ·) h.symm) t := by
  subst h
  simp

/-- The root: the product of every leaf. -/
theorem layerTable_zero_getElem {μ : ℕ} (t : CMlPolynomialEval R μ) :
    (layerTable t 0)[0] = ∏ i : Fin (2 ^ μ), t[i] := by
  rw [layerTable_contractPow t μ (by omega), layerTable_of_eq t (Nat.zero_add μ)]
  rw [show (contractPow μ (Vector.cast (congrArg (2 ^ ·) (Nat.zero_add μ).symm) t))[0] =
      (contractPow μ (Vector.cast (congrArg (2 ^ ·) (Nat.zero_add μ).symm) t))[
        (⟨0, Nat.two_pow_pos 0⟩ : Fin (2 ^ 0))] from rfl, contractPow_getElem]
  refine Finset.prod_congr rfl fun c _ ↦ ?_
  simp only [Fin.getElem_fin, Vector.getElem_cast]
  exact getElem_congr_idx (by simp [childIndex_val])

end
end LeanVM.Protocol
