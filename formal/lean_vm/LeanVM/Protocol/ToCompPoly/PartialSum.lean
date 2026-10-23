/-
  LeanVM.Protocol.ToCompPoly.PartialSum

  The eq-weighted sum of a function over the cube with its first coordinates fixed: the running
  claim of a sumcheck that binds the lowest variable first. Candidate for CompPoly.
-/

module

public import LeanVM.Protocol.ToCompPoly.Multilinear

/-!
# Partial sums over the cube

For a function `g` on `m` coordinates, a point `r`, and the first `j` coordinates fixed to `c`,
`partialSum g r j c` is `Σ_{x ∈ {0,1}^(m - j)} eq(r_{≥ j}, x) · g(c, x)`: the extension, at the
remaining coordinates of `r`, of the table of `g` on the cube of the remaining coordinates
(`restrictTable`). It is the claim a sumcheck on `Σ_x eq(r, x) g(x)` carries after `j` rounds
when the rounds bind the lowest variable first:

* `partialSum_zero`: with nothing fixed it is the extension of the table of `g` at `r`;
* `partialSum_split`: fixing one more coordinate splits it into the two values at `0` and at `1`,
  weighted by `1 - r_j` and `r_j`;
* `partialSum_self`: with everything fixed it is `g c`.

Over an arbitrary commutative ring. Candidate for CompPoly, beside `CompPoly.Multilinear.Basic`.
Nothing here transcribes a source.
-/

namespace LeanVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {R : Type*} [CommRing R]

/-- The point `(c, x)` on `m` coordinates. -/
def fixLow {m j : ℕ} (hj : j ≤ m) (c : Vector R j) (x : Vector R (m - j)) : Vector R m :=
  Vector.cast (Nat.add_sub_cancel' hj) (c ++ x)

/-- The table of `g` on the cube of the last `m - j` coordinates, the first `j` fixed to `c`. -/
def restrictTable {m : ℕ} (g : Vector R m → R) {j : ℕ} (hj : j ≤ m) (c : Vector R j) :
    CMlPolynomialEval R (m - j) :=
  Vector.ofFn fun x ↦ g (fixLow hj c (boolVec x))

/-- The eq-weighted partial sum `Σ_x eq(r_{≥ j}, x) · g(c, x)`; zero when more than `m`
coordinates are fixed. -/
def partialSum {m : ℕ} (g : Vector R m → R) (r : Vector R m) (j : ℕ) (c : Vector R j) : R :=
  if hj : j ≤ m then evalMle (restrictTable g hj c) (r.drop j) else 0

/-! ## Nothing fixed -/

omit [CommRing R] in
private theorem fixLow_zero {m : ℕ} (x : Vector R (m - 0)) :
    fixLow (Nat.zero_le m) (#v[] : Vector R 0) x = x := by
  apply Vector.ext
  intro i hi
  simp [fixLow]

omit [CommRing R] in
private theorem drop_zero {m : ℕ} (r : Vector R m) : r.drop 0 = r := by
  apply Vector.ext
  intro i hi
  simp

/-- With nothing fixed, the partial sum is the extension of the table of `g` at `r`. -/
theorem partialSum_zero {m : ℕ} (g : Vector R m → R) (r : Vector R m) :
    partialSum g r 0 #v[] = evalMle (Vector.ofFn fun x ↦ g (boolVec x)) r := by
  rw [partialSum, dite_eq_left (Nat.zero_le m), drop_zero]
  congr 1
  apply Vector.ext
  intro i hi
  simp only [restrictTable, Vector.getElem_ofFn]
  rw [fixLow_zero]

/-! ## Everything fixed -/

omit [CommRing R] in
private theorem fixLow_self {m : ℕ} (c : Vector R m) (x : Vector R (m - m)) :
    fixLow le_rfl c x = c := by
  apply Vector.ext
  intro i hi
  simp [fixLow, hi]

/-- With everything fixed, the partial sum is the value at the fixed point. -/
theorem partialSum_self {m : ℕ} (g : Vector R m → R) (r : Vector R m) (c : Vector R m) :
    partialSum g r m c = g c := by
  rw [partialSum, dite_eq_left le_rfl, evalMle_eq_sum]
  have hone : 2 ^ (m - m) = 1 := by simp
  have : Unique (Fin (2 ^ (m - m))) :=
    ⟨⟨⟨0, by omega⟩⟩, fun x ↦ Fin.ext (by have := x.isLt; omega)⟩
  rw [Fintype.sum_unique]
  simp only [restrictTable, Fin.getElem_fin, Vector.getElem_ofFn, fixLow_self,
    lagrangeBasis_getElem_nat _ (Fin.isLt _)]
  rw [Finset.prod_eq_one fun b _ ↦ absurd b.isLt (by simp), mul_one]

/-! ## One more coordinate -/

/-- Extending `c` by `0` and then by `x'` is extending `c` by the point `2x'`. -/
private theorem fixLow_push_zero {m j : ℕ} (hj : j < m) (c : Vector R j)
    (x' : Fin (2 ^ (m - (j + 1))))
    (hb : 2 * x'.val < 2 ^ (m - j)) :
    fixLow hj (c.push 0) (boolVec x') =
      fixLow hj.le c (boolVec (⟨2 * x'.val, hb⟩ : Fin (2 ^ (m - j)))) := by
  apply Vector.ext
  intro i hi
  simp only [fixLow, Vector.getElem_cast, Vector.getElem_append, Vector.getElem_push, boolVec,
    Vector.getElem_ofFn]
  by_cases h1 : i < j
  · simp [h1, show i < j + 1 by omega]
  · by_cases h2 : i < j + 1
    · have hij : i = j := by omega
      subst hij
      simp [Nat.testBit_zero]
    · have hs : i - j = (i - (j + 1)) + 1 := by omega
      simp only [h1, h2, dite_false, hs, Nat.testBit_succ, Nat.mul_div_cancel_left _ two_pos]

/-- Extending `c` by `1` and then by `x'` is extending `c` by the point `2x' + 1`. -/
private theorem fixLow_push_one {m j : ℕ} (hj : j < m) (c : Vector R j)
    (x' : Fin (2 ^ (m - (j + 1))))
    (hb : 2 * x'.val + 1 < 2 ^ (m - j)) :
    fixLow hj (c.push 1) (boolVec x') =
      fixLow hj.le c (boolVec (⟨2 * x'.val + 1, hb⟩ : Fin (2 ^ (m - j)))) := by
  apply Vector.ext
  intro i hi
  simp only [fixLow, Vector.getElem_cast, Vector.getElem_append, Vector.getElem_push, boolVec,
    Vector.getElem_ofFn]
  by_cases h1 : i < j
  · simp [h1, show i < j + 1 by omega]
  · by_cases h2 : i < j + 1
    · have hij : i = j := by omega
      subst hij
      simp [Nat.testBit_zero, Nat.add_mod]
    · have hs : i - j = (i - (j + 1)) + 1 := by omega
      simp only [h1, h2, dite_false, hs, Nat.testBit_succ,
        show (2 * x'.val + 1) / 2 = x'.val by omega]

/-- Extending `c` by `X` is extending it by `0` and then setting coordinate `j` to `X`. -/
theorem fixLow_push_set {m j : ℕ} (hj : j < m) (c : Vector R j) (x : Vector R (m - (j + 1)))
    (X : R) : fixLow hj (c.push X) x = (fixLow hj (c.push 0) x).set j X hj := by
  apply Vector.ext
  intro i hi
  simp only [fixLow, Vector.getElem_cast, Vector.getElem_append, Vector.getElem_push,
    Vector.getElem_set]
  by_cases h1 : i < j
  · simp [h1, show i < j + 1 by omega, show j ≠ i by omega]
  · by_cases h2 : i < j + 1
    · have hij : i = j := by omega
      subst hij
      simp
    · simp [h2, show j ≠ i by omega]

/-- Fixing one more coordinate: the partial sum at `j` is the interpolation, by `r_j`, of the
partial sums at `j + 1` with the coordinate fixed to `0` and to `1`. -/
theorem partialSum_split {m : ℕ} (g : Vector R m → R) (r : Vector R m) {j : ℕ} (hj : j < m)
    (c : Vector R j) :
    partialSum g r j c =
      (1 - r[j]) * partialSum g r (j + 1) (c.push 0) +
        r[j] * partialSum g r (j + 1) (c.push 1) := by
  have hm : m - j = (m - (j + 1)) + 1 := by omega
  rw [partialSum, partialSum, partialSum, dite_eq_left hj.le, dite_eq_left (Nat.succ_le_of_lt hj),
    dite_eq_left (Nat.succ_le_of_lt hj)]
  -- The remaining coordinates, with the next one split off.
  rw [← evalMle_cast hm, evalMle_succ]
  have hhead : (Vector.cast hm (r.drop j)).head = r[j] := by
    simp [Vector.head]
  have htail : (Vector.cast hm (r.drop j)).tail = r.drop (j + 1) := by
    apply Vector.ext
    intro i hi
    simp only [Vector.tail_eq_cast_extract, Vector.getElem_cast, Vector.getElem_extract,
      Vector.getElem_drop]
    exact getElem_congr_idx (by omega)
  rw [hhead, htail]
  -- The layer at `r_j` interpolates the two restricted tables.
  have hlayer : evalMleLayer (Vector.cast (congrArg (2 ^ ·) hm) (restrictTable g hj.le c)) r[j] =
      (1 - r[j]) • restrictTable g hj (c.push 0) + r[j] • restrictTable g hj (c.push 1) := by
    apply Vector.ext
    intro i hi
    rw [← Vector.get_eq_getElem _ ⟨i, hi⟩, evalMleLayer_get]
    simp only [Vector.get_eq_getElem, Vector.getElem_cast, Vector.getElem_add, Vector.getElem_smul,
      smul_eq_mul, restrictTable, Vector.getElem_ofFn]
    rw [fixLow_push_zero hj c ⟨i, hi⟩ (by rw [hm, pow_succ]; omega),
      fixLow_push_one hj c ⟨i, hi⟩ (by rw [hm, pow_succ]; omega)]
  rw [hlayer, eval_mle_eq_eval, eval_add, eval_smul, eval_smul, ← eval_mle_eq_eval,
    ← eval_mle_eq_eval]

end
end LeanVM.Protocol
