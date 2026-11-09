/-
  LeanVM.Protocol.ToCompPoly.Multilinear

  Algebra of hypercube tables: sums over the cube, the split of a cube into a low and a high
  block, Boolean points, and reading or placing the slice at a Boolean high index. Candidate for
  CompPoly.
-/

module

public import CompPoly.Multilinear.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Hypercube tables

Lemmas about CompPoly's value tables `CMlPolynomialEval R n` (a `Vector R (2 ^ n)`, bit `k` of the
index being coordinate `k`, low bit first) and their multilinear extension `evalMle`, over an
arbitrary commutative ring `R`. Candidate for CompPoly, beside `CompPoly.Multilinear.Basic`.
Nothing here transcribes a source.

* **Sums.** `sumCube`, `hadamard`; `evalMle_eq_sumCube_hadamard`: evaluating at `r` is summing the
  table against the Lagrange basis at `r`; `sumCube_lagrangeBasis`: the partition of unity;
  `evalMle_replicate`: a constant table extends to the constant.
* **Splitting.** `cubeIndex i j = i + 2 ^ k * j` has low bits `i` and high bits `j`;
  `sum_cube_split` turns a sum over the cube into a double sum; `lagrangeBasis_cubeIndex` factors
  the Lagrange basis across the split.
* **Boolean points.** `boolVec j` is the point of the cube with index `j`; the Lagrange basis
  there is an indicator (`lagrangeBasis_boolVec`), so evaluating reads the entry
  (`evalMle_boolVec`). `boolVec_zero` and `boolVec_onesIndex` name the two corners, and
  `lagrangeBasis_zero_index`, `lagrangeBasis_onesIndex` give the basis at them as products.
* **Slices.** `slice t j` is the subcube of `t` whose high bits are `j`, and `placeSlice t j` is
  the table that holds `t` on that subcube and zero elsewhere. `evalMle_split` writes an
  evaluation as the weighted sum of the slices; `evalMle_append_boolVec` is the selection
  identity, a Boolean high coordinate selects a slice; `evalMle_placeSlice` and
  `sumCube_placeSlice` are its converse. `sliceLow t i` is the strided subcube whose low bits
  are `i`, one entry every `2 ^ k`, and `evalMle_boolVec_append` its selection identity.
* **Low coordinates.** `lowCoords h z` is the low `k` coordinates of a point on `n ≥ k`, and
  `repeatHigh t h` reads a table on `k` variables on `n`, the same in every slice of the high
  coordinates: its extension ignores them (`evalMle_repeatHigh`).

A point is a `Vector R n`, and `z ++ s` puts `z` in the low coordinates.

Derived from Verified-zkEVM/leanth `leanth-project` at 23929f8c, by Aristotle (Harmonic),
Stefano Rocca and Elias Judin, ported to CompPoly's tables and little-endian indexing: the
partition of unity (`Polynomial/Multilinear.lean:213`, `eqTilde_sum_cube`), the collapse of a
sum onto one slice (`ProofSystem/ZeroCheck.lean:836-886`, `sum_prefix_collapse`), and the
selection identity (`ProofSystem/Stacking.lean:603`, `eval_MLE_stack_block`). The proofs are new:
they go through `eval_mle_eq_eval`, the dot product with `lagrangeBasis`, and one lemma,
`lagrangeBasis_cubeIndex`.

## Wrong readings excluded

* `evalMle_append_boolVec` reads the slice at the *high* index and `evalMle_boolVec_append`
  the slice at the *low* index; the two are different subcubes, a window of consecutive entries
  against one entry every `2 ^ k`.
* `placeSlice` puts zero in the other slices, so the cube sum is kept. Copying the table into
  every slice multiplies the sum by `2 ^ m`.
-/

namespace LeanVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {R : Type*} [CommRing R]

/-! ## Sums and products of tables -/

/-- The sum of a table over the cube. -/
def sumCube {n : ℕ} (t : CMlPolynomialEval R n) : R := ∑ i : Fin (2 ^ n), t[i]

/-- The pointwise product of two tables. -/
def hadamard {n : ℕ} (s t : CMlPolynomialEval R n) : CMlPolynomialEval R n :=
  Vector.ofFn fun i ↦ s[i] * t[i]

@[simp] theorem hadamard_getElem {n : ℕ} (s t : CMlPolynomialEval R n) (i : Fin (2 ^ n)) :
    (hadamard s t)[i] = s[i] * t[i] := by
  simp [hadamard]

/-- `lagrangeBasis_getElem` with a natural-number index. -/
theorem lagrangeBasis_getElem_nat {n : ℕ} (w : Vector R n) {a : ℕ} (ha : a < 2 ^ n) :
    (lagrangeBasis w)[a] = ∏ b : Fin n, if a.testBit b then w[b] else 1 - w[b] := by
  have h := lagrangeBasis_getElem (w := w) ⟨a, ha⟩
  simp only [Fin.getElem_fin, BitVec.getLsb_eq_getElem, BitVec.getElem_ofFin] at h
  exact h

/-- Multilinear evaluation is the dot product of the table with the Lagrange basis. -/
theorem evalMle_eq_sum {n : ℕ} (t : CMlPolynomialEval R n) (x : Vector R n) :
    evalMle t x = ∑ i : Fin (2 ^ n), t[i] * (lagrangeBasis x)[i] := by
  rw [eval_mle_eq_eval, CMlPolynomialEval.eval, Vector.dotProduct_eq_root_dotProduct]
  simp [dotProduct, Vector.get_eq_getElem]

/-- Evaluation is invariant under casting the number of variables. -/
theorem evalMle_cast {n n' : ℕ} (h : n = n') (t : CMlPolynomialEval R n) (x : Vector R n) :
    evalMle (Vector.cast (congrArg (2 ^ ·) h) t) (Vector.cast h x) = evalMle t x := by
  subst h
  simp

/-- Evaluation at a point of another ring is invariant under casting the number of variables. -/
theorem eval₂Mle_cast {S : Type*} [CommRing S] (φ : R →+* S) {n n' : ℕ} (h : n = n')
    (t : CMlPolynomialEval R n) (x : Vector S n) :
    eval₂Mle (Vector.cast (congrArg (2 ^ ·) h) t) φ (Vector.cast h x) = eval₂Mle t φ x := by
  subst h
  simp

private theorem evalMle_replicate_one {n : ℕ} (x : Vector R n) :
    evalMle (Vector.replicate (2 ^ n) (1 : R)) x = 1 := by
  induction n with
  | zero => simp [evalMle_zero]
  | succ n ih =>
    rw [evalMle_succ]
    have h : evalMleLayer (Vector.replicate (2 ^ (n + 1)) (1 : R)) x.head =
        Vector.replicate (2 ^ n) 1 := by
      apply Vector.ext
      intro j hj
      rw [← Vector.get_eq_getElem _ ⟨j, hj⟩, evalMleLayer_get]
      simp only [Vector.get_replicate, Vector.getElem_replicate]
      ring
    rw [h, ih]

/-- The Lagrange basis sums to one over the cube: the partition of unity. -/
theorem sumCube_lagrangeBasis {n : ℕ} (r : Vector R n) : sumCube (lagrangeBasis r) = 1 := by
  have h := evalMle_replicate_one r
  rw [evalMle_eq_sum] at h
  simpa [sumCube] using h

/-- A constant table extends to the constant. -/
theorem evalMle_replicate {n : ℕ} (a : R) (x : Vector R n) :
    evalMle (Vector.replicate (2 ^ n) a) x = a := by
  rw [evalMle_eq_sum]
  simp only [Fin.getElem_fin, Vector.getElem_replicate]
  rw [← Finset.mul_sum]
  have hs := sumCube_lagrangeBasis x
  simp only [sumCube, Fin.getElem_fin] at hs
  rw [hs, mul_one]

/-! ## Splitting the cube -/

/-- The index of the cube `{0,1}^(k+m)` whose low `k` bits are `i` and whose high `m` bits are
`j`. -/
def cubeIndex {k m : ℕ} (i : Fin (2 ^ k)) (j : Fin (2 ^ m)) : Fin (2 ^ (k + m)) :=
  ⟨i.val + 2 ^ k * j.val, by
    rw [pow_add]
    calc i.val + 2 ^ k * j.val < 2 ^ k + 2 ^ k * j.val := Nat.add_lt_add_right i.isLt _
      _ = 2 ^ k * (j.val + 1) := by ring
      _ ≤ 2 ^ k * 2 ^ m := Nat.mul_le_mul_left _ j.isLt⟩

@[simp] theorem cubeIndex_val {k m : ℕ} (i : Fin (2 ^ k)) (j : Fin (2 ^ m)) :
    (cubeIndex i j).val = i.val + 2 ^ k * j.val := rfl

theorem cubeIndex_div {k m : ℕ} (i : Fin (2 ^ k)) (j : Fin (2 ^ m)) :
    (cubeIndex i j).val / 2 ^ k = j.val := by
  rw [cubeIndex_val, Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt i.isLt,
    zero_add]

theorem cubeIndex_mod {k m : ℕ} (i : Fin (2 ^ k)) (j : Fin (2 ^ m)) :
    (cubeIndex i j).val % 2 ^ k = i.val := by
  rw [cubeIndex_val, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]

/-- Bit `a` of `cubeIndex i j` is bit `a` of `i` below `k` and bit `a - k` of `j` above. -/
theorem testBit_cubeIndex {k m : ℕ} (i : Fin (2 ^ k)) (j : Fin (2 ^ m)) (a : ℕ) :
    (cubeIndex i j).val.testBit a = if a < k then i.val.testBit a else j.val.testBit (a - k) := by
  rw [cubeIndex_val, add_comm]
  exact Nat.testBit_two_pow_mul_add j.val i.isLt a

/-- The split of the cube into low and high blocks, as an equivalence. -/
def cubeSplit (k m : ℕ) : Fin (2 ^ k) × Fin (2 ^ m) ≃ Fin (2 ^ (k + m)) :=
  (Equiv.prodComm _ _).trans (finProdFinEquiv.trans (finCongr (by rw [pow_add, mul_comm])))

@[simp] theorem cubeSplit_apply {k m : ℕ} (i : Fin (2 ^ k)) (j : Fin (2 ^ m)) :
    cubeSplit k m (i, j) = cubeIndex i j := by
  ext
  simp [cubeSplit, cubeIndex]

/-- A sum over the cube is a double sum over the high and the low block. -/
theorem sum_cube_split {M : Type*} [AddCommMonoid M] {k m : ℕ} (f : Fin (2 ^ (k + m)) → M) :
    ∑ x, f x = ∑ j : Fin (2 ^ m), ∑ i : Fin (2 ^ k), f (cubeIndex i j) := by
  rw [← (cubeSplit k m).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  simp

/-- The low `k` coordinates of a point. -/
def lowVec {k m : ℕ} (w : Vector R (k + m)) : Vector R k :=
  Vector.ofFn fun a ↦ w[a.val]'(by omega)

/-- The high `m` coordinates of a point. -/
def highVec {k m : ℕ} (w : Vector R (k + m)) : Vector R m :=
  Vector.ofFn fun b ↦ w[k + b.val]'(by omega)

omit [CommRing R] in
@[simp] theorem lowVec_append {k m : ℕ} (z : Vector R k) (s : Vector R m) :
    lowVec (z ++ s) = z := by
  apply Vector.ext
  intro a _
  simp [lowVec]

omit [CommRing R] in
@[simp] theorem highVec_append {k m : ℕ} (z : Vector R k) (s : Vector R m) :
    highVec (z ++ s) = s := by
  apply Vector.ext
  intro b hb
  simp [highVec, Vector.getElem_append_right]

omit [CommRing R] in
/-- A point is its low coordinates followed by its high coordinates. -/
theorem lowVec_append_highVec {k m : ℕ} (w : Vector R (k + m)) :
    lowVec w ++ highVec w = w := by
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_append]
  split
  · simp [lowVec]
  · simp only [highVec, Vector.getElem_ofFn]
    congr 1
    omega

/-- The Lagrange basis factors across the split of the index. -/
theorem lagrangeBasis_cubeIndex {k m : ℕ} (w : Vector R (k + m)) (i : Fin (2 ^ k))
    (j : Fin (2 ^ m)) :
    (lagrangeBasis w)[cubeIndex i j] =
      (lagrangeBasis (lowVec w))[i] * (lagrangeBasis (highVec w))[j] := by
  simp only [Fin.getElem_fin, lagrangeBasis_getElem_nat, testBit_cubeIndex]
  rw [Fin.prod_univ_add]
  congr 1
  · refine Finset.prod_congr rfl fun a _ ↦ ?_
    simp [lowVec, a.isLt]
  · refine Finset.prod_congr rfl fun b _ ↦ ?_
    simp [highVec]

/-! ## Boolean points -/

/-- The point of the cube with index `j`, as ring elements. -/
def boolVec {m : ℕ} (j : Fin (2 ^ m)) : Vector R m :=
  Vector.ofFn fun b ↦ if j.val.testBit b then 1 else 0

/-- The index of a cube point, read bit by bit: coordinate `b` is bit `b`, and a coordinate
that is not `1` reads as `0`. The inverse of `boolVec` on the cube (`boolIndex_boolVec`). -/
def boolIndex [DecidableEq R] : {m : ℕ} → Vector R m → Fin (2 ^ m)
  | 0, _ => 0
  | m + 1, p => ⟨(if p[0] = 1 then 1 else 0) + 2 * (boolIndex p.tail).val, by
      have := (boolIndex p.tail).isLt
      simp only [Nat.add_sub_cancel] at this
      rw [pow_succ]
      split <;> omega⟩

/-- The all-ones index of the cube `{0,1}^m`. -/
def onesIndex (m : ℕ) : Fin (2 ^ m) :=
  ⟨(2 ^ m - 1 : ℕ), by have := Nat.two_pow_pos m; omega⟩

/-- The point of index zero is the origin. -/
theorem boolVec_zero {m : ℕ} :
    (boolVec (⟨0, Nat.two_pow_pos m⟩ : Fin (2 ^ m)) : Vector R m) = Vector.replicate m 0 := by
  apply Vector.ext
  intro b hb
  simp [boolVec]

/-- The tail of a cube point is the cube point of the index halved. -/
theorem boolVec_tail {m : ℕ} (j : Fin (2 ^ (m + 1))) :
    (boolVec j : Vector R (m + 1)).tail =
      boolVec (⟨j.val / 2, Nat.div_lt_of_lt_mul (by rw [← pow_succ']; exact j.isLt)⟩ :
        Fin (2 ^ m)) := by
  apply Vector.ext
  intro i hi
  simp only [boolVec, Vector.getElem_tail, Vector.getElem_ofFn, Nat.testBit_add_one]

/-- On the cube, the decoder inverts the encoder. -/
theorem boolIndex_boolVec [DecidableEq R] [Nontrivial R] :
    {m : ℕ} → (j : Fin (2 ^ m)) → boolIndex (boolVec j : Vector R m) = j
  | 0, j => by
    apply Fin.ext
    have hj : j.val = 0 := Nat.lt_one_iff.mp (by simp)
    simp only [boolIndex, Fin.val_zero, hj]
  | m + 1, j => by
    apply Fin.ext
    simp only [boolIndex, boolVec_tail, boolIndex_boolVec (m := m)]
    have h0 : (boolVec j : Vector R (m + 1))[0] = if j.val % 2 = 1 then 1 else 0 := by
      simp [boolVec, Nat.testBit_zero]
    rw [h0]
    have h := Nat.mod_add_div j.val 2
    by_cases hj : j.val % 2 = 1
    · rw [ite_eq_left hj, ite_eq_left rfl]
      omega
    · rw [ite_eq_right hj, ite_eq_right zero_ne_one]
      omega

/-- The decoder commutes with casting the number of variables. -/
theorem boolIndex_cast [DecidableEq R] {m m' : ℕ} (h : m = m') (p : Vector R m) :
    boolIndex (Vector.cast h p) = Fin.cast (congrArg (2 ^ ·) h) (boolIndex p) := by
  subst h
  rfl

/-- Casting the number of variables of a cube point casts its index. -/
theorem boolVec_cast {m m' : ℕ} (h : m = m') (j : Fin (2 ^ m)) :
    Vector.cast h (boolVec j : Vector R m) = boolVec (Fin.cast (congrArg (2 ^ ·) h) j) := by
  subst h
  rfl

/-- Two cube points side by side are the cube point of the combined index. -/
theorem boolVec_append {k m : ℕ} (i : Fin (2 ^ k)) (j : Fin (2 ^ m)) :
    (boolVec i : Vector R k) ++ (boolVec j : Vector R m) = boolVec (cubeIndex i j) := by
  apply Vector.ext
  intro a ha
  simp only [boolVec, Vector.getElem_append, Vector.getElem_ofFn, testBit_cubeIndex]
  split <;> rfl

/-- Two indices below `2 ^ m` agree iff their `m` low bits agree. -/
theorem fin_eq_iff_testBit {m : ℕ} (i j : Fin (2 ^ m)) :
    i = j ↔ ∀ b : Fin m, i.val.testBit b = j.val.testBit b := by
  refine ⟨fun h b ↦ by rw [h], fun h ↦ Fin.ext (Nat.eq_of_testBit_eq fun b ↦ ?_)⟩
  by_cases hb : b < m
  · exact h ⟨b, hb⟩
  · have hi : i.val < 2 ^ b :=
      lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hj : j.val < 2 ^ b :=
      lt_of_lt_of_le j.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.testBit_lt_two_pow hi, Nat.testBit_lt_two_pow hj]

/-- The Lagrange basis at a Boolean point is the indicator of that point. -/
theorem lagrangeBasis_boolVec {m : ℕ} (j i : Fin (2 ^ m)) :
    (lagrangeBasis (boolVec j : Vector R m))[i.val] = if i = j then 1 else 0 := by
  rw [lagrangeBasis_getElem_nat _ i.isLt]
  have h : ∀ b : Fin m,
      (if i.val.testBit b then (boolVec j : Vector R m)[b]
        else 1 - (boolVec j : Vector R m)[b]) =
      if i.val.testBit b = j.val.testBit b then 1 else 0 := by
    intro b
    simp only [boolVec, Fin.getElem_fin, Vector.getElem_ofFn]
    cases i.val.testBit b <;> cases j.val.testBit b <;> simp
  simp only [h, Fintype.prod_boole]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, (fin_eq_iff_testBit i j).not.mp hij]

/-- Evaluating a table at a point of the cube reads the entry. -/
theorem evalMle_boolVec {m : ℕ} (t : CMlPolynomialEval R m) (j : Fin (2 ^ m)) :
    evalMle t (boolVec j) = t[j] := by
  rw [evalMle_eq_sum]
  simp only [Fin.getElem_fin, lagrangeBasis_boolVec, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-! ## Slices: reading and placing a subcube -/

/-- The slice of a table at the high index `j`: the entries whose high `m` bits are `j`. -/
def slice {k m : ℕ} (t : CMlPolynomialEval R (k + m)) (j : Fin (2 ^ m)) :
    CMlPolynomialEval R k :=
  Vector.ofFn fun i ↦ t[cubeIndex i j]

omit [CommRing R] in
theorem slice_getElem {k m : ℕ} (t : CMlPolynomialEval R (k + m)) (j : Fin (2 ^ m))
    (i : Fin (2 ^ k)) : (slice t j)[i] = t[cubeIndex i j] := by
  simp [slice]

/-- The bound of `cubeIndex`, on natural numbers. -/
theorem cubeIndex_lt {k m : ℕ} {i : ℕ} (hi : i < 2 ^ k) (j : Fin (2 ^ m)) :
    i + 2 ^ k * j.val < 2 ^ (k + m) :=
  (cubeIndex ⟨i, hi⟩ j).isLt

omit [CommRing R] in
/-- `slice_getElem` with a natural-number index. -/
theorem slice_getElem_nat {k m : ℕ} (t : CMlPolynomialEval R (k + m)) (j : Fin (2 ^ m)) {i : ℕ}
    (hi : i < 2 ^ k) :
    (slice t j)[i] = t[i + 2 ^ k * j.val]'(cubeIndex_lt hi j) := by
  rw [slice, Vector.getElem_ofFn]
  rfl

/-- Mapping the entries commutes with taking a slice. -/
theorem slice_map {S : Type*} [CommRing S] (φ : R →+* S) {k m : ℕ}
    (t : CMlPolynomialEval R (k + m)) (j : Fin (2 ^ m)) :
    CMlPolynomialEval.map φ (slice t j) = slice (CMlPolynomialEval.map φ t) j := by
  apply Vector.ext
  intro i hi
  simp [slice, CMlPolynomialEval.map]

/-- Evaluation at a split point is the sum of the slices' evaluations, each weighted by the
Lagrange basis of the high coordinates. -/
theorem evalMle_split {k m : ℕ} (t : CMlPolynomialEval R (k + m)) (z : Vector R k)
    (s : Vector R m) :
    evalMle t (z ++ s) = ∑ j : Fin (2 ^ m), (lagrangeBasis s)[j] * evalMle (slice t j) z := by
  rw [evalMle_eq_sum, sum_cube_split]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [evalMle_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [lagrangeBasis_cubeIndex, lowVec_append, highVec_append, slice_getElem]
  ring

/-- The selection identity: a Boolean high coordinate selects the slice at that index. -/
theorem evalMle_append_boolVec {k m : ℕ} (t : CMlPolynomialEval R (k + m)) (z : Vector R k)
    (j : Fin (2 ^ m)) :
    evalMle t (z ++ (boolVec j : Vector R m)) = evalMle (slice t j) z := by
  rw [evalMle_split]
  simp only [Fin.getElem_fin, lagrangeBasis_boolVec, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The slice of a table at the low index `i`: the entries whose low `k` bits are `i`, one
every `2 ^ k` entries. -/
def sliceLow {k m : ℕ} (t : CMlPolynomialEval R (k + m)) (i : Fin (2 ^ k)) :
    CMlPolynomialEval R m :=
  Vector.ofFn fun j ↦ t[cubeIndex i j]

omit [CommRing R] in
theorem sliceLow_getElem {k m : ℕ} (t : CMlPolynomialEval R (k + m)) (i : Fin (2 ^ k))
    (j : Fin (2 ^ m)) : (sliceLow t i)[j] = t[cubeIndex i j] := by
  simp [sliceLow]

/-- Mapping the entries commutes with taking a low slice. -/
theorem sliceLow_map {S : Type*} [CommRing S] (φ : R →+* S) {k m : ℕ}
    (t : CMlPolynomialEval R (k + m)) (i : Fin (2 ^ k)) :
    CMlPolynomialEval.map φ (sliceLow t i) = sliceLow (CMlPolynomialEval.map φ t) i := by
  apply Vector.ext
  intro j hj
  simp [sliceLow, CMlPolynomialEval.map]

/-- The strided selection identity: Boolean low coordinates select the slice at that low
index. The mirror of `evalMle_append_boolVec`. -/
theorem evalMle_boolVec_append {k m : ℕ} (t : CMlPolynomialEval R (k + m)) (i : Fin (2 ^ k))
    (s : Vector R m) :
    evalMle t ((boolVec i : Vector R k) ++ s) = evalMle (sliceLow t i) s := by
  rw [evalMle_split, evalMle_eq_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [evalMle_boolVec, slice_getElem, sliceLow_getElem, mul_comm]

/-- A table placed at the high index `j`: its entries in the slice at `j`, zero in every other
slice. -/
def placeSlice {k m : ℕ} (t : CMlPolynomialEval R k) (j : Fin (2 ^ m)) :
    CMlPolynomialEval R (k + m) :=
  Vector.ofFn fun x ↦ if x.val / 2 ^ k = j.val then
    t[x.val % 2 ^ k]'(Nat.mod_lt _ (Nat.two_pow_pos k)) else 0

/-- Slicing a placed table gives the table at its index and zero at every other index. -/
theorem slice_placeSlice {k m : ℕ} (t : CMlPolynomialEval R k) (j h : Fin (2 ^ m)) :
    slice (placeSlice t j) h = if h = j then t else Vector.replicate (2 ^ k) 0 := by
  apply Vector.ext
  intro i hi
  have hdiv := cubeIndex_div (⟨i, hi⟩ : Fin (2 ^ k)) h
  simp only [cubeIndex_val] at hdiv
  by_cases hh : h = j
  · subst h
    simp [slice, placeSlice, hdiv, Nat.mod_eq_of_lt hi]
  · have hn : h.val ≠ j.val := fun he ↦ hh (Fin.ext he)
    simp [slice, placeSlice, hdiv, hh, hn]

/-- The extension of a placed table is the table's extension times the Lagrange basis of the
high coordinates at the index. -/
theorem evalMle_placeSlice {k m : ℕ} (t : CMlPolynomialEval R k) (j : Fin (2 ^ m))
    (z : Vector R k) (s : Vector R m) :
    evalMle (placeSlice t j) (z ++ s) = (lagrangeBasis s)[j] * evalMle t z := by
  rw [evalMle_split, Finset.sum_eq_single j]
  · simp [slice_placeSlice]
  · intro h _ hh
    simp [slice_placeSlice, hh, evalMle_replicate]
  · simp

/-! ## Splitting the low coordinates, and one coordinate at a time -/

/-- The low split: evaluation at `z ++ s` is the sum over the low index of the evaluations at the
Boolean low points, weighted by the Lagrange basis of `z`. -/
theorem evalMle_split_low {k m : ℕ} (t : CMlPolynomialEval R (k + m)) (z : Vector R k)
    (s : Vector R m) :
    evalMle t (z ++ s) =
      ∑ i : Fin (2 ^ k), (lagrangeBasis z)[i] * evalMle t ((boolVec i : Vector R k) ++ s) := by
  rw [evalMle_eq_sum, sum_cube_split, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [evalMle_eq_sum, sum_cube_split, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [lagrangeBasis_cubeIndex, lowVec_append, highVec_append, Finset.mul_sum,
    Finset.sum_eq_single i]
  · rw [lagrangeBasis_cubeIndex, lowVec_append, highVec_append]
    simp only [Fin.getElem_fin, lagrangeBasis_boolVec, ite_true]
    ring
  · intro i' _ hne
    rw [lagrangeBasis_cubeIndex, lowVec_append, highVec_append]
    simp [lagrangeBasis_boolVec, hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Evaluation is linear: the extension of a weighted sum of tables is the weighted sum of
their extensions. -/
theorem evalMle_ofFn_sum {n : ℕ} {ι : Type*} (s : Finset ι) (a : ι → R)
    (p : ι → CMlPolynomialEval R n) (r : Vector R n) :
    evalMle (Vector.ofFn fun x ↦ ∑ i ∈ s, a i * (p i)[x]) r = ∑ i ∈ s, a i * evalMle (p i) r := by
  simp only [evalMle_eq_sum, Fin.getElem_fin, Vector.getElem_ofFn, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- Evaluation is affine in each coordinate: the value at a point whose coordinate `k` is `X`
interpolates between the values at `0` and at `1`. -/
theorem evalMle_set {n : ℕ} (t : CMlPolynomialEval R n) (p : Vector R n) {k : ℕ} (hk : k < n)
    (X : R) :
    evalMle t (p.set k X) = (1 - X) * evalMle t (p.set k 0) + X * evalMle t (p.set k 1) := by
  simp only [evalMle_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  simp only [Fin.getElem_fin, lagrangeBasis_getElem_nat _ a.isLt]
  have hrest : ∀ Y : R, ∏ b ∈ Finset.univ.erase (⟨k, hk⟩ : Fin n),
      (if a.val.testBit b then (p.set k Y)[b.val] else 1 - (p.set k Y)[b.val]) =
      ∏ b ∈ Finset.univ.erase (⟨k, hk⟩ : Fin n),
        (if a.val.testBit b then p[b.val] else 1 - p[b.val]) := by
    intro Y
    refine Finset.prod_congr rfl fun b hb ↦ ?_
    have hbk : k ≠ b.val := fun h ↦ (Finset.mem_erase.mp hb).1 (Fin.ext h.symm)
    rw [Vector.getElem_set_ne hk b.isLt hbk]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (⟨k, hk⟩ : Fin n)),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (⟨k, hk⟩ : Fin n)),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (⟨k, hk⟩ : Fin n)),
    hrest, hrest, hrest]
  simp only [Vector.getElem_set_self]
  cases a.val.testBit k <;> simp <;> ring

/-! ## Tables of the low coordinates -/

omit [CommRing R] in
/-- The low `k` coordinates of a point on `n ≥ k` coordinates. -/
def lowCoords {k n : ℕ} (h : k ≤ n) (z : Vector R n) : Vector R k :=
  Vector.cast (min_eq_left h) (z.take k)

omit [CommRing R] in
@[simp] theorem getElem_lowCoords {k n : ℕ} (h : k ≤ n) (z : Vector R n) {a : ℕ} (ha : a < k) :
    (lowCoords h z)[a] = z[a] := by
  simp only [lowCoords, Vector.getElem_cast, Vector.getElem_take]

omit [CommRing R] in
/-- The low coordinates of a point split at `k` are its first part. -/
@[simp] theorem lowCoords_append {k m : ℕ} (z : Vector R k) (s : Vector R m) :
    lowCoords (Nat.le_add_right k m) (z ++ s) = z := by
  apply Vector.ext
  intro a ha
  rw [getElem_lowCoords _ _ ha, Vector.getElem_append_left ha]

/-- A table on `k` coordinates read on `n ≥ k`: the entry at `x` is the table's entry at the low
`k` bits of `x`, whatever the high bits. -/
def repeatHigh {k n : ℕ} (t : CMlPolynomialEval R k) (_ : k ≤ n) : CMlPolynomialEval R n :=
  Vector.ofFn fun x ↦ t[x.val % 2 ^ k]'(Nat.mod_lt _ (Nat.two_pow_pos k))

omit [CommRing R] in
/-- Every slice of a repeated table is the table. -/
theorem slice_repeatHigh {k m : ℕ} (t : CMlPolynomialEval R k) (j : Fin (2 ^ m)) :
    slice (repeatHigh t (Nat.le_add_right k m)) j = t := by
  apply Vector.ext
  intro i hi
  rw [← Fin.getElem_fin _ ⟨i, hi⟩, slice_getElem]
  simp only [repeatHigh, Fin.getElem_fin, Vector.getElem_ofFn, cubeIndex_mod]

/-- The extension of a repeated table ignores the high coordinates: it is the table's extension
at the low ones. -/
theorem evalMle_repeatHigh {k n : ℕ} (t : CMlPolynomialEval R k) (h : k ≤ n) (z : Vector R n) :
    evalMle (repeatHigh t h) z = evalMle t (lowCoords h z) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← lowVec_append_highVec z, evalMle_split]
  simp only [slice_repeatHigh, ← Finset.sum_mul, lowCoords_append]
  have hs := sumCube_lagrangeBasis (highVec z)
  simp only [sumCube] at hs
  rw [hs, one_mul]

end
end LeanVM.Protocol
