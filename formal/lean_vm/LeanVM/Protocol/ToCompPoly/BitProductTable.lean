/-
  LeanVM.Protocol.ToCompPoly.BitProductTable

  Hypercube tables whose entries factor over the bits of the index, and their multilinear
  extension, which factors over the coordinates. Candidate for CompPoly.
-/

module

public import LeanVM.Protocol.ToCompPoly.Multilinear

/-!
# Tables that factor over the index bits

`bitProductTable f` has, at index `i`, the product over the coordinates `k` of `f k b`, where `b`
is bit `k` of `i`. Its multilinear extension at `x` is the product over `k` of the one-variable
interpolants `(1 - x_k) * f k false + x_k * f k true` (`evalMle_bitProductTable`): a product
over the cube's coordinates never needs the `2 ^ n` entries. Over an arbitrary commutative
ring. Candidate for CompPoly, beside `CompPoly.Multilinear.Basic`. Nothing here transcribes a
source.

Two tables of this shape:

* the Lagrange basis `lagrangeBasis w` (`lagrangeBasis_eq_bitProductTable`), whose extension
  CompPoly writes as the equality kernel (`eqTilde_eq_prod`);
* the geometric table `powersTable a n`, entry `i` being `a ^ i`
  (`powersTable_eq_bitProductTable`, from the binary expansion `pow_eq_prod_testBit`), whose
  extension is `∏ k, ((1 - x_k) + x_k * a ^ 2 ^ k)` (`evalMle_powersTable`).

Coordinate `k` is bit `k` of the index, low bit first, so the order of the coordinates is part
of every statement.
-/

namespace LeanVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The table that factors over the bits of its index: the entry at `i` is the product over the
coordinates `k` of `f k b`, where `b` is bit `k` of `i`. -/
def bitProductTable {n : ℕ} (f : Fin n → Bool → R) : CMlPolynomialEval R n :=
  Vector.ofFn fun i ↦ ∏ k : Fin n, f k (i.val.testBit k)

theorem bitProductTable_getElem {n : ℕ} (f : Fin n → Bool → R) {i : ℕ} (hi : i < 2 ^ n) :
    (bitProductTable f)[i] = ∏ k : Fin n, f k (i.testBit k) := by
  simp [bitProductTable]

theorem map_bitProductTable {n : ℕ} (φ : R →+* S) (f : Fin n → Bool → R) :
    CMlPolynomialEval.map φ (bitProductTable f) = bitProductTable fun k b ↦ φ (f k b) := by
  apply Vector.ext
  intro i hi
  simp [CMlPolynomialEval.map, bitProductTable]

/-- The extension of a table that factors over the index bits factors over the coordinates. -/
theorem evalMle_bitProductTable {n : ℕ} (f : Fin n → Bool → R) (x : Vector R n) :
    evalMle (bitProductTable f) x =
      ∏ k : Fin n, ((1 - x[k]) * f k false + x[k] * f k true) := by
  induction n with
  | zero => simp [bitProductTable, evalMle, evalMleValues]
  | succ n ih =>
    rw [evalMle_succ]
    have hstep : evalMleLayer (bitProductTable f) x.head =
        ((1 - x.head) * f 0 false + x.head * f 0 true) •
          bitProductTable (fun k ↦ f k.succ) := by
      apply Vector.ext
      intro j hj
      rw [← Vector.get_eq_getElem _ ⟨j, hj⟩, evalMleLayer_get, Vector.getElem_smul]
      simp only [bitProductTable, Vector.get_ofFn, Vector.getElem_ofFn, smul_eq_mul]
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      have h0 : (2 * j).testBit 0 = false := by simp [Nat.testBit_zero]
      have h1 : (2 * j + 1).testBit 0 = true := by simp [Nat.testBit_zero]
      have hs0 : ∀ k : ℕ, (2 * j).testBit (k + 1) = j.testBit k := fun k ↦ by
        rw [Nat.testBit_succ]; congr 1; omega
      have hs1 : ∀ k : ℕ, (2 * j + 1).testBit (k + 1) = j.testBit k := fun k ↦ by
        rw [Nat.testBit_succ]; congr 1; omega
      simp only [Fin.val_zero, Fin.val_succ, h0, h1, hs0, hs1]
      ring
    rw [hstep, eval_mle_eq_eval, eval_smul, ← eval_mle_eq_eval, ih, Fin.prod_univ_succ]
    congr 1
    exact Finset.prod_congr rfl fun k _ ↦ by simp [Nat.add_comm]

/-- The extension at a point of another ring, after mapping the entries. -/
theorem eval₂Mle_bitProductTable {n : ℕ} (φ : R →+* S) (f : Fin n → Bool → R)
    (x : Vector S n) :
    eval₂Mle (bitProductTable f) φ x =
      ∏ k : Fin n, ((1 - x[k]) * φ (f k false) + x[k] * φ (f k true)) := by
  rw [eval₂Mle, map_bitProductTable, evalMle_bitProductTable]

/-- The Lagrange basis factors over the index bits. -/
theorem lagrangeBasis_eq_bitProductTable {n : ℕ} (w : Vector R n) :
    lagrangeBasis w = bitProductTable fun k b ↦ if b then w[k] else 1 - w[k] := by
  apply Vector.ext
  intro i hi
  rw [lagrangeBasis_getElem_nat w hi, bitProductTable_getElem _ hi]

/-- A power is the product of the repeated squares its exponent's bits select. -/
theorem pow_eq_prod_testBit (a : R) {n i : ℕ} (hi : i < 2 ^ n) :
    a ^ i = ∏ k : Fin n, if i.testBit k then a ^ 2 ^ k.val else 1 := by
  induction n generalizing a i with
  | zero =>
    have : i = 0 := by simpa using hi
    simp [this]
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    have hdiv : i / 2 < 2 ^ n := by omega
    have hrest : ∀ k : Fin n,
        (if i.testBit (k.succ : Fin (n + 1)).val then a ^ 2 ^ (k.succ : Fin (n + 1)).val else 1) =
          if (i / 2).testBit k then (a ^ 2) ^ 2 ^ k.val else 1 := fun k ↦ by
      rw [Fin.val_succ, Nat.testBit_succ, ← pow_mul, ← pow_succ']
    rw [Finset.prod_congr rfl fun k _ ↦ hrest k, ← ih (a ^ 2) hdiv, ← pow_mul]
    have hi2 : i = i % 2 + 2 * (i / 2) := (Nat.mod_add_div i 2).symm
    rcases Nat.mod_two_eq_zero_or_one i with h | h
    · have hb : i.testBit 0 = false := by simp [Nat.testBit_zero, h]
      simp only [Fin.val_zero, hb]
      rw [h, zero_add] at hi2
      simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
      conv_lhs => rw [hi2]
    · have hb : i.testBit 0 = true := by simp [Nat.testBit_zero, h]
      simp only [Fin.val_zero, hb, ite_true, pow_zero, pow_one]
      rw [h] at hi2
      conv_lhs => rw [hi2, pow_add, pow_one]

/-- The geometric table: entry `i` is `a ^ i`. -/
def powersTable (a : R) (n : ℕ) : CMlPolynomialEval R n :=
  Vector.ofFn fun i ↦ a ^ i.val

theorem powersTable_eq_bitProductTable (a : R) (n : ℕ) :
    powersTable a n = bitProductTable fun k b ↦ if b then a ^ 2 ^ k.val else 1 := by
  apply Vector.ext
  intro i hi
  rw [bitProductTable_getElem _ hi, ← pow_eq_prod_testBit a hi]
  simp [powersTable]

theorem map_powersTable (φ : R →+* S) (a : R) (n : ℕ) :
    CMlPolynomialEval.map φ (powersTable a n) = powersTable (φ a) n := by
  apply Vector.ext
  intro i hi
  simp [CMlPolynomialEval.map, powersTable]

/-- The extension of the geometric table is the product of its one-bit interpolants. -/
theorem evalMle_powersTable (a : R) (n : ℕ) (x : Vector R n) :
    evalMle (powersTable a n) x = ∏ k : Fin n, ((1 - x[k]) + x[k] * a ^ 2 ^ k.val) := by
  rw [powersTable_eq_bitProductTable, evalMle_bitProductTable]
  simp

theorem eval₂Mle_powersTable (φ : R →+* S) (a : R) (n : ℕ) (x : Vector S n) :
    eval₂Mle (powersTable a n) φ x =
      ∏ k : Fin n, ((1 - x[k]) + x[k] * φ (a ^ 2 ^ k.val)) := by
  rw [eval₂Mle, map_powersTable, evalMle_powersTable]
  simp only [map_pow]

end
end LeanVM.Protocol
