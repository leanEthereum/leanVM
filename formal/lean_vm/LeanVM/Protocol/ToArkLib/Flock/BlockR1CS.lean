/-
  LeanVM.Protocol.ToArkLib.Flock.BlockR1CS

  One block of a rank-one constraint system whose third matrix is the identity: two Boolean
  matrices, with evaluators of their products and of their transposes' products. Candidate for
  ArkLib.
-/

module

public import LeanVM.Protocol.ToCompPoly.Multilinear
public import Mathlib.Algebra.CharP.Defs

/-!
# Blocks of an R1CS with `C = I`

A Boolean circuit whose linear wires are substituted away is a rank-one constraint system
`(A z) ∘ (B z) = z`: one row per committed wire, `A` and `B` Boolean square matrices on the
`2 ^ m` positions of a witness block, the third matrix the identity. A verifier never builds the
matrices: it evaluates the products `A W`, `B W` (a forward walk of the circuit) and the
transposes' `Aᵀ e`, `Bᵀ e` (a backward walk). A `BlockR1CS R m` carries the two matrices and the
two walks over a commutative ring `R`, with the proofs that the walks compute the products
(`rows_fst`, `rows_snd`, `cols_fst`, `cols_snd`).

* `BlockR1CS.Holds C z`: the block `z` satisfies `(A z)_k · (B z)_k = z_k` at every position.
* `rows_add`, `rows_smul_*`, `rows_sum`: the walks are linear, so a combination of blocks walks
  to the combination of their walks.
* `sum_mul_rows_fst`, `sum_mul_rows_snd`: the adjoint identity `Σ_k e_k (A W)_k = Σ_j (Aᵀ e)_j W_j`.
* `isBool_rows_fst`, `isBool_rows_snd`: in characteristic two, a Boolean block walks to Boolean
  products.

A batch of `2 ^ κ` blocks of `2 ^ (s + m)` positions is stored as `2 ^ s` tables on the other
`m + κ` coordinates, table `jsk` holding the positions whose low `s` bits are `jsk`
(`batchBlock`): the layout of a witness whose low `s` coordinates are packed into one element.
`BatchHolds C cpos z`: every block of the batch satisfies the constraints and holds `1` at the
constant position `cpos`.

Generic over the ring; nothing here transcribes a source.
-/

namespace LeanVM.Protocol

open CompPoly

@[expose] public section

variable {R : Type*} [CommRing R]

/-- One block of an R1CS with `C = I` on `2 ^ m` positions: the Boolean matrices `A` and `B`, a
walk computing `(A W, B W)` and a walk computing `(Aᵀ e, Bᵀ e)`, with the proofs that they
compute those products. -/
structure BlockR1CS (R : Type*) [CommRing R] (m : ℕ) where
  /-- The left matrix, `A k j` its entry at row `k` and column `j`. -/
  A : Fin (2 ^ m) → Fin (2 ^ m) → Bool
  /-- The right matrix. -/
  B : Fin (2 ^ m) → Fin (2 ^ m) → Bool
  /-- The forward walk: `(A W, B W)`. -/
  rows : CMlPolynomialEval R m → CMlPolynomialEval R m × CMlPolynomialEval R m
  /-- The backward walk: `(Aᵀ e, Bᵀ e)`. -/
  cols : CMlPolynomialEval R m → CMlPolynomialEval R m × CMlPolynomialEval R m
  /-- The forward walk computes `A W`. -/
  rows_fst : ∀ W (k : Fin (2 ^ m)), (rows W).1[k] = ∑ j, if A k j then W[j] else 0
  /-- The forward walk computes `B W`. -/
  rows_snd : ∀ W (k : Fin (2 ^ m)), (rows W).2[k] = ∑ j, if B k j then W[j] else 0
  /-- The backward walk computes `Aᵀ e`. -/
  cols_fst : ∀ e (j : Fin (2 ^ m)), (cols e).1[j] = ∑ k, if A k j then e[k] else 0
  /-- The backward walk computes `Bᵀ e`. -/
  cols_snd : ∀ e (j : Fin (2 ^ m)), (cols e).2[j] = ∑ k, if B k j then e[k] else 0

namespace BlockR1CS

variable {m : ℕ} (C : BlockR1CS R m)

/-- The block satisfies the constraints: `(A z)_k · (B z)_k = z_k` at every position. -/
def Holds (z : CMlPolynomialEval R m) : Prop :=
  ∀ k : Fin (2 ^ m), (C.rows z).1[k] * (C.rows z).2[k] = z[k]

/-- Decided with one walk of the block, shared by every position. -/
instance [DecidableEq R] (z : CMlPolynomialEval R m) : Decidable (C.Holds z) :=
  match h : C.rows z with
  | w => decidable_of_iff (∀ k : Fin (2 ^ m), w.1[k] * w.2[k] = z[k]) (by rw [Holds, h])

/-- A block with the naive walks, summing the products entry by entry: for small circuits. -/
def ofMatrices (A B : Fin (2 ^ m) → Fin (2 ^ m) → Bool) : BlockR1CS R m where
  A := A
  B := B
  rows W := (Vector.ofFn fun k ↦ ∑ j, if A k j then W[j] else 0,
    Vector.ofFn fun k ↦ ∑ j, if B k j then W[j] else 0)
  cols e := (Vector.ofFn fun j ↦ ∑ k, if A k j then e[k] else 0,
    Vector.ofFn fun j ↦ ∑ k, if B k j then e[k] else 0)
  rows_fst W k := by simp
  rows_snd W k := by simp
  cols_fst e j := by simp
  cols_snd e j := by simp

/-! ## Linearity -/

private theorem sum_ite_add (p : Fin (2 ^ m) → Bool) (W W' : Fin (2 ^ m) → R) :
    (∑ j, if p j then W j + W' j else 0) =
      (∑ j, if p j then W j else 0) + ∑ j, if p j then W' j else 0 := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ by split <;> simp

/-- The forward walk of a weighted sum of blocks is the weighted sum of their walks, left
product. -/
theorem rows_fst_sum {ι : Type*} (s : Finset ι) (a : ι → R) (W : ι → CMlPolynomialEval R m)
    (k : Fin (2 ^ m)) :
    (C.rows (Vector.ofFn fun j ↦ ∑ i ∈ s, a i * (W i)[j])).1[k] =
      ∑ i ∈ s, a i * (C.rows (W i)).1[k] := by
  simp only [rows_fst, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  split <;> simp

/-- The forward walk of a weighted sum of blocks is the weighted sum of their walks, right
product. -/
theorem rows_snd_sum {ι : Type*} (s : Finset ι) (a : ι → R) (W : ι → CMlPolynomialEval R m)
    (k : Fin (2 ^ m)) :
    (C.rows (Vector.ofFn fun j ↦ ∑ i ∈ s, a i * (W i)[j])).2[k] =
      ∑ i ∈ s, a i * (C.rows (W i)).2[k] := by
  simp only [rows_snd, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  split <;> simp

/-! ## The adjoint identity -/

/-- `Σ_k e_k (A W)_k = Σ_j (Aᵀ e)_j W_j`. -/
theorem sum_mul_rows_fst (e W : CMlPolynomialEval R m) :
    ∑ k : Fin (2 ^ m), e[k] * (C.rows W).1[k] = ∑ j : Fin (2 ^ m), (C.cols e).1[j] * W[j] := by
  simp only [rows_fst, cols_fst, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  split <;> simp [mul_comm]

/-- `Σ_k e_k (B W)_k = Σ_j (Bᵀ e)_j W_j`. -/
theorem sum_mul_rows_snd (e W : CMlPolynomialEval R m) :
    ∑ k : Fin (2 ^ m), e[k] * (C.rows W).2[k] = ∑ j : Fin (2 ^ m), (C.cols e).2[j] * W[j] := by
  simp only [rows_snd, cols_snd, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  split <;> simp [mul_comm]

/-! ## Boolean blocks -/

/-- A Boolean value: `0` or `1`. -/
def IsBool (x : R) : Prop := x = 0 ∨ x = 1

omit [CommRing R] in
private theorem isBool_sum [CommRing R] [CharP R 2] {ι : Type*} (s : Finset ι) (f : ι → R)
    (hf : ∀ i ∈ s, IsBool (f i)) : IsBool (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Or.inl (by simp)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have h2 : (1 : R) + 1 = 0 := by
      have := CharP.cast_eq_zero R 2
      rw [Nat.cast_ofNat] at this
      rw [one_add_one_eq_two, this]
    rcases hf a (Finset.mem_insert_self a s) with h | h <;>
      rcases ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi) with h' | h' <;>
      simp [IsBool, h, h', h2]

/-- In characteristic two, a Boolean block walks to a Boolean left product. -/
theorem isBool_rows_fst [CharP R 2] {z : CMlPolynomialEval R m}
    (hz : ∀ j : Fin (2 ^ m), IsBool z[j])
    (k : Fin (2 ^ m)) : IsBool (C.rows z).1[k] := by
  rw [rows_fst]
  exact isBool_sum _ _ fun j _ ↦ by split <;> [exact hz j; exact Or.inl rfl]

/-- In characteristic two, a Boolean block walks to a Boolean right product. -/
theorem isBool_rows_snd [CharP R 2] {z : CMlPolynomialEval R m}
    (hz : ∀ j : Fin (2 ^ m), IsBool z[j])
    (k : Fin (2 ^ m)) : IsBool (C.rows z).2[k] := by
  rw [rows_snd]
  exact isBool_sum _ _ fun j _ ↦ by split <;> [exact hz j; exact Or.inl rfl]

/-! ## A batch of blocks -/

/-- Block `t` of a batch stored as `2 ^ s` tables: position `j`, whose low `s` bits are `jsk` and
whose high `m` bits are `jin`, holds entry `cubeIndex jin t` of table `jsk`. -/
def batchBlock {s m κ : ℕ} (z : Fin (2 ^ s) → CMlPolynomialEval R (m + κ)) (t : Fin (2 ^ κ)) :
    CMlPolynomialEval R (s + m) :=
  Vector.ofFn fun j ↦ (z ((cubeSplit s m).symm j).1)[cubeIndex ((cubeSplit s m).symm j).2 t]

omit [CommRing R] in
theorem batchBlock_cubeIndex {s m κ : ℕ} (z : Fin (2 ^ s) → CMlPolynomialEval R (m + κ))
    (t : Fin (2 ^ κ)) (jsk : Fin (2 ^ s)) (jin : Fin (2 ^ m)) :
    (batchBlock z t)[cubeIndex jsk jin] = (z jsk)[cubeIndex jin t] := by
  have h : (cubeSplit s m).symm (cubeIndex jsk jin) = (jsk, jin) := by
    rw [← cubeSplit_apply, Equiv.symm_apply_apply]
  simp only [batchBlock, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, h]

/-- Every block of the batch satisfies the constraints and holds `1` at the constant
position. -/
def BatchHolds {s m κ : ℕ} (C : BlockR1CS R (s + m)) (cpos : Fin (2 ^ (s + m)))
    (z : Fin (2 ^ s) → CMlPolynomialEval R (m + κ)) : Prop :=
  ∀ t : Fin (2 ^ κ), C.Holds (batchBlock z t) ∧ (batchBlock z t)[cpos] = 1

instance {s m κ : ℕ} [DecidableEq R] (C : BlockR1CS R (s + m)) (cpos : Fin (2 ^ (s + m)))
    (z : Fin (2 ^ s) → CMlPolynomialEval R (m + κ)) : Decidable (BatchHolds C cpos z) :=
  inferInstanceAs (Decidable (∀ _t : Fin (2 ^ κ), _ ∧ _))

end BlockR1CS

end
end LeanVM.Protocol
