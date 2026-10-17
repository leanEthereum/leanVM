import KeccakGkr.Multilinear
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Polynomial.Coeff

/-!
# The embedding sixteen instances are packed with

`crates/keccak_gkr/src/rmfe.rs` packs sixteen bits into a binary polynomial of degree at most
`23` (`embMask i` is the embedding of the `i`-th unit vector, bit `k` the coefficient of `X^k`)
and reads sixteen bits back from a polynomial of degree at most `46` (bit `i` of the projection
is the parity of the coefficients `projMask i` selects). The tables below are the crate's, as
`Rmfe::build` computes them.

Over any field of characteristic two, `rmfe` proves Lemma `lem:rmfe` of `doc/leanvm` on the unit
vectors, `proj_k (emb_a * emb_b) = [a = b = k]`, which by bilinearity is the whole lemma. The
finite check behind it is `rmfe_table`, decided by the kernel.
-/

open Polynomial

namespace KeccakGkr

/-- The embedding of each unit vector, bit `k` the coefficient of `X^k`. -/
def embMask : Fin 16 → ℕ := ![4244747, 8354290, 4935178, 7500812, 5461978, 1907870, 310894,
  7885382, 621788, 1089150, 2036820, 2178300, 5045448, 7821168, 1602438, 8489494]

/-- Bit `i` of the projection is the parity of the coefficients `projMask i` selects. -/
def projMask : Fin 16 → ℕ := ![1, 140737488355327, 43218598786281, 32136906789799,
  111925089164473, 101951566367639, 112771593653537, 102871349771039, 126754541004432,
  60819261648545, 20682647020959, 30409630824272, 11891857888673, 6939470531743, 76314673122000,
  70368744177664]

/-- The parity of `p 0, …, p (n - 1)`. -/
def parBits : ℕ → (ℕ → Bool) → Bool
  | 0, _ => false
  | n + 1, p => xor (parBits n p) (p n)

/-- Bit `k` of the projection of `emb_a * emb_b`, as the parity of the products' terms. -/
def rmfeCell (a b k : Fin 16) : Bool :=
  parBits 24 fun i => (embMask a).testBit i &&
    parBits 24 fun j => (embMask b).testBit j && (projMask k).testBit (i + j)

set_option maxRecDepth 100000 in
theorem rmfe_table : ∀ a b k : Fin 16, rmfeCell a b k = (a == k && b == k) := by
  decide +kernel

theorem embMask_lt (a : Fin 16) : embMask a < 2 ^ 24 := by
  revert a
  decide

variable {E : Type} [Field E] [CharP E 2]

theorem bit_xor (x y : Bool) : (bit (xor x y) : E) = bit x + bit y := by
  cases x <;> cases y <;> simp [bit, CharTwo.add_self_eq_zero]

omit [CharP E 2] in
theorem bit_and (x y : Bool) : (bit (x && y) : E) = bit x * bit y := by
  cases x <;> cases y <;> simp [bit]

theorem sum_bit_eq_parBits (n : ℕ) (p : ℕ → Bool) :
    ∑ i ∈ Finset.range n, (bit (p i) : E) = bit (parBits n p) := by
  induction n with
  | zero => simp [parBits]
  | succ n ih => rw [Finset.sum_range_succ, ih, parBits, bit_xor]

/-- The embedding of the `a`-th unit vector. -/
noncomputable def embPoly (a : Fin 16) : E[X] :=
  ∑ i ∈ Finset.range 24, C (bit ((embMask a).testBit i)) * X ^ i

/-- Coordinate `k` of the projection, extended linearly to field coefficients. -/
def projE (k : Fin 16) (G : E[X]) : E :=
  ∑ c ∈ Finset.range 47, bit ((projMask k).testBit c) * G.coeff c

omit [CharP E 2] in
theorem embPoly_natDegree (a : Fin 16) : (embPoly a : E[X]).natDegree ≤ 23 := by
  refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  refine (natDegree_C_mul_X_pow_le _ _).trans ?_
  have := Finset.mem_range.mp hi
  omega

omit [CharP E 2] in
theorem projE_add (k : Fin 16) (G H : E[X]) : projE k (G + H) = projE k G + projE k H := by
  simp [projE, mul_add, Finset.sum_add_distrib]

omit [CharP E 2] in
theorem projE_C_mul (k : Fin 16) (e : E) (G : E[X]) : projE k (C e * G) = e * projE k G := by
  simp [projE, Finset.mul_sum, mul_left_comm]

omit [CharP E 2] in
theorem projE_sum {ι : Type} (s : Finset ι) (k : Fin 16) (G : ι → E[X]) :
    projE k (∑ i ∈ s, G i) = ∑ i ∈ s, projE k (G i) := by
  simp only [projE, finsetSum_coeff, Finset.mul_sum]
  exact Finset.sum_comm

omit [CharP E 2] in
theorem projE_X_pow (k : Fin 16) {m : ℕ} (hm : m < 47) :
    projE k (X ^ m : E[X]) = bit ((projMask k).testBit m) := by
  simp only [projE, coeff_X_pow]
  rw [Finset.sum_eq_single m]
  · simp
  · intro c _ hc; simp [hc]
  · intro h; exact absurd (Finset.mem_range.mpr hm) h

/-- Lemma `lem:rmfe` of `doc/leanvm` on the unit vectors. -/
theorem rmfe (a b k : Fin 16) :
    projE k (embPoly a * embPoly b : E[X]) = if a = k ∧ b = k then 1 else 0 := by
  have h : projE k (embPoly a * embPoly b : E[X]) = bit (rmfeCell a b k) := by
    simp only [embPoly, Finset.sum_mul, Finset.mul_sum, projE_sum]
    have : ∀ i ∈ Finset.range 24, ∀ j ∈ Finset.range 24,
        projE k (C (bit ((embMask a).testBit i)) * X ^ i *
          (C (bit ((embMask b).testBit j)) * X ^ j) : E[X]) =
        bit ((embMask a).testBit i && ((embMask b).testBit j && (projMask k).testBit (i + j))) := by
      intro i hi j hj
      rw [show (C (bit ((embMask a).testBit i)) * X ^ i *
          (C (bit ((embMask b).testBit j)) * X ^ j) : E[X]) =
          C (bit ((embMask a).testBit i) * bit ((embMask b).testBit j)) * X ^ (i + j) by
        rw [C_mul, pow_add]; ring]
      rw [projE_C_mul, projE_X_pow k (by simp at hi hj; omega), bit_and, bit_and, mul_assoc]
    rw [Finset.sum_comm,
      Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => this i hi j hj]
    simp only [bit_and, ← Finset.mul_sum]
    simp only [← bit_and, sum_bit_eq_parBits, rmfeCell]
  rw [h, rmfe_table]
  by_cases ha : a = k <;> by_cases hb : b = k <;> simp [ha, hb, bit]

end KeccakGkr
