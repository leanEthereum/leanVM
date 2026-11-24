/-
  LeanVM.Protocol.Whir.Sound.Lanes

  The verifier's lane arithmetic as folds of integer-indexed oracles: `dot(row, eq_kernel(s))`
  and `multilinear_eval(table, s)` are the row folded by the challenges, low bit first; and the
  regrouping of a message split into lanes and message bits.
-/

module

import LeanVM.Protocol.Whir.Sound.Weights
public import LeanVM.Protocol.Verifier.EqKernel
public import LeanVM.Protocol.Whir.Sound.Sumcheck
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.Johnson.FiniteBounds
public import ArkLib.Data.CodingTheory.ReedSolomon
public import Mathlib.Tactic

/-!
# Lanes and folds

The deployed verifier (`LeanVM.Protocol.Verifier`, leanVM `40f877dc`,
`crates/verifier/src/whir.rs`, `multilinear.rs`)
reduces an opened row of `2^ℓ` lanes with the equality kernel of the level's fold challenges,
`dot(row, eq_kernel(folds))`, and evaluates the final residual table with `multilinear_eval`.
Both are the integer-indexed fold `foldsN`, the first
challenge binding the low bit:

* `foldsN_eq_sum`: `foldsN s O i = Σ_{j < 2^|s|} eq(s, j)·O(i·2^|s| + j)`, `eq(s, j) = eqAt s j`
  the equality weight of the bits of `j` (characteristic two: `1 + r = 1 − r`), the entries of
  `eq_kernel(s)` (`eqKernel_getD`), so `dot_eqKernel_eq_foldsN`:
  `dot(row, eq_kernel(s)) = foldsN s row 0`;
* `multilinearEval_eq_foldsN`: `multilinear_eval(t, s) = foldsN s t 0` for a table of `2^|s|`
  entries.

`joinMsg` regroups a message on `m` lane bits and `κ'` message bits into one message on
`n = m + κ'` bits (`sum_joinMsg`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Whir Finset

@[expose] public section

/-! ## Integer-indexed folds -/

/-- One fold of an integer-indexed lane oracle on the low lane bit. -/
def foldN {ι : Type*} (s : E) (O : ℕ → ι → E) : ℕ → ι → E :=
  fun j x ↦ (1 - s) * O (2 * j) x + s * O (2 * j + 1) x

/-- The folds of a list of challenges, first challenge first. -/
def foldsN {ι : Type*} (s : List E) (O : ℕ → ι → E) : ℕ → ι → E :=
  s.foldl (fun O c ↦ foldN c O) O

/-- **The fold is an eq-weighted sum**: `foldsN s O i = Σ_{j < 2^|s|} eq(s, j)·O(i·2^|s| + j)`. -/
theorem foldsN_eq_sum {ι : Type*} (s : List E) (O : ℕ → ι → E) (i : ℕ) (x : ι) :
    foldsN s O i x = ∑ j ∈ range (2 ^ s.length), eqAt s j * O (i * 2 ^ s.length + j) x := by
  induction s generalizing O i with
  | nil => simp [foldsN]
  | cons c s ih =>
    simp only [foldsN, List.foldl_cons] at ih ⊢
    rw [ih, List.length_cons, pow_succ, mul_comm (2 ^ s.length) 2, sum_range_two_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [foldN, CharTwo.sub_eq_add]
    rw [(eqAt_two_mul c s j).1, (eqAt_two_mul c s j).2,
      show i * (2 * 2 ^ s.length) + 2 * j = 2 * (i * 2 ^ s.length + j) by ring,
      show i * (2 * 2 ^ s.length) + (2 * j + 1) = 2 * (i * 2 ^ s.length + j) + 1 by ring]
    ring

/-- **The lane fold of an opened row**: `dot(row, eq_kernel(s))` is the row folded by `s`. -/
theorem dot_eqKernel_eq_foldsN (row s : List E) (h : row.length = 2 ^ s.length) :
    dot row (eqKernel s) = foldsN s (fun j (_ : Unit) ↦ row.getD j 0) 0 () := by
  rw [dot_eq_sum _ _ (by rw [h, eqKernel_length]), foldsN_eq_sum, h]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [eqKernel_getD, ite_eq_left (Finset.mem_range.mp hj), zero_mul, zero_add, mul_comm]

/-! ## `multilinear_eval` -/

/-- One `foldPairs` step is one `foldN` on an even-length table. -/
theorem getD_foldPairs (r : E) : ∀ (l : List E), Even l.length → ∀ j,
    (foldPairs r l).getD j 0 = foldN r (fun j' (_ : Unit) ↦ l.getD j' 0) j ()
  | [], _, j => by simp [foldPairs, foldN]
  | [a], hl, j => by simp at hl
  | a :: b :: rest, hl, j => by
    have he : Even rest.length := by
      simpa [Nat.even_add_one, parity_simps] using hl
    cases j with
    | zero => simp [foldPairs, foldN, CharTwo.sub_eq_add]; ring
    | succ j =>
      rw [foldPairs, List.getD_cons_succ, getD_foldPairs r rest he j]
      simp [foldN, show 2 * (j + 1) = 2 * j + 2 by ring]

theorem length_foldPairs (r : E) : ∀ (l : List E), (foldPairs r l).length = l.length / 2
  | [] => by simp [foldPairs]
  | [a] => by simp [foldPairs]
  | a :: b :: rest => by
    rw [foldPairs, List.length_cons, length_foldPairs r rest]
    simp only [List.length_cons]
    omega

/-- **`multilinear_eval` is the fold**: for a table of `2^|s|` entries,
`multilinear_eval(t, s) = foldsN s t 0`. -/
theorem multilinearEval_eq_foldsN (t s : List E) (h : t.length = 2 ^ s.length) :
    multilinearEval t s = foldsN s (fun j (_ : Unit) ↦ t.getD j 0) 0 () := by
  rw [multilinearEval]
  suffices H : ∀ (s : List E) (t : List E), t.length = 2 ^ s.length →
      ∀ j, (s.foldl (fun cur r ↦ foldPairs r cur) t).getD j 0 =
        foldsN s (fun j (_ : Unit) ↦ t.getD j 0) j () by
    rw [← H s t h 0, List.headD_eq_getD]
  intro s
  induction s with
  | nil => intro t _ j; simp [foldsN]
  | cons c s ih =>
    intro t ht j
    rw [List.foldl_cons, ih _ (by rw [length_foldPairs, ht, List.length_cons, pow_succ]; simp)]
    have hf : (fun j (_ : Unit) ↦ (foldPairs c t).getD j 0) = foldN c (fun j _ ↦ t.getD j 0) := by
      funext j' u
      exact getD_foldPairs c t (by rw [ht, List.length_cons, pow_succ]; simp) j'
    simp only [foldsN, List.foldl_cons, hf]

/-! ## Regrouping lanes and message bits -/

/-- A message on `m` lane bits and `κ'` message bits as one message on `n = m + κ'` bits, the
lane bits first. -/
def joinMsg {n m κ' : ℕ} (hn : n = m + κ') (g : (Fin m → Bool) → (Fin κ' → Bool) → E) :
    (Fin n → Bool) → E :=
  fun p ↦ g (fun i ↦ p (Fin.cast hn.symm (Fin.castAdd κ' i)))
    (fun i ↦ p (Fin.cast hn.symm (Fin.natAdd m i)))

/-- The split of a cube point into lane and message bits. -/
def splitEquiv (m κ' : ℕ) : (Fin m → Bool) × (Fin κ' → Bool) ≃ (Fin (m + κ') → Bool) where
  toFun uv := Fin.append uv.1 uv.2
  invFun p := (fun i ↦ p (Fin.castAdd κ' i), fun i ↦ p (Fin.natAdd m i))
  left_inv uv := by simp
  right_inv p := by simp [Fin.append_castAdd_natAdd]

theorem bitsL_append {m κ' : ℕ} (u : Fin m → Bool) (v : Fin κ' → Bool) :
    bitsL (Fin.append u v) = bitsL u ++ bitsL v := by
  simp [bitsL, List.ofFn_add, Fin.append_right]

/-- **Regrouping**: the inner product with the joined message on the full cube is the claim on
the split message. -/
theorem sum_joinMsg {n m κ' : ℕ} (hn : n = m + κ') (Φ : List E → E)
    (g : (Fin m → Bool) → (Fin κ' → Bool) → E) :
    ∑ p, Φ (bitsL p) * joinMsg hn g p = claimSum Φ g := by
  subst hn
  rw [claimSum, ← Fintype.sum_prod_type', ← (splitEquiv m κ').sum_comp]
  refine Finset.sum_congr rfl fun uv _ ↦ ?_
  simp [splitEquiv, joinMsg, bitsL_append]

/-- A claim on zero lane bits is the inner product on the message cube. -/
theorem claimSum_zero {κ : ℕ} (Φ : List E → E) (g : (Fin 0 → Bool) → (Fin κ → Bool) → E) :
    claimSum Φ g = ∑ x, Φ (bitsL x) * g Fin.elim0 x := by
  rw [claimSum, Fintype.sum_eq_single (Fin.elim0 : Fin 0 → Bool)
    fun u hu ↦ absurd (funext fun i ↦ i.elim0) hu]
  simp only [bitsL_zero, List.nil_append]

end
end LeanVM.Protocol.Whir.Sound
