/-
  LeanVM.Protocol.Whir.Sound.Lanes

  The verifier's lane arithmetic as folds of integer-indexed oracles: `dot(row, eq_kernel(s))`
  and `multilinear_eval(table, s)` are the row folded by the challenges, low bit first; and the
  regrouping of a message split into lanes and message bits.
-/

module

public import LeanVM.Protocol.Whir.Sound.Weights

/-!
# Lanes and folds

The deployed verifier (`LeanVM.Protocol.Verifier`, leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`, `python-verifier/verifier.py:232-244, 956-961`)
reduces an opened row of `2^ℓ` lanes with the equality kernel of the level's fold challenges,
`dot(row, eq_kernel(folds))`, and evaluates the final residual table with `multilinear_eval`.
Both are the integer-indexed fold `foldsN` of `LeanVM.Protocol.Whir.Sound.Code`, the first
challenge binding the low bit:

* `foldsN_eq_sum`: `foldsN s O i = Σ_{j < 2^|s|} eq(s, j)·O(i·2^|s| + j)`, with `eqB s j` the
  equality weight of the bits of `j`;
* `getD_eqKernel`: the entries of `eq_kernel(s)` are `eqB s j` (characteristic two:
  `1 + r = 1 − r`), so `dot_eqKernel`: `dot(row, eq_kernel(s)) = foldsN s row 0`;
* `multilinearEval_eq_foldsN`: `multilinear_eval(t, s) = foldsN s t 0` for a table of `2^|s|`
  entries.

`joinMsg` regroups a message on `m` lane bits and `κ'` message bits into one message on
`n = m + κ'` bits (`sum_joinMsg`).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Whir Finset

@[expose] public section

/-! ## Equality weights of integer indices -/

/-- `eq(s, j) = Π_i (j_i ? s_i : 1 − s_i)`, bit `0` of `j` paired with `s₀`. -/
def eqB : List E → ℕ → E
  | [], _ => 1
  | c :: s, j => (if j % 2 = 1 then c else 1 - c) * eqB s (j / 2)

/-- A sum over `2N` indices pairs even and odd ones. -/
theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ j ∈ range (2 * N), f j = ∑ j ∈ range N, (f (2 * j) + f (2 * j + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, add_assoc]

/-- **The fold is an eq-weighted sum**: `foldsN s O i = Σ_{j < 2^|s|} eq(s, j)·O(i·2^|s| + j)`. -/
theorem foldsN_eq_sum {ι : Type*} (s : List E) (O : ℕ → ι → E) (i : ℕ) (x : ι) :
    foldsN s O i x = ∑ j ∈ range (2 ^ s.length), eqB s j * O (i * 2 ^ s.length + j) x := by
  induction s generalizing O i with
  | nil => simp [foldsN, eqB]
  | cons c s ih =>
    simp only [foldsN, List.foldl_cons] at ih ⊢
    rw [ih, List.length_cons, pow_succ, mul_comm (2 ^ s.length) 2, sum_range_two_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [foldN, eqB, Nat.mul_add_mod, Nat.mul_mod_right,
      Nat.mul_add_div (by norm_num : 0 < 2),
      Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    norm_num
    rw [show i * (2 * 2 ^ s.length) + 2 * j = 2 * (i * 2 ^ s.length + j) by ring,
      show i * (2 * 2 ^ s.length) + (2 * j + 1) = 2 * (i * 2 ^ s.length + j) + 1 by ring]
    ring

/-- `eqB s j` reads only the low `|s|` bits of `j`. -/
theorem eqB_congr (s : List E) {j j' : ℕ} (h : ∀ i < s.length, j.testBit i = j'.testBit i) :
    eqB s j = eqB s j' := by
  induction s generalizing j j' with
  | nil => rfl
  | cons c s ih =>
    simp only [eqB]
    have h0 := h 0 (by simp)
    simp only [Nat.testBit_zero, decide_eq_decide] at h0
    rw [ih (j := j / 2) (j' := j' / 2) fun i hi ↦ by
      rw [Nat.testBit_div_two, Nat.testBit_div_two]; exact h (i + 1) (by simp; omega)]
    have : (j % 2 = 1) = (j' % 2 = 1) := propext h0
    simp only [this]

/-- Appending a challenge multiplies by the factor of the next bit. -/
theorem eqB_append (s : List E) (r : E) (j : ℕ) :
    eqB (s ++ [r]) j = eqB s j * (if j.testBit s.length then r else 1 - r) := by
  induction s generalizing j with
  | nil => simp [eqB, Nat.testBit_zero]
  | cons c s ih =>
    simp only [List.cons_append, eqB, ih, List.length_cons, ← Nat.testBit_div_two]
    ring

/-- `eq_kernel(s)` has `2^|s|` entries. -/
theorem length_eqKernel (s : List E) : (eqKernel s).length = 2 ^ s.length := by
  induction s using List.reverseRecOn with
  | nil => simp [eqKernel]
  | append_singleton s r ih =>
    rw [eqKernel, List.foldl_append] at *
    simp [ih, pow_succ, mul_two]

theorem getD_map_mul (K : List E) (c : E) (j : ℕ) :
    (K.map (· * c)).getD j 0 = K.getD j 0 * c := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases K[j]? <;> simp

theorem getD_append' (A B : List E) (j : ℕ) :
    (A ++ B).getD j 0 = if j < A.length then A.getD j 0 else B.getD (j - A.length) 0 := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_append_right (by omega)]

/-- **The entries of `eq_kernel(s)`** are the equality weights `eqB s j`. -/
theorem getD_eqKernel (s : List E) {j : ℕ} (hj : j < 2 ^ s.length) :
    (eqKernel s).getD j 0 = eqB s j := by
  induction s using List.reverseRecOn generalizing j with
  | nil => simp [eqKernel, eqB] at hj ⊢; subst hj; rfl
  | append_singleton s r ih =>
    have hlen := length_eqKernel s
    have hk : eqKernel (s ++ [r]) = (eqKernel s).map (· * (1 + r)) ++ (eqKernel s).map (· * r) := by
      simp [eqKernel, List.foldl_append]
    rw [hk, eqB_append]
    rw [List.length_append, List.length_singleton, pow_succ, mul_two] at hj
    rw [getD_append']
    simp only [List.length_map, hlen]
    by_cases hlt : j < 2 ^ s.length
    · simp only [hlt, ↓reduceIte, getD_map_mul, ih hlt, Nat.testBit_lt_two_pow hlt,
        CharTwo.sub_eq_add]
      simp
    · push Not at hlt
      simp only [show ¬ j < 2 ^ s.length by omega, ↓reduceIte, getD_map_mul]
      rw [ih (by omega)]
      have hdiv : j / 2 ^ s.length = 1 :=
        Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)
      have hbit : j.testBit s.length = true := by
        rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff, hdiv]
      simp only [hbit, ↓reduceIte]
      congr 1
      refine eqB_congr s fun i hi ↦ ?_
      rw [show j - 2 ^ s.length = j % 2 ^ s.length by
        rw [Nat.mod_eq_sub_mod hlt, Nat.mod_eq_of_lt (by omega)], Nat.testBit_mod_two_pow]
      simp [hi]

/-- `dot` of two lists of equal length is the indexed sum. -/
theorem dot_eq_sum (a b : List E) (h : a.length = b.length) :
    dot a b = ∑ j ∈ range a.length, a.getD j 0 * b.getD j 0 := by
  rw [dot, foldl_add_eq, zero_add]
  induction a generalizing b with
  | nil => simp
  | cons x a ih =>
    cases b with
    | nil => simp at h
    | cons y b =>
      simp only [List.zipWith_cons_cons, List.sum_cons, List.length_cons,
        Finset.sum_range_succ', List.getD_cons_succ, List.getD_cons_zero]
      rw [ih b (by simpa using h), add_comm]

/-- **The lane fold of an opened row**: `dot(row, eq_kernel(s))` is the row folded by `s`. -/
theorem dot_eqKernel (row s : List E) (h : row.length = 2 ^ s.length) :
    dot row (eqKernel s) = foldsN s (fun j (_ : Unit) ↦ row.getD j 0) 0 () := by
  rw [dot_eq_sum _ _ (by rw [h, length_eqKernel]), foldsN_eq_sum, h]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [getD_eqKernel s (Finset.mem_range.mp hj), zero_mul, zero_add, mul_comm]

/-- The fold is computed column by column. -/
theorem foldsN_apply {ι : Type*} (s : List E) (O : ℕ → ι → E) (j : ℕ) (x : ι) :
    foldsN s O j x = foldsN s (fun j' (_ : Unit) ↦ O j' x) j () := by
  rw [foldsN_eq_sum, foldsN_eq_sum]

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

/-- Claims are linear in the weight. -/
theorem claimSum_add_smul {m κ : ℕ} (Φ Ψ : List E → E) (c : E)
    (g : (Fin m → Bool) → (Fin κ → Bool) → E) :
    claimSum (fun r ↦ Φ r + c * Ψ r) g = claimSum Φ g + c * claimSum Ψ g := by
  simp only [claimSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun x _ ↦ by ring

end
end LeanVM.Protocol.Whir.Sound
