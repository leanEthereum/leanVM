/-
  LeanVM.Protocol.Verifier.EqKernel

  The verifier's equality kernel `eq_kernel`, its inner product `dot` and the equality weight they
  compute, as sums over the hypercube.
-/

module

public import Statement.LeanVmVerifier
public import LeanVM.Parameters.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Data.List.GetD

/-!
# The equality kernel

The verifier's points are lists, the first coordinate the lowest bit of an index (`eq_kernel`,
`crates/verifier/src/multilinear.rs`). Here:

* `eqAt pt w = Π_k eq(pt_k, bit k of w)`, defined coordinate by coordinate from the first;
  `eqAt_append`: a point split in two; `eqAt_two_mul`, `eqAt_two_mul_add_one`: a pair of indices;
  `sum_eqAt`: the weights sum to one;
* `eqKernel_snoc`: one more coordinate doubles the kernel; `eqKernel_length`,
  `eqKernel_getD`: `eqKernel pt` lists `eqAt pt w` for `w < 2^|pt|`;
* `dot_eq_sum_left`, `dot_eqKernel`: the verifier's inner product as a sum, and with the kernel the
  equality-weighted sum (`foldl_add_eq`, `foldl_mul_eq`: folds are sums and products);
* `sum_range_two_mul`, `sum_range_mul`: sums over a range regrouped, for any commutative monoid.

All of it is characteristic two: `1 + r` is `1 - r`.
-/

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters Finset

@[expose] public section

/-! ## Sums over ranges -/

/-- A sum over `2N` indices pairs even and odd ones. -/
theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ j ∈ range (2 * N), f j = ∑ j ∈ range N, (f (2 * j) + f (2 * j + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, add_assoc]

/-- A sum over `a·b` indices, by blocks of `b`. -/
theorem sum_range_mul {M : Type*} [AddCommMonoid M] (a b : ℕ) (F : ℕ → M) :
    ∑ p ∈ range (a * b), F p = ∑ i ∈ range a, ∑ k ∈ range b, F (b * i + k) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]
    congr 1
    refine sum_congr rfl fun k _ ↦ ?_
    rw [Nat.mul_comm a b]

/-- Sums over the cube of `m + 1` coordinates split on the first. -/
theorem sum_cube_succ {M : Type*} [AddCommMonoid M] (m : ℕ) (F : ℕ → M) :
    ∑ w ∈ range (2 ^ (m + 1)), F w = ∑ w ∈ range (2 ^ m), (F (2 * w) + F (2 * w + 1)) := by
  rw [pow_succ, mul_comm, sum_range_two_mul]

/-! ## Equality weights -/

/-- The equality weight of index `w` at the point `pt`, the first coordinate on the lowest bit. -/
def eqAt : List E → ℕ → E
  | [], _ => 1
  | r :: rs, w => (if w % 2 = 1 then r else 1 + r) * eqAt rs (w / 2)

@[simp] theorem eqAt_nil (w : ℕ) : eqAt [] w = 1 := rfl

theorem eqAt_cons (r : E) (rs : List E) (w : ℕ) :
    eqAt (r :: rs) w = (if w % 2 = 1 then r else 1 + r) * eqAt rs (w / 2) := rfl

/-- Only the low `|pt|` bits matter. -/
theorem eqAt_mod : ∀ (pt : List E) (w : ℕ), eqAt pt w = eqAt pt (w % 2 ^ pt.length)
  | [], _ => rfl
  | r :: rs, w => by
    rw [eqAt_cons, eqAt_cons, List.length_cons, pow_succ, mul_comm (2 ^ rs.length) 2,
      Nat.mod_mul_right_mod, Nat.mod_mul_right_div_self, ← eqAt_mod rs]

/-- A point split in two. -/
theorem eqAt_append : ∀ (a b : List E) (w : ℕ),
    eqAt (a ++ b) w = eqAt a w * eqAt b (w / 2 ^ a.length)
  | [], b, w => by simp
  | r :: a, b, w => by
    rw [List.cons_append, eqAt_cons, eqAt_cons, eqAt_append a b, List.length_cons, pow_succ,
      Nat.div_div_eq_div_mul, mul_comm (2 ^ a.length) 2, mul_assoc]

/-- The weight at the even index of a pair. -/
theorem eqAt_two_mul (r : E) (rs : List E) (w : ℕ) :
    eqAt (r :: rs) (2 * w) = (1 + r) * eqAt rs w := by
  rw [eqAt_cons, ite_eq_right (show ¬2 * w % 2 = 1 by omega), show 2 * w / 2 = w by omega]

/-- The weight at the odd index of a pair. -/
theorem eqAt_two_mul_add_one (r : E) (rs : List E) (w : ℕ) :
    eqAt (r :: rs) (2 * w + 1) = r * eqAt rs w := by
  rw [eqAt_cons, ite_eq_left (show (2 * w + 1) % 2 = 1 by omega), show (2 * w + 1) / 2 = w by omega]

/-- The equality weights sum to one. -/
theorem sum_eqAt : ∀ pt : List E, ∑ w ∈ range (2 ^ pt.length), eqAt pt w = 1
  | [] => by simp
  | r :: rs => by
    rw [List.length_cons, sum_cube_succ, ← sum_eqAt rs, sum_congr rfl fun w _ ↦ ?_]
    rw [eqAt_two_mul, eqAt_two_mul_add_one, ← add_mul, add_assoc,
      CharTwo.add_self_eq_zero, add_zero, one_mul]

/-! ## `eq_kernel` -/

/-- One more coordinate doubles the kernel: the old weights times `1 + r`, then times `r`. -/
theorem eqKernel_snoc (pt : List E) (r : E) :
    eqKernel (pt ++ [r]) = (eqKernel pt).map (· * (1 + r)) ++ (eqKernel pt).map (· * r) := by
  simp only [eqKernel, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem eqKernel_length (pt : List E) : (eqKernel pt).length = 2 ^ pt.length := by
  induction pt using List.reverseRecOn with
  | nil => rfl
  | append_singleton pt r ih =>
    rw [eqKernel_snoc, List.length_append, List.length_map, List.length_map, ih,
      List.length_append, List.length_singleton, pow_succ, mul_two]

/-- Scaling a list scales each entry, the default zero read as zero. -/
theorem getD_map_mul {R : Type*} [MulZeroClass R] (l : List R) (c : R) (w : ℕ) :
    (l.map (· * c)).getD w 0 = l.getD w 0 * c := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[w]? <;> simp

/-- **`eq_kernel` lists the equality weights.** -/
theorem eqKernel_getD (pt : List E) (w : ℕ) :
    (eqKernel pt).getD w 0 = if w < 2 ^ pt.length then eqAt pt w else 0 := by
  induction pt using List.reverseRecOn generalizing w with
  | nil =>
    rcases w with _ | w
    · rfl
    · simp [eqKernel, List.getD_eq_getElem?_getD]
  | append_singleton pt r ih =>
    have hlen := eqKernel_length pt
    have hp : 2 ^ (pt.length + 1) = 2 ^ pt.length + 2 ^ pt.length := by rw [pow_succ]; ring
    rw [eqKernel_snoc, List.length_append, List.length_singleton, eqAt_append]
    by_cases hw : w < 2 ^ pt.length
    · rw [List.getD_append _ _ _ _ (by simpa [hlen] using hw), getD_map_mul, ih,
        ite_eq_left hw, ite_eq_left (by omega), Nat.div_eq_of_lt hw]
      simp [eqAt]
    · rw [List.getD_append_right _ _ _ _ (by simp [hlen]; omega), List.length_map, hlen,
        getD_map_mul, ih]
      by_cases hw2 : w < 2 ^ (pt.length + 1)
      · have hq : w / 2 ^ pt.length = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
        rw [ite_eq_left hw2, hq, ite_eq_left (by omega), eqAt_mod pt w,
          eqAt_mod pt (w - 2 ^ pt.length), ← Nat.mod_eq_sub_mod (by omega)]
        simp [eqAt]
      · rw [ite_eq_right hw2, ite_eq_right (by omega), zero_mul]

/-! ## `dot` -/

/-- A left fold of `+` from `a` is `a` plus the sum. -/
theorem foldl_add_eq {M : Type*} [AddMonoid M] (l : List M) (a : M) :
    l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.sum_cons, add_assoc]

/-- A left fold of `*` from `a` is `a` times the product. -/
theorem foldl_mul_eq {M : Type*} [Monoid M] (l : List M) (a : M) :
    l.foldl (· * ·) a = a * l.prod := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.prod_cons, mul_assoc]

/-- `dot` sums over its left list's indices, the right list read as zero past its end. -/
theorem dot_eq_sum_left (a b : List E) :
    dot a b = ∑ j ∈ range a.length, a.getD j 0 * b.getD j 0 := by
  rw [dot, foldl_add_eq, zero_add]
  induction a generalizing b with
  | nil => simp
  | cons x a ih =>
    rcases b with _ | ⟨y, b⟩
    · simp
    · simp only [List.zipWith_cons_cons, List.sum_cons, List.length_cons, sum_range_succ',
        List.getD_cons_succ, List.getD_cons_zero]
      rw [ih b, add_comm]

/-- `dot` of two lists of the same length is the sum of the products. -/
theorem dot_eq_sum (a b : List E) (_h : a.length = b.length) :
    dot a b = ∑ j ∈ range a.length, a.getD j 0 * b.getD j 0 :=
  dot_eq_sum_left a b

/-- **The verifier's `dot(eq[:n], w)`**: the equality-weighted sum of `w`. -/
theorem dot_eqKernel (pt w : List E) (hn : w.length ≤ 2 ^ pt.length) :
    dot ((eqKernel pt).take w.length) w = ∑ j ∈ range w.length, eqAt pt j * w.getD j 0 := by
  rw [dot_eq_sum_left, List.length_take, eqKernel_length, min_eq_left hn]
  refine sum_congr rfl fun j hj ↦ ?_
  have hj' := mem_range.1 hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hj',
    ← List.getD_eq_getElem?_getD, eqKernel_getD, ite_eq_left (by omega)]

end
end LeanVM.Protocol.Verifier
