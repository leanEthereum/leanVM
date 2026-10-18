/-
  LeanVM.Guest.B1.Main.Multilinear

  Multilinear extensions over lists (V:687): splitting the table, scaling it, tensor products, the
  equality kernel, and the extension as a sum against the kernel.
-/

module

public import LeanVM.Guest.B1.Main.AggLoop99

/-!
# Multilinear extensions

`multilinearEval l p` folds `l` along `p`, the first coordinate pairing adjacent entries
(`mleFold`). It splits over blocks of `2^|p|` entries (`mleFold_append`), commutes with scaling
(`mleFold_map_mul`), and so evaluates a tensor `A ⊗ B` at `p ++ q` as the product of `B` at `p` and
`A` at `q` (`mle_tensor`). The equality kernel is such a tensor (`eqKernel_cons`), so its
extension is `eqEval` (`mle_eqKernel`), and an extension is the sum of the table against the
kernel of the point (`mle_eq_sum`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Folding pairs -/

theorem foldPairs_append (r : E) : ∀ (l1 l2 : List E), 2 ∣ l1.length →
    foldPairs r (l1 ++ l2) = foldPairs r l1 ++ foldPairs r l2
  | [], l2, _ => by cases l2 <;> rfl
  | [_], _, h => by simp at h
  | a :: b :: l1, l2, h => by
    simp only [List.cons_append, foldPairs, List.cons.injEq, true_and]
    exact foldPairs_append r l1 l2 (by simp at h; omega)

theorem length_foldPairs (r : E) : ∀ (l : List E), (foldPairs r l).length = l.length / 2
  | [] => by simp [foldPairs]
  | [_] => by simp [foldPairs]
  | a :: b :: l => by
    simp only [foldPairs, List.length_cons, length_foldPairs r l]; omega

theorem foldPairs_map_mul (r a : E) : ∀ (l : List E),
    foldPairs r (l.map (a * ·)) = (foldPairs r l).map (a * ·)
  | [] => rfl
  | [_] => rfl
  | x :: y :: l => by
    simp only [List.map_cons, foldPairs, foldPairs_map_mul r a l, List.cons.injEq, and_true]
    ring

/-- The fold of a table along a point. -/
def mleFold (p l : List E) : List E := p.foldl (fun cur r => foldPairs r cur) l

theorem mleFold_cons (r : E) (p l : List E) : mleFold (r :: p) l = mleFold p (foldPairs r l) := rfl

theorem mleFold_nil (l : List E) : mleFold [] l = l := rfl

theorem mleFold_append_point (p q l : List E) : mleFold (p ++ q) l = mleFold q (mleFold p l) := by
  simp [mleFold, List.foldl_append]

theorem multilinearEval_eq (l p : List E) : multilinearEval l p = (mleFold p l).headD 0 := rfl

theorem length_mleFold : ∀ (p l : List E), (mleFold p l).length = l.length / 2 ^ p.length
  | [], l => by simp [mleFold_nil]
  | r :: p, l => by
    rw [mleFold_cons, length_mleFold p, length_foldPairs, List.length_cons, pow_succ,
      Nat.div_div_eq_div_mul, mul_comm]

theorem mleFold_append : ∀ (p l1 l2 : List E), 2 ^ p.length ∣ l1.length →
    mleFold p (l1 ++ l2) = mleFold p l1 ++ mleFold p l2
  | [], _, _, _ => rfl
  | r :: p, l1, l2, h => by
    rw [List.length_cons, pow_succ] at h
    rw [mleFold_cons, mleFold_cons, mleFold_cons, foldPairs_append r l1 l2
      (Dvd.dvd.trans (Dvd.intro_left _ rfl) h), mleFold_append p]
    rw [length_foldPairs]
    obtain ⟨k, hk⟩ := h
    rw [hk, show 2 ^ p.length * 2 * k = (2 ^ p.length * k) * 2 by ring, Nat.mul_div_cancel _ (by omega)]
    exact Dvd.intro k rfl

theorem mleFold_map_mul (a : E) : ∀ (p l : List E), mleFold p (l.map (a * ·)) = (mleFold p l).map (a * ·)
  | [], _ => rfl
  | r :: p, l => by rw [mleFold_cons, mleFold_cons, foldPairs_map_mul, mleFold_map_mul a p]

theorem mleFold_nil_table : ∀ (p : List E), mleFold p [] = []
  | [] => rfl
  | r :: p => by rw [mleFold_cons, show foldPairs r [] = [] by simp [foldPairs], mleFold_nil_table p]

theorem flatMap_singleton_eq_map {α β : Type} (f : α → β) :
    ∀ (A : List α), (A.flatMap fun a => [f a]) = A.map f
  | [] => rfl
  | a :: A => by simp [flatMap_singleton_eq_map f A]

theorem mleFold_flatMap (p : List E) (g : E → List E) (hg : ∀ a, 2 ^ p.length ∣ (g a).length) :
    ∀ (A : List E), mleFold p (A.flatMap g) = A.flatMap fun a => mleFold p (g a)
  | [] => by simp [mleFold_nil_table]
  | a :: A => by
    rw [List.flatMap_cons, mleFold_append p _ _ (hg a), mleFold_flatMap p g hg A, List.flatMap_cons]

/-- A table of `2^|p|` entries folds to one. -/
theorem mleFold_single {p l : List E} (h : l.length = 2 ^ p.length) :
    mleFold p l = [multilinearEval l p] := by
  have hl := length_mleFold p l
  rw [h, Nat.div_self (by positivity)] at hl
  rw [multilinearEval_eq]
  match hm : mleFold p l, hl with
  | [m], _ => rfl

/-- **The extension of a tensor**: `A ⊗ B`, `B` the fast index, at `p ++ q` is `B` at `p` times `A`
at `q`. -/
theorem mle_tensor {A B p q : List E} (hB : B.length = 2 ^ p.length) (hA : A.length = 2 ^ q.length) :
    multilinearEval (A.flatMap fun a => B.map (a * ·)) (p ++ q) =
      multilinearEval A q * multilinearEval B p := by
  rw [multilinearEval_eq, mleFold_append_point,
    mleFold_flatMap p _ (fun a => by rw [List.length_map, hB])]
  simp only [mleFold_map_mul, mleFold_single hB, List.map_cons, List.map_nil]
  rw [flatMap_singleton_eq_map (fun a => a * multilinearEval B p),
    show (fun a => a * multilinearEval B p) = (multilinearEval B p * ·) from
      funext fun a => mul_comm a _, mleFold_map_mul, mleFold_single hA]
  simp [mul_comm]

/-! ## The equality kernel -/

theorem eqKernel_from (l : List E) : ∀ p : List E,
    p.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) l =
      (eqKernel p).flatMap fun w => l.map (w * ·) := by
  intro p
  induction p using List.reverseRecOn with
  | nil => simp [eqKernel]
  | append_singleton p x ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih, eqKernel_append_one,
      List.flatMap_append, List.map_flatMap, List.map_flatMap, List.flatMap_map, List.flatMap_map]
    have key : ∀ a : E, ((eqKernel p).flatMap fun w => (l.map (w * ·)).map (· * a)) =
        (eqKernel p).flatMap fun w => l.map ((w * a) * ·) := fun a =>
      List.flatMap_congr fun w _ => by
        rw [List.map_map]; exact List.map_congr_left fun b _ => by simp only [Function.comp]; ring
    rw [key, key]

theorem eqKernel_cons (r : E) (p : List E) :
    eqKernel (r :: p) = (eqKernel p).flatMap fun w => [1 + r, r].map (w * ·) := by
  rw [eqKernel, List.foldl_cons, eqKernel_from]
  simp

theorem foldl_mul_assoc (a b : E) : ∀ l : List E, l.foldl (· * ·) (a * b) = a * l.foldl (· * ·) b
  | [] => rfl
  | x :: l => by simp only [List.foldl_cons, mul_assoc, foldl_mul_assoc a (b * x) l]

theorem eqEval_cons (x y : E) (l m : List E) :
    eqEval (x :: l) (y :: m) = (1 + x + y) * eqEval l m := by
  simp only [eqEval, List.zipWith_cons_cons, List.foldl_cons, one_mul]
  rw [← foldl_mul_assoc, mul_one]

/-- **The extension of the equality kernel** of `c` at `q` is `eqEval c q`. -/
theorem mle_eqKernel : ∀ (c q : List E), c.length = q.length →
    multilinearEval (eqKernel c) q = eqEval c q
  | [], [], _ => rfl
  | c0 :: c, q0 :: q, h => by
    rw [eqEval_cons, eqKernel_cons, show q0 :: q = [q0] ++ q from rfl,
      mle_tensor (by rfl) (by rw [length_eqKernel]; simp at h; rw [h]),
      mle_eqKernel c q (by simpa using h)]
    simp only [multilinearEval, List.foldl_cons, List.foldl_nil,
      foldPairs, List.headD_cons]
    have h2 : c0 * q0 + c0 * q0 = 0 := e_add_self _
    rw [mul_comm]
    linear_combination (eqEval c q) * h2
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-! ## The extension as a sum -/

theorem sum_range_double (f : ℕ → E) : ∀ N : ℕ,
    ∑ i ∈ Finset.range (2 * N), f i = ∑ j ∈ Finset.range N, (f (2 * j) + f (2 * j + 1))
  | 0 => rfl
  | N + 1 => by
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      sum_range_double f N, Finset.sum_range_succ, add_assoc]

theorem foldPairs_getD (r : E) : ∀ (B : List E) (j : ℕ), 2 * j + 1 < B.length →
    (foldPairs r B).getD j 0 = B.getD (2 * j) 0 * (1 + r) + B.getD (2 * j + 1) 0 * r
  | x :: y :: B, 0, _ => by simp [foldPairs]
  | x :: y :: B, j + 1, h => by
    simp only [foldPairs, List.getD_cons_succ]
    rw [foldPairs_getD r B j (by simp at h; omega), show 2 * (j + 1) = 2 * j + 1 + 1 by ring,
      List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ]
  | [], _, h => by simp at h
  | [_], _, h => by simp at h

theorem flatMap_pair_getD (a b : E) : ∀ (A : List E) (j : ℕ), j < A.length →
    (A.flatMap fun w => [a, b].map (w * ·)).getD (2 * j) 0 = A.getD j 0 * a ∧
      (A.flatMap fun w => [a, b].map (w * ·)).getD (2 * j + 1) 0 = A.getD j 0 * b
  | w :: A, 0, _ => by simp
  | w :: A, j + 1, h => by
    have := flatMap_pair_getD a b A j (by simp at h; omega)
    simp only [List.flatMap_cons, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.getD_cons_succ, show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
    exact this
  | [], _, h => by simp at h

/-- **An extension is the sum of the table against the kernel** of the point. -/
theorem mle_eq_sum : ∀ (p B : List E), B.length = 2 ^ p.length →
    multilinearEval B p = ∑ i ∈ Finset.range (2 ^ p.length), B.getD i 0 * (eqKernel p).getD i 0
  | [], [b], _ => by simp [multilinearEval, eqKernel]
  | [], [], h => by simp at h
  | [], _ :: _ :: _, h => by simp at h
  | r :: p, B, h => by
    have hB : B.length = 2 * 2 ^ p.length := by rw [h, List.length_cons, pow_succ, mul_comm]
    rw [multilinearEval_eq, mleFold_cons, ← multilinearEval_eq,
      mle_eq_sum p (foldPairs r B) (by rw [length_foldPairs, hB]; omega), List.length_cons, pow_succ,
      mul_comm, sum_range_double]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < 2 ^ p.length := Finset.mem_range.mp hj
    obtain ⟨e0, e1⟩ := flatMap_pair_getD (1 + r) r (eqKernel p) j (by rw [length_eqKernel]; exact hj')
    rw [foldPairs_getD r B j (by omega), eqKernel_cons, e0, e1]
    ring

end
end LeanVM.Guest.B1.Main
