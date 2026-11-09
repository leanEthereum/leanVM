/-
  LeanVM.Guest.B1.Whir.InnerSpec

  The Spec's terminal weights as products: `inducedWeight` and `eqEval`.
-/

module

public import LeanVM.Guest.B1.Whir.ResQuery

/-!
# The terminal weights, unfolded

* `inducedWeight_eq`: `inducedWeight ml qs (powers λ q) x = Σ_i λ^i·Π_t (1 + x_t(1 + χ_t(q_i)·inv_t))`,
  `χ` the subspace walk (`chainF`) from the query's position, `inv` the roots' inverses;
* `induced_factor`: with the vanishing tables equal to the roots and their inverses, and every
  coefficient `x_t·inv_t` nonzero, a query's product is the scale `Π_t x_t·inv_t` times the
  guest's `residual_query` value (`residualProd`) at `d_t = (1 + x_t)/(x_t·inv_t)`;
* `eqEval_eq`: `eqEval z x = Π_t (1 + z_t + x_t)`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

/-- The subspace walk from coordinate `n` at `c`. -/
def chainF (roots : List E) : ℕ → E → ℕ → E
  | _, c, 0 => c
  | n, c, t + 1 => chainF roots (n + 1) (c ^ 2 + roots.getD n 0 * c) t

theorem chainF_succ (roots : List E) : ∀ (t n : ℕ) (c : E),
    chainF roots n c (t + 1) =
      chainF roots n c t ^ 2 + roots.getD (n + t) 0 * chainF roots n c t
  | 0, n, c => by simp [chainF]
  | t + 1, n, c => by
    show chainF roots (n + 1) (c ^ 2 + roots.getD n 0 * c) (t + 1) =
      chainF roots (n + 1) (c ^ 2 + roots.getD n 0 * c) t ^ 2 +
        roots.getD (n + (t + 1)) 0 * chainF roots (n + 1) (c ^ 2 + roots.getD n 0 * c) t
    rw [chainF_succ roots t (n + 1), show n + 1 + t = n + (t + 1) by ring]

/-- The walk is B1-a's `residualChain` on values agreeing with the roots. -/
theorem chainF_eq_residualChain (roots vals : List E) (c : E) :
    ∀ t, (∀ s < t, vals.getD s 0 = roots.getD s 0) →
      chainF roots 0 c t = residualChain vals c t
  | 0, _ => rfl
  | t + 1, h => by
    rw [chainF_succ, residualChain, chainF_eq_residualChain roots vals c t
      (fun s hs ↦ h s (by omega)), Nat.zero_add, ← h t (by omega)]
    ring

/-- The roots' inverses, as `inducedWeight` takes them. -/
def invsOf (ml : ℕ) : List E := (subspaceRoots ml).map fun v ↦ if v = 0 then 0 else v⁻¹

theorem zipIdx_foldl_prod (roots invs : List E) : ∀ (l : List E) (n : ℕ) (w c : E),
    (l.zipIdx n).foldl (fun (acc : E × E) (q : E × ℕ) ↦
        (acc.1 * (1 + q.1 * (1 + acc.2 * invs.getD q.2 0)), acc.2 ^ 2 + roots.getD q.2 0 * acc.2))
      (w, c) =
      (w * ∏ t ∈ Finset.range l.length,
        (1 + l.getD t 0 * (1 + chainF roots n c t * invs.getD (n + t) 0)),
       chainF roots n c l.length)
  | [], n, w, c => by simp [chainF]
  | a :: l, n, w, c => by
    rw [List.zipIdx_cons, List.foldl_cons, zipIdx_foldl_prod roots invs l (n + 1)]
    simp only [List.length_cons, Finset.prod_range_succ', List.getD_cons_succ,
      List.getD_cons_zero, chainF, Nat.add_zero, Prod.mk.injEq, and_true]
    simp only [show ∀ t, n + 1 + t = n + (t + 1) from fun t ↦ by ring]
    ring

theorem zip_foldl_sum (g : E → ℕ → E) : ∀ (ws : List E) (qs : List ℕ) (a : E),
    (List.zip ws qs).foldl (fun tot (p : E × ℕ) ↦ tot + g p.1 p.2) a =
      a + ∑ i ∈ Finset.range (min ws.length qs.length), g (ws.getD i 0) (qs.getD i 0)
  | [], _, a => by simp
  | _ :: _, [], a => by simp
  | w :: ws, q :: qs, a => by
    rw [List.zip_cons_cons, List.foldl_cons, zip_foldl_sum g ws qs]
    simp only [List.length_cons, Nat.add_min_add_right, Finset.sum_range_succ',
      List.getD_cons_succ, List.getD_cons_zero]
    ring

theorem powers_length (lam : E) : ∀ (n : ℕ) (acc : E), (powersFrom acc lam n).length = n
  | 0, _ => rfl
  | n + 1, acc => by simp [powersFrom, powers_length lam n]

theorem powersFrom_getD (lam : E) : ∀ (n : ℕ) (acc : E) (i : ℕ), i < n →
    (powersFrom acc lam n).getD i 0 = acc * lam ^ i
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, acc, 0, _ => by simp [powersFrom]
  | n + 1, acc, i + 1, h => by
    rw [powersFrom, List.getD_cons_succ, powersFrom_getD lam n _ i (by omega)]
    ring

/-- A query's term of `inducedWeight`. -/
def iwTerm (ml : ℕ) (x : List E) (w : E) (q : ℕ) : E :=
  ((x.zipIdx 0).foldl (fun (acc : E × E) (q : E × ℕ) ↦
    (acc.1 * (1 + q.1 * (1 + acc.2 * (invsOf ml).getD q.2 0)),
      acc.2 ^ 2 + (subspaceRoots ml).getD q.2 0 * acc.2)) (w, eOfNat q)).1

/-- **`inducedWeight`, unfolded.** -/
theorem inducedWeight_eq (ml : ℕ) (qs : List ℕ) (lam : E) (x : List E) :
    inducedWeight ml qs (powers lam qs.length) x =
      ∑ i ∈ Finset.range qs.length, lam ^ i * ∏ t ∈ Finset.range x.length,
        (1 + x.getD t 0 * (1 + chainF (subspaceRoots ml) 0 (eOfNat (qs.getD i 0)) t *
          (invsOf ml).getD t 0)) := by
  have e : inducedWeight ml qs (powers lam qs.length) x =
      (List.zip (powers lam qs.length) qs).foldl (fun tot (p : E × ℕ) ↦ tot +
        iwTerm ml x p.1 p.2) 0 := rfl
  rw [e, zip_foldl_sum, zero_add, powers, powers_length, min_self]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [iwTerm, zipIdx_foldl_prod, powersFrom_getD lam _ _ _ (Finset.mem_range.mp hi), one_mul]
  simp only [Nat.zero_add]

/-- **A query's product, factored** onto the guest's `residual_query`. -/
theorem induced_factor {ml vo : ℕ} {X : ℕ → E} (q : E)
    (hval : ∀ t < ml, word (vanishVal (vo + t)) 0 0 = (subspaceRoots ml).getD t 0)
    (hinv : ∀ t < ml, word (vanishInv (vo + t)) 0 0 = (invsOf ml).getD t 0)
    (hne : ∀ t < ml, X t * word (vanishInv (vo + t)) 0 0 ≠ 0) :
    ∏ t ∈ Finset.range ml, (1 + X t * (1 + chainF (subspaceRoots ml) 0 q t * (invsOf ml).getD t 0)) =
      (∏ t ∈ Finset.range ml, (X t * word (vanishInv (vo + t)) 0 0)) *
        residualProd (osVals vo ml) q (fun t ↦ (1 + X t) / (X t * word (vanishInv (vo + t)) 0 0))
          ml := by
  rw [← residual_prod (osVals vo ml) q X (fun t ↦ word (vanishInv (vo + t)) 0 0) ml hne]
  refine Finset.prod_congr rfl fun t ht ↦ ?_
  have ht' := Finset.mem_range.mp ht
  rw [hinv t ht', chainF_eq_residualChain (subspaceRoots ml) (osVals vo ml) q t (fun s hs ↦ by
    rw [osVals_getD (by omega), hval s (by omega)])]

/-- **`eqEval`, unfolded.** -/
theorem eqEval_eq : ∀ (z x : List E),
    eqEval z x = ∏ t ∈ Finset.range (min z.length x.length), (1 + z.getD t 0 + x.getD t 0) := by
  have key : ∀ (z x : List E) (a : E),
      (List.zipWith (fun x z ↦ 1 + x + z) z x).foldl (· * ·) a =
        a * ∏ t ∈ Finset.range (min z.length x.length), (1 + z.getD t 0 + x.getD t 0) := by
    intro z
    induction z with
    | nil => intro x a; simp
    | cons b z ih =>
      intro x a
      rcases x with _ | ⟨y, x⟩
      · simp
      · rw [List.zipWith_cons_cons, List.foldl_cons, ih]
        simp only [List.length_cons, Nat.add_min_add_right, Finset.prod_range_succ',
          List.getD_cons_succ, List.getD_cons_zero]
        ring
  intro z x
  rw [eqEval, key, one_mul]

end
end LeanVM.Guest.B1.Whir
