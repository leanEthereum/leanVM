import Whir.Algebra

namespace Whir.Completeness

open scoped BigOperators

variable {R : Type*} [CommRing R] [CharP R 2]

/-- A block of k consecutive sumcheck folds. The remaining m coordinates keep round order. -/
def foldBlock : (k m : ℕ) → (Cube (m + k) → R) → (Fin k → R) → Cube m → R
  | 0, _, f, _ => f
  | k + 1, m, f, r =>
    foldBlock k m (foldFirst (n := m + k) f (r 0)) (fun i => r i.succ)

def runBlock : (k m : ℕ) → (Cube (m + k) → R) → (Cube (m + k) → R) →
    (Fin k → R) → R → R
  | 0, _, _, _, _, claim => claim
  | k + 1, m, w, f, r, claim =>
    runBlock k m (foldFirst (n := m + k) w (r 0)) (foldFirst f (r 0))
      (fun i => r i.succ)
      (compactRound claim (roundConstant w f) (roundQuadratic w f) (r 0))

theorem block_complete (k m : ℕ) (w f : Cube (m + k) → R) (r : Fin k → R) :
    runBlock k m w f r (innerProduct w f) =
      innerProduct (foldBlock k m w r) (foldBlock k m f r) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [runBlock, foldBlock]
    rw [honest_round]
    exact ih _ _ _

omit [CharP R 2] in
/-- Fold/encode commutation for every block size, including uneven final blocks. -/
theorem foldBlock_linear {I : Type*} [Fintype I] (k m : ℕ)
    (a : I → R) (f : I → Cube (m + k) → R) (r : Fin k → R) (u : Cube m) :
    foldBlock k m (fun x => ∑ i, a i * f i x) r u =
      ∑ i, a i * foldBlock k m (f i) r u := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [foldBlock]
    have h : foldFirst (n := m + k) (fun x => ∑ i, a i * f i x) (r 0) =
        fun x => ∑ i, a i * foldFirst (f i) (r 0) x := by
      funext x
      simp only [foldFirst, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    exact (congrArg (fun g => foldBlock k m g (fun i => r i.succ) u) h).trans
      (ih (fun i => foldFirst (f i) (r 0)) (fun i => r i.succ))

/-- Residual, OOD, then column claims in the production batching order. -/
def nextWeight {m q : ℕ} (residual : Cube m → R) (z : Fin m → R)
    (columns : Fin q → Fin m → R) (lambda : R) : Cube m → R :=
  fun u => residual u + lambda * eqWeight z u +
    ∑ j, lambda ^ (j.val + 2) * tensorWeight (columns j) u

def nextClaim {m q : ℕ} (residual : R) (folded : Cube m → R) (z : Fin m → R)
    (columns : Fin q → Fin m → R) (lambda : R) : R :=
  residual + lambda * mle folded z +
    ∑ j, lambda ^ (j.val + 2) * novelEncode (columns j) folded

omit [CharP R 2] in
/-- Honest OOD and authenticated column answers preserve the residual invariant. -/
theorem next_claim_complete {m q : ℕ} (residual folded : Cube m → R)
    (z : Fin m → R) (columns : Fin q → Fin m → R) (lambda : R) :
    nextClaim (innerProduct residual folded) folded z columns lambda =
      innerProduct (nextWeight residual z columns lambda) folded := by
  simp only [nextClaim, nextWeight, mle, innerProduct, novelEncode_eq_innerProduct,
    innerProduct, add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · simp only [mul_assoc]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro u _
    ring

/-- Closing level: there is no OOD claim, so consistency powers start at one. -/
def finalWeight {m q : ℕ} (residual : Cube m → R)
    (columns : Fin q → Fin m → R) (lambda : R) : Cube m → R :=
  fun u => residual u + ∑ j, lambda ^ (j.val + 1) * tensorWeight (columns j) u

def finalClaim {m q : ℕ} (residual : R) (folded : Cube m → R)
    (columns : Fin q → Fin m → R) (lambda : R) : R :=
  residual + ∑ j, lambda ^ (j.val + 1) * novelEncode (columns j) folded

omit [CharP R 2] in
theorem final_claim_complete {m q : ℕ} (residual folded : Cube m → R)
    (columns : Fin q → Fin m → R) (lambda : R) :
    finalClaim (innerProduct residual folded) folded columns lambda =
      innerProduct (finalWeight residual columns lambda) folded := by
  simp only [finalClaim, finalWeight, innerProduct, novelEncode_eq_innerProduct,
    innerProduct, add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- An ideal interactive schedule. Column parameters are normalized subspace-polynomial
values. No field sampling, Merkle hashing or transcript serialization is implicit. -/
inductive Schedule (R : Type u) : ℕ → Type u
  | terminal {m : ℕ} (point : Fin m → R) : Schedule R m
  | closing {m q : ℕ} (point : Fin m → R)
      (columns : Fin q → Fin m → R) (lambda : R) : Schedule R m
  | level {k m q : ℕ} (folds : Fin k → R) (ood : Fin m → R)
      (columns : Fin q → Fin m → R) (lambda : R)
      (next : Schedule R m) : Schedule R (m + k)

/-- The residual claim is not recomputed from the witness: compact messages update it. -/
def replay : {n : ℕ} → Schedule R n → (Cube n → R) → (Cube n → R) → R → R × R
  | _, .terminal point, w, f, claim =>
    (honestSumcheck _ w f point claim, mle w point * mle f point)
  | _, .closing point columns lambda, w, f, claim =>
    let weight := finalWeight w columns lambda
    (honestSumcheck _ weight f point (finalClaim claim f columns lambda),
      mle weight point * mle f point)
  | _, .level (k := k) (m := m) folds ood columns lambda next, w, f, claim =>
    let folded := foldBlock k m f folds
    let residual := runBlock k m w f folds claim
    replay next (nextWeight (foldBlock k m w folds) ood columns lambda) folded
      (nextClaim residual folded ood columns lambda)

/-- Algebraic all-level completeness for any fold ladder and arbitrary challenges.
This theorem concerns honest algebraic messages, not Rust source-level refinement. -/
theorem all_levels_complete {n : ℕ} (schedule : Schedule R n)
    (w f : Cube n → R) :
    (replay schedule w f (innerProduct w f)).1 =
      (replay schedule w f (innerProduct w f)).2 := by
  induction schedule with
  | terminal point => exact honestSumcheck_complete _ w f point
  | closing point columns lambda =>
    simp only [replay, final_claim_complete]
    exact honestSumcheck_complete _ _ _ _
  | level folds ood columns lambda next ih =>
    simp only [replay, block_complete, next_claim_complete]
    exact ih _ _

end Whir.Completeness
