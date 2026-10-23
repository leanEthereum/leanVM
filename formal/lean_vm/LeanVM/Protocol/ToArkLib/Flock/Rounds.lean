/-
  LeanVM.Protocol.ToArkLib.Flock.Rounds

  The honest round polynomials of the two quadratic sumchecks of a Flock argument: the
  normalized zerocheck round on `A · B - C` binding the lowest variable first, and the plain
  lincheck round on a sum of products binding the highest variable first. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Flock.Tables
public import LeanVM.Protocol.ToArkLib.SumcheckRound
public import LeanVM.Protocol.ToCompPoly.HighSum
public import LeanVM.Protocol.ToCompPoly.PartialSum

/-!
# Quadratic round polynomials

Both sumchecks of a Flock argument have a summand of degree two in each variable: the
zerocheck's `g(v) = Ã(v) · B̃(v) - C̃(v)` against `eq(r, ·)` (a normalized round, the equality
factor outside the message), and the lincheck's `Σ_i M̃_i(v) · Z̃_i(v)` with unit weights (a plain
round). The honest round message is the three coefficients, low degree first, of the running
claim with the next coordinate left free: every extension is affine in it (`evalMle_set`), so the
coefficients are sums of products of the values at `0` and `1`.

* `normRound`, `evaluate_normRound`: the zerocheck round binding coordinate `j`; its message
  evaluates to the next partial sum `partialSum g r (j + 1) (c.push X)`, and
  `weightedSum_normRound` is the check `(1 - r_j) · h(0) + r_j · h(1)` against the running claim.
* `highRound`, `evaluate_highRound`: the lincheck round binding coordinate `m - 1 - j`; its
  message evaluates to `highSum (linFun M Z) (j + 1) (c.push X)`, and `weightedSum_highRound` is
  the check `h(0) + h(1)`.

Nothing here transcribes a source.
-/

namespace LeanVM.Protocol

namespace Flock

open CompPoly CMlPolynomialEval SumcheckRound

@[expose] public section

variable {F : Type} [Field F]

/-- `Σ_{i < 3} q_i X^i` for the message `#v[q₀, q₁, q₂]`. -/
theorem evaluate_three (q₀ q₁ q₂ X : F) :
    evaluate 2 (#v[q₀, q₁, q₂] : Message F 2) X = q₀ + q₁ * X + q₂ * X ^ 2 := by
  simp [evaluate, Fin.sum_univ_three]

/-! ## The zerocheck round -/

/-- The zerocheck summand on three tables: `Ã · B̃ - C̃`. -/
def prodSub {n : ℕ} (tA tB tC : CMlPolynomialEval F n) (v : Vector F n) : F :=
  evalMle tA v * evalMle tB v - evalMle tC v

/-- The honest normalized round message binding coordinate `j`, the first `j` coordinates fixed
to `c`: the three coefficients of `X ↦ Σ_b eq(r_{>j}, b) · g(c, X, b)`. -/
def normRound {n : ℕ} (tA tB tC : CMlPolynomialEval F n) (r : Vector F n) (j : ℕ)
    (c : Vector F j) : Message F 2 :=
  if hj : j < n then
    let L := lagrangeBasis (r.drop (j + 1))
    let pt := fun (b : Fin (2 ^ (n - (j + 1)))) (X : F) ↦
      (fixLow hj (c.push 0) (boolVec b)).set j X hj
    let e := fun (t : CMlPolynomialEval F n) (b : Fin (2 ^ (n - (j + 1)))) (X : F) ↦
      evalMle t (pt b X)
    #v[∑ b, L[b] * (e tA b 0 * e tB b 0 - e tC b 0),
      ∑ b, L[b] * (e tA b 0 * (e tB b 1 - e tB b 0) + (e tA b 1 - e tA b 0) * e tB b 0 -
        (e tC b 1 - e tC b 0)),
      ∑ b, L[b] * ((e tA b 1 - e tA b 0) * (e tB b 1 - e tB b 0))]
  else 0

/-- The normalized round message evaluates to the next partial sum. -/
theorem evaluate_normRound {n : ℕ} (tA tB tC : CMlPolynomialEval F n) (r : Vector F n) {j : ℕ}
    (hj : j < n) (c : Vector F j) (X : F) :
    evaluate 2 (normRound tA tB tC r j c) X =
      partialSum (prodSub tA tB tC) r (j + 1) (c.push X) := by
  have hj' : j + 1 ≤ n := hj
  rw [normRound, dite_eq_left hj]
  dsimp only
  rw [evaluate_three, partialSum, dite_eq_left hj', evalMle_eq_sum, Finset.sum_mul,
    Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  have hrt : (restrictTable (prodSub tA tB tC) hj' (c.push X))[b] =
      prodSub tA tB tC (fixLow hj' (c.push X) (boolVec b)) := by
    simp [restrictTable]
  have hset : ∀ t : CMlPolynomialEval F n, evalMle t (fixLow hj' (c.push X) (boolVec b)) =
      (1 - X) * evalMle t ((fixLow hj (c.push 0) (boolVec b)).set j 0 hj) +
        X * evalMle t ((fixLow hj (c.push 0) (boolVec b)).set j 1 hj) := fun t ↦ by
    rw [fixLow_push_set hj]
    exact evalMle_set t _ hj X
  rw [hrt, prodSub, hset, hset, hset]
  ring

/-- The normalized round's check: the weighted sum of the honest message over `0, 1` with the
weights `1 - r_j, r_j` is the running claim. -/
theorem weightedSum_normRound {X : Type} {n : ℕ} (tA tB tC : CMlPolynomialEval F n)
    (pt : X → Vector F n) (x : X) {j : ℕ} (hj : j < n) (c : Vector F j) :
    weightedSum 2 (normalizedWeights pt x j) (normRound tA tB tC (pt x) j c) =
      partialSum (prodSub tA tB tC) (pt x) j c := by
  rw [normalizedWeights, dite_eq_left hj, weightedSum, partialSum_split _ _ hj]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    evaluate_normRound tA tB tC (pt x) hj]

/-! ## The lincheck round -/

/-- The honest plain round message binding coordinate `m - 1 - j`, the last `j` coordinates fixed
to the reversed `c`: the three coefficients of `X ↦ Σ_b Σ_i M̃_i(b, X, c) · Z̃_i(b, X, c)`. -/
def highRound {s m : ℕ} (M Z : CMlPolynomialEval F (s + m)) (j : ℕ) (c : Vector F j) :
    Message F 2 :=
  if hj : j < m then
    let pt := fun (b : Fin (2 ^ (m - (j + 1)))) (X : F) ↦
      (highFix hj (c.push 0) (boolVec b)).set (m - (j + 1)) X (by omega)
    let e := fun (t : CMlPolynomialEval F (s + m)) (i : Fin (2 ^ s))
      (b : Fin (2 ^ (m - (j + 1)))) (X : F) ↦ evalMle (sliceLow t i) (pt b X)
    #v[∑ b, ∑ i, e M i b 0 * e Z i b 0,
      ∑ b, ∑ i, (e M i b 0 * (e Z i b 1 - e Z i b 0) + (e M i b 1 - e M i b 0) * e Z i b 0),
      ∑ b, ∑ i, (e M i b 1 - e M i b 0) * (e Z i b 1 - e Z i b 0)]
  else 0

/-- The plain round message evaluates to the next high sum. -/
theorem evaluate_highRound {s m : ℕ} (M Z : CMlPolynomialEval F (s + m)) {j : ℕ} (hj : j < m)
    (c : Vector F j) (X : F) :
    evaluate 2 (highRound M Z j c) X = highSum (linFun M Z) (j + 1) (c.push X) := by
  have hj' : j + 1 ≤ m := hj
  have hk : m - (j + 1) < m := by omega
  rw [highRound, dite_eq_left hj]
  dsimp only
  rw [evaluate_three, highSum, dite_eq_left hj', Finset.sum_mul, Finset.sum_mul,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  have hset : ∀ t : CMlPolynomialEval F m, evalMle t (highFix hj' (c.push X) (boolVec b)) =
      (1 - X) * evalMle t ((highFix hj (c.push 0) (boolVec b)).set (m - (j + 1)) 0 hk) +
        X * evalMle t ((highFix hj (c.push 0) (boolVec b)).set (m - (j + 1)) 1 hk) :=
    fun t ↦ by
      rw [highFix_push_set hj]
      exact evalMle_set t _ hk X
  rw [linFun, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hset, hset]
  ring

/-- The plain round's check: the sum of the honest message at `0` and `1` is the running
claim. -/
theorem weightedSum_highRound {s m : ℕ} (M Z : CMlPolynomialEval F (s + m)) {j : ℕ} (hj : j < m)
    (c : Vector F j) :
    weightedSum 2 [(0, 1), (1, 1)] (highRound M Z j c) = highSum (linFun M Z) j c := by
  rw [weightedSum, highSum_split _ hj]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul,
    evaluate_highRound M Z hj]

end

end Flock

end LeanVM.Protocol
