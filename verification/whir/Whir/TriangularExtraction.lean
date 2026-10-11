import Whir.ReedSolomonExtraction
import CompPoly.Univariate.ToPoly.Degree

/-! Executable coefficient recovery in a supplied triangular polynomial basis.
This avoids a classical inverse of the novel-basis linear equivalence.
`countedPeel` bounds peeling with a supplied basis; `countedPreparedPeel`
additionally executes and charges all recursive novel-basis, subspace,
evaluation and normalization preparation at each peeling step. Both have
checked value correspondence to the original implementation. Inverses have
an explicit implementation charge. Comparisons, allocation and copying are
separate from field arithmetic; this is not a machine-time certificate. -/
namespace Whir.TriangularExtraction
open CompPoly
open scoped BigOperators

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
omit [DecidableEq F]

/-- Strip the highest coefficient first. Output is descending; a single final reversal puts it in coefficient order. -/
def peel (basis : Nat → CPolynomial F) : Nat → CPolynomial F → List F
  | 0, _ => []
  | n + 1, p =>
    let currentBasis := basis n
    let coefficient := p.coeff n / currentBasis.coeff n
    coefficient :: peel basis n (p - CPolynomial.C coefficient * currentBasis)

def recover (basis : Nat → CPolynomial F) (size : Nat) (p : CPolynomial F) : Array F :=
  (peel basis size p).reverse.toArray

omit [DecidableEq F] in
/-- The basis hypotheses are algebraic triangularity, not an assumption that the decoder succeeds. -/
theorem peel_recovers (basis : Nat → CPolynomial F) (size : Nat) (a : Nat → F)
    (triangular : ∀ i j, i < size → i < j → (basis i).coeff j = 0)
    (diagonal : ∀ i < size, (basis i).coeff i ≠ 0) :
    peel basis size (∑ i ∈ Finset.range size, CPolynomial.C (a i) * basis i) =
      (List.range size).reverse.map a := by
  induction size with
  | zero => simp [peel]
  | succ n ih =>
    have lowerCoefficient :
        (∑ i ∈ Finset.range n, CPolynomial.C (a i) * basis i).coeff n = 0 := by
      rw [CPolynomial.coeff_finset_sum]
      apply Finset.sum_eq_zero
      intro i hi
      have lower := Finset.mem_range.mp hi
      rw [CPolynomial.coeff_C_mul, triangular i n (by omega) lower, mul_zero]
    have topCoefficient :
        (∑ i ∈ Finset.range (n + 1), CPolynomial.C (a i) * basis i).coeff n /
          (basis n).coeff n = a n := by
      rw [Finset.sum_range_succ, CPolynomial.coeff_add, lowerCoefficient,
        CPolynomial.coeff_C_mul, zero_add]
      exact mul_div_cancel_right₀ (a n) (diagonal n (by omega))
    rw [peel]
    rw [topCoefficient, Finset.sum_range_succ, add_sub_cancel_right]
    rw [ih (fun i j hi hij => triangular i j (by omega) hij)
      (fun i hi => diagonal i (by omega))]
    simp [List.range_succ, List.reverse_append]

theorem recover_recovers (basis : Nat → CPolynomial F) (size : Nat) (a : Nat → F)
    (triangular : ∀ i j, i < size → i < j → (basis i).coeff j = 0)
    (diagonal : ∀ i < size, (basis i).coeff i ≠ 0) :
    recover basis size (∑ i ∈ Finset.range size, CPolynomial.C (a i) * basis i) =
      ((List.range size).map a).toArray := by
  simp [recover, peel_recovers basis size a triangular diagonal, List.map_reverse]

/-- Executable preparation of exactly the additive subspace polynomials used by WHIR. -/
def subspace (v : Nat → F) : Nat → CPolynomial F
  | 0 => CPolynomial.X
  | n + 1 =>
    let previous := subspace v n
    previous * (previous + CPolynomial.C (previous.eval (v n)))

def normalized (v : Nat → F) (n : Nat) : CPolynomial F :=
  let p := subspace v n
  CPolynomial.C (p.eval (v n))⁻¹ * p

def novel (v : Nat → F) : Nat → Nat → CPolynomial F
  | 0, _ => 1
  | n + 1, j => if j < 2 ^ n then novel v n j
      else novel v n (j - 2 ^ n) * normalized v n

omit [DecidableEq F] in
theorem subspace_toPoly (v : Nat → F) (n : Nat) :
    (subspace v n).toPoly = AdditiveCode.subspace v n := by
  induction n with
  | zero => simp [subspace, AdditiveCode.subspace, CPolynomial.X_toPoly]
  | succ n ih =>
    simp [subspace, AdditiveCode.subspace, CPolynomial.toPoly_mul,
      CPolynomial.toPoly_add, CPolynomial.C_toPoly, CPolynomial.eval_toPoly, ih]

theorem normalized_toPoly (v : Nat → F) (n : Nat) :
    (normalized v n).toPoly = AdditiveCode.normalized v n := by
  simp [normalized, AdditiveCode.normalized, CPolynomial.toPoly_mul,
    CPolynomial.C_toPoly, CPolynomial.eval_toPoly, subspace_toPoly]

theorem novel_toPoly (v : Nat → F) (n j : Nat) :
    (novel v n j).toPoly = AdditiveCode.novel v n j := by
  induction n generalizing j with
  | zero => simp [novel, AdditiveCode.novel, CPolynomial.toPoly_one]
  | succ n ih =>
    simp only [novel, AdditiveCode.novel]
    split_ifs <;> simp [CPolynomial.toPoly_mul, normalized_toPoly, ih]

/-- The implemented triangular inverse recovers novel coefficients. The proof never enumerates field-valued witnesses. -/
theorem recover_novel [CharP F 2] (v : Nat → F) (n : Nat)
    (independent : AdditiveCode.Independent v n) (a : Nat → F) (p : CPolynomial F)
    (representation : p.toPoly = ∑ i ∈ Finset.range (2 ^ n),
      Polynomial.C (a i) * AdditiveCode.novel v n i) :
    recover (novel v n) (2 ^ n) p = ((List.range (2 ^ n)).map a).toArray := by
  have equal : p = ∑ i ∈ Finset.range (2 ^ n), CPolynomial.C (a i) * novel v n i := by
    apply CPolynomial.eq_iff_coeff.mpr
    intro j
    rw [CPolynomial.coeff_toPoly, CPolynomial.coeff_toPoly, representation]
    apply congrArg (fun q : Polynomial F => q.coeff j)
    rw [CPolynomial.toPoly_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [CPolynomial.toPoly_mul, CPolynomial.C_toPoly, novel_toPoly]
  rw [equal]
  apply recover_recovers
  · intro i j hi hij
    rw [CPolynomial.coeff_toPoly, novel_toPoly]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      ((AdditiveCode.novel_degree independent hi).1.trans_lt hij)
  · intro i hi
    rw [CPolynomial.coeff_toPoly, novel_toPoly]
    have degree := AdditiveCode.novel_degree independent hi
    have leading : (AdditiveCode.novel v n i).coeff i =
        (AdditiveCode.novel v n i).leadingCoeff := by
      simpa only [degree.1] using
        (Polynomial.coeff_natDegree (p := AdditiveCode.novel v n i))
    rw [leading]
    exact degree.2

omit [DecidableEq F] in
private theorem constant_mul_size (a : F) (p : CPolynomial F) (width : Nat)
    (support : p.val.size ≤ width) :
    (CPolynomial.C a * p).val.size ≤ width := by
  apply CPolynomial.mem_degreeLT_iff_size_le.mp
  apply CPolynomial.mem_degreeLT.mpr
  rw [CPolynomial.degree_lt_iff_coeff_zero]
  intro j hj
  rw [CPolynomial.coeff_C_mul,
    CPolynomial.coeff_eq_zero_of_size_le p (support.trans hj), mul_zero]

private theorem subtract_size (p q : CPolynomial F) (width : Nat)
    (left : p.val.size ≤ width) (right : q.val.size ≤ width) :
    (p - q).val.size ≤ width := by
  apply CPolynomial.mem_degreeLT_iff_size_le.mp
  apply CPolynomial.mem_degreeLT.mpr
  rw [CPolynomial.degree_lt_iff_coeff_zero]
  intro j hj
  rw [CPolynomial.coeff_sub,
    CPolynomial.coeff_eq_zero_of_size_le p (left.trans hj),
    CPolynomial.coeff_eq_zero_of_size_le q (right.trans hj), sub_self]

/-- Field-arithmetic instrumentation of actual triangular peeling, including
the naive convolution used even for constant multiplication. `inverseCost`
charges the supplied field implementation; for `E` the ladder costs 382
multiplications. Prepared basis generation, coefficient lookups, trimming,
allocation and list reversal are not included in this counter. -/
def countedPeel (inverseCost : Nat) (basis : Nat → CPolynomial F) :
    Nat → CPolynomial F → List F × Nat
  | 0, _ => ([], 0)
  | n + 1, p =>
    let currentBasis := basis n
    let coefficient := p.coeff n / currentBasis.coeff n
    let product := ReedSolomonExtraction.countedMul (CPolynomial.C coefficient) currentBasis
    let tail := countedPeel inverseCost basis n (p - product.1)
    (coefficient :: tail.1,
      inverseCost + 1 + product.2 +
        product.1.val.size + max p.val.size product.1.val.size + tail.2)

theorem countedPeel_value (inverseCost : Nat) (basis : Nat → CPolynomial F)
    (size : Nat) (p : CPolynomial F) :
    (countedPeel inverseCost basis size p).1 = peel basis size p := by
  induction size generalizing p with
  | zero => rfl
  | succ size ih =>
    simp [countedPeel, peel, ReedSolomonExtraction.countedMul_value, ih]

/-- A real quadratic coefficient-arithmetic bound for the peeling phase, not
merely a bound on its number of polynomial operations. All intermediate
supports are derived from these initial input and prepared-basis supports. -/
theorem countedPeel_cost (inverseCost : Nat) (basis : Nat → CPolynomial F)
    (size width : Nat) (p : CPolynomial F)
    (inputSupport : p.val.size ≤ width)
    (basisSupport : ∀ i < size, (basis i).val.size ≤ width) :
    (countedPeel inverseCost basis size p).2 ≤
      size * (4 * width + inverseCost + 2) := by
  induction size generalizing p with
  | zero => simp [countedPeel]
  | succ size ih =>
    let a := p.coeff size / (basis size).coeff size
    have basisSize := basisSupport size (by omega)
    have constantSize : (CPolynomial.C a).val.size ≤ 1 := by
      exact (CPolynomial.Raw.Trim.size_le_size _).trans_eq (by rfl)
    have productCost :
        (ReedSolomonExtraction.countedMul (CPolynomial.C a) (basis size)).2 ≤
          1 + 2 * width := by
      calc
        _ ≤ (CPolynomial.C a).val.size *
            ((CPolynomial.C a).val.size + 2 * (basis size).val.size) :=
          ReedSolomonExtraction.countedRawMul_cost _ _
        _ ≤ 1 * (1 + 2 * width) :=
          Nat.mul_le_mul constantSize
            (Nat.add_le_add constantSize (Nat.mul_le_mul_left 2 basisSize))
        _ = _ := by omega
    have productSize : (ReedSolomonExtraction.countedMul
        (CPolynomial.C a) (basis size)).1.val.size ≤ width := by
      rw [ReedSolomonExtraction.countedMul_value]
      exact constant_mul_size a (basis size) width basisSize
    have residualSize := subtract_size p
      (ReedSolomonExtraction.countedMul (CPolynomial.C a) (basis size)).1
      width inputSupport productSize
    have tail := ih (p - (ReedSolomonExtraction.countedMul
      (CPolynomial.C a) (basis size)).1) residualSize
      (fun i hi => basisSupport i (by omega))
    change inverseCost + 1 +
      (ReedSolomonExtraction.countedMul (CPolynomial.C a) (basis size)).2 +
      (ReedSolomonExtraction.countedMul (CPolynomial.C a) (basis size)).1.val.size +
      max p.val.size
        (ReedSolomonExtraction.countedMul (CPolynomial.C a) (basis size)).1.val.size +
      (countedPeel inverseCost basis size
        (p - (ReedSolomonExtraction.countedMul (CPolynomial.C a) (basis size)).1)).2 ≤ _
    rw [Nat.add_mul]
    omega

open ReedSolomonExtraction

/-- Preparation costs are executed inside the instrumented novel-basis
constructor; they are not supplied as an external or assumed budget. -/
def countedSubspace (v : Nat → F) : Nat → CPolynomial F × Nat
  | 0 => (CPolynomial.X, 0)
  | n + 1 =>
    let previous := countedSubspace v n
    let evaluation := countedEval previous.1 (v n)
    let added := countedAdd previous.1 (CPolynomial.C evaluation.1)
    let product := countedMul previous.1 added.1
    (product.1, previous.2 + evaluation.2 + added.2 + product.2)

theorem countedSubspace_value (v : Nat → F) (n : Nat) :
    (countedSubspace v n).1 = subspace v n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [countedSubspace, subspace, countedMul_value, countedAdd, countedEval_value, ih]

def countedNormalized (inverseCost : Nat) (v : Nat → F) (n : Nat) : CPolynomial F × Nat :=
  let p := countedSubspace v n
  let evaluation := countedEval p.1 (v n)
  let product := countedMul (CPolynomial.C evaluation.1⁻¹) p.1
  (product.1, p.2 + evaluation.2 + inverseCost + product.2)

theorem countedNormalized_value (inverseCost : Nat) (v : Nat → F) (n : Nat) :
    (countedNormalized inverseCost v n).1 = normalized v n := by
  simp [countedNormalized, normalized, countedMul_value, countedEval_value, countedSubspace_value]

def countedNovel (inverseCost : Nat) (v : Nat → F) : Nat → Nat → CPolynomial F × Nat
  | 0, _ => (1, 0)
  | n + 1, j =>
    if j < 2 ^ n then countedNovel inverseCost v n j else
      let previous := countedNovel inverseCost v n (j - 2 ^ n)
      let normalized := countedNormalized inverseCost v n
      let product := countedMul previous.1 normalized.1
      (product.1, previous.2 + normalized.2 + product.2)

theorem countedNovel_value (inverseCost : Nat) (v : Nat → F) (n j : Nat) :
    (countedNovel inverseCost v n j).1 = novel v n j := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    simp only [countedNovel, novel]
    split_ifs <;> simp [countedMul_value, countedNormalized_value, ih]

theorem subspace_support (v : Nat → F) (n : Nat) :
    (subspace v n).val.size ≤ 2 ^ (n + 1) := by
  induction n with
  | zero => exact Nat.le_refl 2
  | succ n ih =>
    have positive : 1 ≤ 2 ^ (n + 1) := Nat.one_le_pow _ _ (by omega)
    have added := (add_support (subspace v n)
      (CPolynomial.C ((subspace v n).eval (v n)))).trans
      (max_le ih ((constant_support _).trans positive))
    have product := mul_support (subspace v n)
      (subspace v n + CPolynomial.C ((subspace v n).eval (v n)))
    change _ ≤ 2 ^ (n + 1 + 1)
    rw [Nat.pow_succ]
    exact product.trans (by omega)

theorem normalized_support (v : Nat → F) (n : Nat) :
    (normalized v n).val.size ≤ 2 ^ (n + 1) := by
  exact (constant_mul_support _ _).trans (subspace_support v n)

theorem novel_support (v : Nat → F) (n j : Nat) :
    (novel v n j).val.size ≤ 2 ^ (n + 1) := by
  induction n generalizing j with
  | zero => exact (Nat.le_refl 1).trans (by norm_num)
  | succ n ih =>
    simp only [novel]
    split_ifs
    · exact (ih j).trans (Nat.pow_le_pow_right (by omega) (by omega))
    · exact (mul_support _ _).trans (by
        have left := ih (j - 2 ^ n)
        have right := normalized_support v n
        rw [Nat.pow_succ]
        omega)

def preparationUnit (width : Nat) : Nat := 8 * (width + 1) ^ 2

theorem countedSubspace_cost (v : Nat → F) (n width : Nat)
    (limit : 2 ^ (n + 1) ≤ width) :
    (countedSubspace v n).2 ≤ n * preparationUnit width := by
  induction n with
  | zero => simp [countedSubspace]
  | succ n ih =>
    have lowerLimit : 2 ^ (n + 1) ≤ width :=
      (Nat.pow_le_pow_right (by omega) (by omega)).trans limit
    have previousSupport : (countedSubspace v n).1.val.size ≤ width := by
      rw [countedSubspace_value]; exact (subspace_support v n).trans lowerLimit
    have positive : 1 ≤ width := (Nat.one_le_pow _ _ (by omega)).trans lowerLimit
    have addedSupport : ((countedSubspace v n).1 +
        CPolynomial.C ((countedSubspace v n).1.eval (v n))).val.size ≤ width :=
      (add_support _ _).trans (max_le previousSupport ((constant_support _).trans positive))
    have evaluationCost := countedEval_cost (countedSubspace v n).1 (v n) width previousSupport
    have productCost := countedMul_cost (countedSubspace v n).1
      ((countedSubspace v n).1 + CPolynomial.C ((countedSubspace v n).1.eval (v n)))
      width previousSupport addedSupport
    have previousCost := ih lowerLimit
    have addedCost : max (countedSubspace v n).1.val.size
        (CPolynomial.C ((countedSubspace v n).1.eval (v n))).val.size ≤ width :=
      max_le previousSupport ((constant_support _).trans positive)
    have step : (countedEval (countedSubspace v n).1 (v n)).2 +
        max (countedSubspace v n).1.val.size
          (CPolynomial.C ((countedSubspace v n).1.eval (v n))).val.size +
        (countedMul (countedSubspace v n).1
          ((countedSubspace v n).1 + CPolynomial.C ((countedSubspace v n).1.eval (v n)))).2 ≤
        preparationUnit width := by
      unfold preparationUnit
      nlinarith
    simp only [countedSubspace, countedAdd, countedEval_value]
    rw [Nat.add_mul]
    omega

theorem countedNormalized_cost (inverseCost : Nat) (v : Nat → F) (n width : Nat)
    (limit : 2 ^ (n + 1) ≤ width) :
    (countedNormalized inverseCost v n).2 ≤ (n + 1) * preparationUnit width + inverseCost := by
  have support : (countedSubspace v n).1.val.size ≤ width := by
    rw [countedSubspace_value]; exact (subspace_support v n).trans limit
  have positive : 1 ≤ width := (Nat.one_le_pow _ _ (by omega)).trans limit
  have previous := countedSubspace_cost v n width limit
  have evaluation := countedEval_cost (countedSubspace v n).1 (v n) width support
  have product := countedMul_cost
    (CPolynomial.C ((countedSubspace v n).1.eval (v n))⁻¹)
    (countedSubspace v n).1 width ((constant_support _).trans positive) support
  have step : (countedEval (countedSubspace v n).1 (v n)).2 +
      (countedMul (CPolynomial.C ((countedSubspace v n).1.eval (v n))⁻¹)
        (countedSubspace v n).1).2 ≤ preparationUnit width := by
    unfold preparationUnit; nlinarith
  simp only [countedNormalized, countedEval_value]
  rw [Nat.add_mul]
  omega

def novelBudget (inverseCost depth width : Nat) : Nat :=
  depth * ((depth + 1) * preparationUnit width + 3 * (width + 1) ^ 2 + inverseCost)

theorem countedNovel_cost (inverseCost : Nat) (v : Nat → F) (n j width : Nat)
    (limit : 2 ^ (n + 1) ≤ width) :
    (countedNovel inverseCost v n j).2 ≤ novelBudget inverseCost n width := by
  induction n generalizing j with
  | zero => simp [countedNovel, novelBudget]
  | succ n ih =>
    have lowerLimit : 2 ^ (n + 1) ≤ width :=
      (Nat.pow_le_pow_right (by omega) (by omega)).trans limit
    have previous := ih (j - 2 ^ n) lowerLimit
    have normalization := countedNormalized_cost inverseCost v n width lowerLimit
    have previousSupport : (countedNovel inverseCost v n (j - 2 ^ n)).1.val.size ≤ width := by
      rw [countedNovel_value]; exact (novel_support _ _ _).trans lowerLimit
    have normalizedSupport : (countedNormalized inverseCost v n).1.val.size ≤ width := by
      rw [countedNormalized_value]; exact (normalized_support _ _).trans lowerLimit
    have product := countedMul_cost (countedNovel inverseCost v n (j - 2 ^ n)).1
      (countedNormalized inverseCost v n).1 width previousSupport normalizedSupport
    have square : width ^ 2 ≤ (width + 1) ^ 2 := by nlinarith
    have positive : 0 ≤ preparationUnit width := Nat.zero_le _
    simp only [countedNovel]
    split_ifs
    · have smaller := ih j lowerLimit
      unfold novelBudget at smaller ⊢
      have budgetMono : (n + 1) * preparationUnit width + 3 * (width + 1) ^ 2 + inverseCost ≤
          (n + 1 + 1) * preparationUnit width + 3 * (width + 1) ^ 2 + inverseCost := by
        gcongr; omega
      exact smaller.trans (Nat.mul_le_mul (by omega) budgetMono)
    · unfold novelBudget at previous ⊢
      have budgetMono : (n + 1) * preparationUnit width + 3 * (width + 1) ^ 2 + inverseCost ≤
          (n + 1 + 1) * preparationUnit width + 3 * (width + 1) ^ 2 + inverseCost := by
        gcongr; omega
      have previousBudget := previous.trans (Nat.mul_le_mul_left n budgetMono)
      rw [Nat.add_mul]
      omega

/-- Prepare each novel polynomial exactly where the original peeling algorithm
calls `basis i`, and charge that preparation before the scalar division. -/
def countedPreparedPeel (inverseCost : Nat) (v : Nat → F) (depth : Nat) :
    Nat → CPolynomial F → List F × Nat
  | 0, _ => ([], 0)
  | size + 1, p =>
    let basis := countedNovel inverseCost v depth size
    let coefficient := p.coeff size / basis.1.coeff size
    let product := countedMul (CPolynomial.C coefficient) basis.1
    let tail := countedPreparedPeel inverseCost v depth size (p - product.1)
    (coefficient :: tail.1, basis.2 + inverseCost + 1 + product.2 +
      product.1.val.size + max p.val.size product.1.val.size + tail.2)

theorem countedPreparedPeel_value (inverseCost : Nat) (v : Nat → F) (depth size : Nat)
    (p : CPolynomial F) :
    (countedPreparedPeel inverseCost v depth size p).1 = peel (novel v depth) size p := by
  induction size generalizing p with
  | zero => rfl
  | succ size ih =>
    simp [countedPreparedPeel, peel, countedNovel_value, countedMul_value, ih]

theorem countedPreparedPeel_cost (inverseCost : Nat) (v : Nat → F) (depth size width : Nat)
    (p : CPolynomial F) (limit : 2 ^ (depth + 1) ≤ width) (support : p.val.size ≤ width) :
    (countedPreparedPeel inverseCost v depth size p).2 ≤
      size * (novelBudget inverseCost depth width + 4 * width + inverseCost + 2) := by
  induction size generalizing p with
  | zero => simp [countedPreparedPeel]
  | succ size ih =>
    let basis := countedNovel inverseCost v depth size
    let coefficient := p.coeff size / basis.1.coeff size
    have basisSupport : basis.1.val.size ≤ width := by
      rw [countedNovel_value]; exact (novel_support _ _ _).trans limit
    have basisCost := countedNovel_cost inverseCost v depth size width limit
    have productSupport : (countedMul (CPolynomial.C coefficient) basis.1).1.val.size ≤ width := by
      rw [countedMul_value]; exact (constant_mul_support _ _).trans basisSupport
    have productCost : (countedMul (CPolynomial.C coefficient) basis.1).2 ≤ 1 + 2 * width := by
      exact (countedRawMul_cost _ _).trans (by
        calc
          _ ≤ 1 * (1 + 2 * width) :=
            Nat.mul_le_mul (constant_support coefficient)
              (Nat.add_le_add (constant_support coefficient) (Nat.mul_le_mul_left 2 basisSupport))
          _ = _ := by omega)
    have residualSupport := subtract_size p
      (countedMul (CPolynomial.C coefficient) basis.1).1 width support productSupport
    have tail := ih (p - (countedMul (CPolynomial.C coefficient) basis.1).1) residualSupport
    change basis.2 + inverseCost + 1 + (countedMul (CPolynomial.C coefficient) basis.1).2 +
      (countedMul (CPolynomial.C coefficient) basis.1).1.val.size +
      max p.val.size (countedMul (CPolynomial.C coefficient) basis.1).1.val.size +
      (countedPreparedPeel inverseCost v depth size
        (p - (countedMul (CPolynomial.C coefficient) basis.1).1)).2 ≤ _
    change basis.2 ≤ _ at basisCost
    rw [Nat.add_mul]
    omega

end Whir.TriangularExtraction
