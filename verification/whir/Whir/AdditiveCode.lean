import Whir.CodingBounds
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.Algebra.CharP.Two

/-! Annex D's dense additive encoder. Independence is a binary-span condition,
not a coding-theoretic assumption. Optimized NTT refinement is separate. -/
namespace Whir.AdditiveCode
open Polynomial
open scoped BigOperators
noncomputable section

variable {F : Type*} [Field F]

/-- The unnormalized recursion used by `Concrete.subspaceRoots`. -/
def subspace (v : ℕ → F) : ℕ → F[X]
  | 0 => X
  | n + 1 => subspace v n * (subspace v n + C ((subspace v n).eval (v n)))

theorem subspace_degree (v : ℕ → F) (n : ℕ) :
    (subspace v n).natDegree = 2^n ∧ (subspace v n).Monic := by
  induction n with
  | zero => simp [subspace]
  | succ n ih =>
    have hp : 0 < (subspace v n).natDegree := by rw [ih.1]; positivity
    have hm : (subspace v n + C ((subspace v n).eval (v n))).Monic :=
      ih.2.add_of_left (degree_C_le.trans_lt (by
        rw [degree_eq_natDegree ih.2.ne_zero]
        exact_mod_cast hp))
    constructor
    · rw [subspace, ih.2.natDegree_mul hm, natDegree_add_C, ih.1, pow_succ]
      omega
    · exact ih.2.mul hm

/-- Binary span of the first `n` vectors, including zero. -/
def binarySpan (v : ℕ → F) : ℕ → Set F
  | 0 => {0}
  | n + 1 => binarySpan v n ∪ (fun x => x + v n) '' binarySpan v n

/-- Each new vector lies outside the binary span of its predecessors. -/
def Independent (v : ℕ → F) (n : ℕ) : Prop :=
  ∀ i < n, v i ∉ binarySpan v i

section CharTwo
variable [CharP F 2]

theorem subspace_add (v : ℕ → F) (n : ℕ) (x y : F) :
    (subspace v n).eval (x+y) = (subspace v n).eval x + (subspace v n).eval y := by
  induction n with
  | zero => simp [subspace]
  | succ n ih =>
    simp only [subspace, eval_mul, eval_add, eval_C, ih]
    ring_nf
    simp [CharTwo.two_eq_zero]

/-- Additivity as a polynomial identity, not merely on field-valued points. -/
theorem subspace_comp_add (v : ℕ → F) (n : ℕ) (p q : F[X]) :
    (subspace v n).comp (p+q) =
      (subspace v n).comp p + (subspace v n).comp q := by
  induction n with
  | zero => simp [subspace]
  | succ n ih =>
    simp only [subspace, mul_comp, add_comp, C_comp, ih]
    ring_nf
    simp [CharTwo.two_eq_zero]

omit [CharP F 2] in
@[simp] theorem subspace_zero (v : ℕ → F) (n : ℕ) :
    (subspace v n).eval 0 = 0 := by
  induction n with
  | zero => simp [subspace]
  | succ n ih => simp [subspace, ih]

/-- The recursion has exactly the intended binary-subspace roots, even before
independence is imposed. -/
theorem subspace_roots (v : ℕ → F) (n : ℕ) (x : F) :
    (subspace v n).eval x = 0 ↔ x ∈ binarySpan v n := by
  induction n generalizing x with
  | zero => simp [subspace, binarySpan]
  | succ n ih =>
    simp only [subspace, eval_mul, eval_add, eval_C, mul_eq_zero,
      binarySpan, Set.mem_union, Set.mem_image]
    rw [ih]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · right
        refine ⟨x + v n, (ih _).mp ?_, ?_⟩
        · rw [subspace_add]; exact h
        · simp [add_assoc, CharTwo.add_self_eq_zero]
    · rintro (h | ⟨y, hy, rfl⟩)
      · exact Or.inl h
      · right
        rw [subspace_add, (ih _).mpr hy, zero_add, CharTwo.add_self_eq_zero]

theorem root_ne_zero {v : ℕ → F} {n i : ℕ} (h : Independent v n) (hi : i < n) :
    (subspace v i).eval (v i) ≠ 0 := by
  exact fun hz => h i hi ((subspace_roots v i (v i)).mp hz)

/-- Finite enumeration of exactly the binary span. -/
def binaryPoints [DecidableEq F] (v : ℕ → F) : ℕ → Finset F
  | 0 => {0}
  | n+1 => binaryPoints v n ∪ (binaryPoints v n).image (fun x => x + v n)

omit [CharP F 2] in
@[simp] theorem mem_binaryPoints [DecidableEq F] (v : ℕ → F) (n : ℕ) (x : F) :
    x ∈ binaryPoints v n ↔ x ∈ binarySpan v n := by
  induction n generalizing x with
  | zero => simp [binaryPoints, binarySpan]
  | succ n ih => simp [binaryPoints, binarySpan, ih]

theorem binaryPoints_disjoint [DecidableEq F] {v : ℕ → F} {n : ℕ}
    (h : Independent v (n+1)) :
    Disjoint (binaryPoints v n) ((binaryPoints v n).image (fun x => x + v n)) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  obtain ⟨y, hy', rfl⟩ := Finset.mem_image.mp hy
  have hz := (subspace_roots v n (y + v n)).mpr ((mem_binaryPoints v n _).mp hx)
  rw [subspace_add, (subspace_roots v n y).mpr ((mem_binaryPoints v n _).mp hy'),
    zero_add] at hz
  exact root_ne_zero h (Nat.lt_succ_self n) hz

theorem binaryPoints_card [DecidableEq F] {v : ℕ → F} {n : ℕ}
    (h : Independent v n) : (binaryPoints v n).card = 2^n := by
  induction n with
  | zero => simp [binaryPoints]
  | succ n ih =>
    rw [binaryPoints, Finset.card_union_of_disjoint (binaryPoints_disjoint h),
      Finset.card_image_of_injective _ (add_left_injective (v n)),
      ih (fun i hi => h i (by omega)), pow_succ]
    omega

/-- The recursion is exactly Annex D's product over the binary subspace. -/
theorem subspace_eq_product [DecidableEq F] {v : ℕ → F} {n : ℕ}
    (h : Independent v n) :
    subspace v n = ∏ x ∈ binaryPoints v n, (X + C x) := by
  induction n with
  | zero => simp [subspace, binaryPoints]
  | succ n ih =>
    have ih' := ih (fun i hi => h i (by omega))
    rw [binaryPoints, Finset.prod_union (binaryPoints_disjoint h)]
    rw [Finset.prod_image (fun a _ b _ hab => add_right_cancel hab)]
    have hshift : (∏ x ∈ binaryPoints v n, (X + C (x + v n))) =
        (subspace v n).comp (X + C (v n)) := by
      rw [ih']
      simp only [prod_comp, add_comp, X_comp, C_comp, map_add]
      apply Finset.prod_congr rfl
      intro x _
      ring
    rw [hshift, subspace_comp_add, comp_X, comp_C, ← ih', subspace]

end CharTwo

/-- Division by the nonzero diagonal value normalizes each additive factor. -/
def normalized (v : ℕ → F) (i : ℕ) : F[X] :=
  C ((subspace v i).eval (v i))⁻¹ * subspace v i

theorem normalized_degree {v : ℕ → F} {n i : ℕ} [CharP F 2]
    (h : Independent v n) (hi : i < n) :
    (normalized v i).natDegree = 2^i ∧ (normalized v i).leadingCoeff ≠ 0 := by
  have hr := root_ne_zero h hi
  have hp := subspace_degree v i
  constructor
  · simp [normalized, natDegree_mul (C_ne_zero.mpr (inv_ne_zero hr)) hp.2.ne_zero, hp.1]
  · simp [normalized, leadingCoeff_mul, hp.2.leadingCoeff, hr]

@[simp] theorem normalized_at_basis {v : ℕ → F} {n i : ℕ} [CharP F 2]
    (h : Independent v n) (hi : i < n) : (normalized v i).eval (v i) = 1 := by
  simp [normalized, root_ne_zero h hi]

/-- Low-bit-first product basis; the upper half appends the new factor, exactly
as the dense column loop does. Only indices below `2^n` are used. -/
def novel (v : ℕ → F) : ℕ → ℕ → F[X]
  | 0, _ => 1
  | n + 1, j => if j < 2^n then novel v n j
      else novel v n (j - 2^n) * normalized v n

theorem novel_degree {v : ℕ → F} [CharP F 2] {n : ℕ}
    (h : Independent v n) {j : ℕ} (hj : j < 2^n) :
    (novel v n j).natDegree = j ∧ (novel v n j).leadingCoeff ≠ 0 := by
  induction n generalizing j with
  | zero => have : j = 0 := by simpa using hj
            subst j
            simp [novel]
  | succ n ih =>
    have hprev : Independent v n := fun i hi => h i (by omega)
    have hn := normalized_degree h (Nat.lt_succ_self n)
    simp only [novel]
    split_ifs with hj'
    · exact ih hprev hj'
    · have hlt : j - 2^n < 2^n := by rw [pow_succ] at hj; omega
      have hb := ih hprev hlt
      constructor
      · rw [natDegree_mul (leadingCoeff_ne_zero.mp hb.2) (leadingCoeff_ne_zero.mp hn.2),
          hb.1, hn.1]
        omega
      · rw [leadingCoeff_mul]; exact mul_ne_zero hb.2 hn.2

/-- Extend the finite triangular family by monomials to use Mathlib's
polynomial-sequence basis theorem. The extension does not alter the code. -/
noncomputable def sequence (v : ℕ → F) [CharP F 2] (n : ℕ) (h : Independent v n) :
    Polynomial.Sequence F where
  elems' j := if j < 2^n then novel v n j else X^j
  degree_eq' j := by
    split_ifs with hj
    · exact (degree_eq_iff_natDegree_eq (leadingCoeff_ne_zero.mp (novel_degree h hj).2)).mpr
        (novel_degree h hj).1
    · simp

/-- The actual coefficient-to-polynomial map. -/
def polynomial (v : ℕ → F) (n : ℕ) (a : Fin (2^n) → F) : F[X] :=
  ∑ j, a j • novel v n j

theorem novel_independent {v : ℕ → F} [CharP F 2] {n : ℕ}
    (h : Independent v n) :
    LinearIndependent F (fun j : Fin (2^n) => novel v n j) := by
  simpa [sequence, Function.comp_def] using
    (sequence v n h).linearIndependent.comp (fun j : Fin (2^n) => j.val) Fin.val_injective

theorem polynomial_injective {v : ℕ → F} [CharP F 2] {n : ℕ}
    (h : Independent v n) : Function.Injective (polynomial v n) := by
  intro a b hab
  have hz : ∑ j, (a j - b j) • novel v n j = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hab
  have he := Fintype.linearIndependent_iff.mp (novel_independent h) _ hz
  funext j
  exact sub_eq_zero.mp (he j)

theorem polynomial_degree_lt {v : ℕ → F} [CharP F 2] {n : ℕ}
    (h : Independent v n) (a : Fin (2^n) → F) :
    (polynomial v n a).degree < 2^n := by
  have he : (2 : WithBot ℕ)^n = ((2^n : ℕ) : WithBot ℕ) := by norm_cast
  rw [he, ← mem_degreeLT]
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  rw [mem_degreeLT,
    degree_eq_natDegree (leadingCoeff_ne_zero.mp (novel_degree h j.isLt).2),
    (novel_degree h j.isLt).1]
  exact_mod_cast j.isLt

/-- Surjectivity onto precisely the RS polynomial space, not a larger space. -/
theorem polynomial_surjective {v : ℕ → F} [CharP F 2] {n : ℕ}
    (h : Independent v n) (p : F[X]) :
    (∃ a : Fin (2^n) → F, polynomial v n a = p) ↔ p.degree < 2^n := by
  constructor
  · rintro ⟨a, rfl⟩; exact polynomial_degree_lt h a
  · intro hp
    have hs := (sequence v n h).span_degreeLT
      (m := 2^n) (fun i _ => isUnit_iff_ne_zero.mpr
        (leadingCoeff_ne_zero.mpr ((sequence v n h).ne_zero i)))
    have hr : (sequence v n h) '' Set.Iio (2^n) =
        Set.range (fun j : Fin (2^n) => novel v n j) := by
      ext q
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, hi⟩, by simp [sequence, show i < 2^n from hi]⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i.val, i.isLt, by simp [sequence]⟩
    rw [hr] at hs
    have hm : p ∈ Submodule.span F (Set.range (fun j : Fin (2^n) => novel v n j)) := by
      rw [hs, mem_degreeLT]; exact hp
    exact (Submodule.mem_span_range_iff_exists_fun F).mp hm

/-- Distinct novel-basis messages agree at at most `2^n-1` distinct points. -/
theorem agreement_bound {v : ℕ → F} [CharP F 2] [DecidableEq F] {n : ℕ}
    (h : Independent v n) (domain : Finset F) (a b : Fin (2^n) → F) (hab : a ≠ b) :
    (domain.filter fun x => (polynomial v n a).eval x =
      (polynomial v n b).eval x).card ≤ 2^n - 1 := by
  have hd (c : Fin (2^n) → F) : (polynomial v n c).natDegree ≤ 2^n - 1 := by
    by_cases hz : polynomial v n c = 0
    · simp [hz]
    · exact Nat.le_pred_of_lt ((natDegree_lt_iff_degree_lt hz).mpr (polynomial_degree_lt h c))
  exact Whir.Soundness.evaluation_agreement domain _ _
    (fun he => hab (polynomial_injective h he)) _ (hd a) (hd b)

/-- The dense novel-basis evaluation code on an arbitrary set of distinct points. -/
def evaluation (v : ℕ → F) (n : ℕ) (domain : Finset F) (a : Fin (2^n) → F) :
    domain → F := fun x => (polynomial v n a).eval x

theorem evaluation_agreement {v : ℕ → F} [CharP F 2] [DecidableEq F] {n : ℕ}
    (h : Independent v n) (domain : Finset F) (a b : Fin (2^n) → F) (hab : a ≠ b) :
    CodingBounds.agreement (evaluation v n domain a) (evaluation v n domain b) ≤ 2^n-1 := by
  classical
  have hc : CodingBounds.agreement (evaluation v n domain a) (evaluation v n domain b) =
      (domain.filter fun x => (polynomial v n a).eval x = (polynomial v n b).eval x).card := by
    change CodingBounds.agreement
      (fun x : domain => (polynomial v n a).eval x.val)
      (fun x : domain => (polynomial v n b).eval x.val) = _
    simp only [CodingBounds.agreement, Finset.card_filter]
    exact (Finset.sum_subtype domain (fun _ => Iff.rfl)
      (fun x => if (polynomial v n a).eval x = (polynomial v n b).eval x then 1 else 0)).symm
  rw [hc]
  exact agreement_bound h domain a b hab

/-- Evaluation is injective as soon as the domain contains the code dimension. -/
theorem evaluation_injective {v : ℕ → F} [CharP F 2] [DecidableEq F] {n : ℕ}
    (h : Independent v n) (domain : Finset F) (hd : 2^n ≤ domain.card) :
    Function.Injective (evaluation v n domain) := by
  intro a b he
  by_contra hab
  have hc := agreement_bound h domain a b hab
  have hp : ∀ x ∈ domain, (polynomial v n a).eval x = (polynomial v n b).eval x :=
    fun x hx => congrFun he ⟨x, hx⟩
  rw [Finset.filter_true_of_mem hp] at hc
  have : 0 < 2^n := by positivity
  omega

/-- Exact set equality with the RS space, suitable for the audited same-set MCA.
The statement neither assumes nor postulates that the additive encoder is RS. -/
theorem mem_evaluation_range {v : ℕ → F} [CharP F 2] {n : ℕ}
    (h : Independent v n) (domain : Finset F) (word : domain → F) :
    word ∈ Set.range (evaluation v n domain) ↔
      ∃ p : F[X], p.degree < 2^n ∧ ∀ x : domain, p.eval x.val = word x := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨polynomial v n a, polynomial_degree_lt h a, fun _ => rfl⟩
  · rintro ⟨p, hp, he⟩
    obtain ⟨a, ha⟩ := (polynomial_surjective h p).mpr hp
    exact ⟨a, by funext x; simpa [evaluation, ha] using he x⟩

/-- The existing finite-code Johnson bound instantiated by the proved encoder. -/
theorem evaluation_candidates_card {v : ℕ → F} [CharP F 2] [Fintype F]
    [DecidableEq F] {n : ℕ} (h : Independent v n)
    (domain : Finset F) (oracle : domain → F) (t : ℕ)
    (hd : 2^n - 1 ≤ domain.card)
    (threshold : (domain.card : ℚ) * (2^n-1 : ℕ) < (t : ℚ)^2) :
    ((CodingBounds.candidates (evaluation v n domain) oracle t).card : ℚ) ≤
      (domain.card * (domain.card - (2^n-1 : ℕ) : ℚ)) /
        ((t : ℚ)^2 - domain.card * (2^n-1 : ℕ)) := by
  simpa using CodingBounds.candidates_card (evaluation v n domain) oracle t (2^n-1)
    (by simpa using hd) (fun a b hab => evaluation_agreement h domain a b hab)
    (by simpa using threshold)

end
end Whir.AdditiveCode
