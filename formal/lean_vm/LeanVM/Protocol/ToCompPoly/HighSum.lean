/-
  LeanVM.Protocol.ToCompPoly.HighSum

  The sum of a function over the cube with its last coordinates fixed, highest first: the running
  claim of a plain sumcheck that binds the highest variable first. Candidate for CompPoly.
-/

module

public import LeanVM.Protocol.ToCompPoly.Multilinear

/-!
# Sums with the high coordinates fixed

A plain sumcheck that binds the highest variable first draws its challenges `c_0, c_1, …` for
the coordinates `m - 1, m - 2, …`. After `j` rounds the last `j` coordinates hold
`c_{j-1}, …, c_0`, the reverse of the challenges, and the running claim is
`highSum g j c = Σ_{x ∈ {0,1}^(m-j)} g(x, c_{j-1}, …, c_0)`:

* `highSum_zero`: with nothing fixed it is the sum of `g` over the cube;
* `highSum_split`: fixing one more coordinate splits it into the sums with that coordinate `0`
  and `1`;
* `highFix_push_set`: the point with one more challenge `X` is the point with `0` there and the
  coordinate `m - 1 - j` set to `X`, so a multilinear `g` is affine in `X`;
* `highSum_self`: with everything fixed it is `g` at the reversed challenges.

Over an arbitrary commutative ring. Nothing here transcribes a source.
-/

namespace LeanVM.Protocol

open CompPoly CMlPolynomialEval

@[expose] public section

variable {R : Type*} [CommRing R]

/-- The point `(x, c_{j-1}, …, c_0)` on `m` coordinates. -/
def highFix {m j : ℕ} (hj : j ≤ m) (c : Vector R j) (x : Vector R (m - j)) : Vector R m :=
  Vector.cast (Nat.sub_add_cancel hj) (x ++ c.reverse)

/-- The sum `Σ_{x ∈ {0,1}^(m-j)} g(x, c_{j-1}, …, c_0)`; zero when more than `m` coordinates are
fixed. -/
def highSum {m : ℕ} (g : Vector R m → R) (j : ℕ) (c : Vector R j) : R :=
  if hj : j ≤ m then ∑ x : Fin (2 ^ (m - j)), g (highFix hj c (boolVec x)) else 0

omit [CommRing R] in
theorem highFix_getElem {m j : ℕ} (hj : j ≤ m) (c : Vector R j) (x : Vector R (m - j)) (i : ℕ)
    (hi : i < m) :
    (highFix hj c x)[i] =
      if h : i < m - j then x[i] else c[j - 1 - (i - (m - j))]'(by omega) := by
  simp only [highFix, Vector.getElem_cast, Vector.getElem_append, Vector.getElem_reverse]

/-- With nothing fixed, the sum is the sum over the cube. -/
theorem highSum_zero {m : ℕ} (g : Vector R m → R) :
    highSum g 0 #v[] = ∑ x : Fin (2 ^ m), g (boolVec x) := by
  rw [highSum, dite_eq_left (Nat.zero_le m)]
  refine Finset.sum_congr rfl fun x _ ↦ congrArg g ?_
  apply Vector.ext
  intro i hi
  rw [highFix_getElem, dite_eq_left (by omega)]

/-- With everything fixed, the sum is `g` at the reversed challenges. -/
theorem highSum_self {m : ℕ} (g : Vector R m → R) (c : Vector R m) :
    highSum g m c = g c.reverse := by
  rw [highSum, dite_eq_left le_rfl]
  have hone : 2 ^ (m - m) = 1 := by simp
  have : Unique (Fin (2 ^ (m - m))) :=
    ⟨⟨⟨0, by omega⟩⟩, fun x ↦ Fin.ext (by have := x.isLt; omega)⟩
  rw [Fintype.sum_unique]
  congr 1
  apply Vector.ext
  intro i hi
  rw [highFix_getElem, dite_eq_right (by omega), Vector.getElem_reverse]
  congr 1
  omega

/-- One more challenge `X` is the point with `0` there and coordinate `m - 1 - j` set to `X`. -/
theorem highFix_push_set {m j : ℕ} (hj : j < m) (c : Vector R j) (x : Vector R (m - (j + 1)))
    (X : R) :
    highFix hj (c.push X) x = (highFix hj (c.push 0) x).set (m - (j + 1)) X (by omega) := by
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_set, highFix_getElem, highFix_getElem]
  by_cases h1 : i < m - (j + 1)
  · rw [dite_eq_left h1, dite_eq_left h1, ite_eq_right (by omega)]
  · rw [dite_eq_right h1, dite_eq_right h1]
    by_cases h2 : m - (j + 1) = i
    · rw [ite_eq_left h2, Vector.getElem_push, dite_eq_right (by omega)]
    · rw [ite_eq_right h2, Vector.getElem_push, Vector.getElem_push, dite_eq_left (by omega),
        dite_eq_left (by omega)]

/-- Bit `i` of `x + 2^p` for `x < 2^p` and `i < p` is bit `i` of `x`. -/
private theorem testBit_add_two_pow_low {x p i : ℕ} (hi : i < p) :
    (x + 2 ^ p).testBit i = x.testBit i := by
  rw [add_comm, Nat.testBit_two_pow_add_gt hi]

/-- Bit `p` of `x + 2^p` for `x < 2^p` is set. -/
private theorem testBit_add_two_pow_self {x p : ℕ} (hx : x < 2 ^ p) :
    (x + 2 ^ p).testBit p = true := by
  rw [add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hx]
  rfl

/-- The point at a cube index whose top bit is `b`: one more challenge, `b`. -/
private theorem highFix_boolVec_top {m j : ℕ} (hj : j < m) (c : Vector R j)
    (x' : Fin (2 ^ (m - (j + 1)))) (b : Bool)
    (hx : x'.val + (if b then 2 ^ (m - (j + 1)) else 0) < 2 ^ (m - j)) :
    highFix hj.le c (boolVec (⟨x'.val + (if b then 2 ^ (m - (j + 1)) else 0), hx⟩ :
      Fin (2 ^ (m - j)))) = highFix hj (c.push (if b then 1 else 0)) (boolVec x') := by
  apply Vector.ext
  intro i hi
  rw [highFix_getElem, highFix_getElem]
  simp only [boolVec, Vector.getElem_ofFn]
  by_cases h1 : i < m - (j + 1)
  · rw [dite_eq_left (by omega), dite_eq_left h1]
    cases b
    · simp
    · simp only [ite_true, testBit_add_two_pow_low h1]
  · by_cases h2 : i = m - (j + 1)
    · subst h2
      rw [dite_eq_left (by omega), dite_eq_right h1, Vector.getElem_push,
        dite_eq_right (by omega)]
      cases b
      · simp [Nat.testBit_lt_two_pow x'.isLt]
      · simp [testBit_add_two_pow_self x'.isLt]
    · rw [dite_eq_right (by omega), dite_eq_right h1, Vector.getElem_push,
        dite_eq_left (by omega)]
      congr 1
      omega

/-- Fixing one more coordinate splits the sum into the sums with that coordinate `0` and `1`. -/
theorem highSum_split {m : ℕ} (g : Vector R m → R) {j : ℕ} (hj : j < m) (c : Vector R j) :
    highSum g j c = highSum g (j + 1) (c.push 0) + highSum g (j + 1) (c.push 1) := by
  rw [highSum, highSum, highSum, dite_eq_left hj.le, dite_eq_left (show j + 1 ≤ m from hj),
    dite_eq_left (show j + 1 ≤ m from hj)]
  set p := m - (j + 1) with hp
  have hmj : m - j = p + 1 := by omega
  -- Split the cube of `m - j` coordinates by its top bit.
  have hsplit : ∀ f : Fin (2 ^ (m - j)) → R, ∑ x, f x =
      ∑ x' : Fin (2 ^ p), f ⟨x'.val + 0, by rw [hmj, pow_succ]; omega⟩ +
        ∑ x' : Fin (2 ^ p), f ⟨x'.val + 2 ^ p, by rw [hmj, pow_succ]; omega⟩ := by
    intro f
    have hcard : 2 ^ (m - j) = 2 ^ p + 2 ^ p := by rw [hmj, pow_succ]; ring
    rw [← (finCongr hcard).symm.sum_comp, Fin.sum_univ_add]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ congrArg f (Fin.ext ?_)
    simp
  rw [hsplit]
  congr 1
  · refine Finset.sum_congr rfl fun x' _ ↦ congrArg g ?_
    have hb : x'.val + (if false then 2 ^ p else 0) < 2 ^ (m - j) := by
      simp only [Bool.false_eq_true, ite_false]
      rw [hmj, pow_succ]
      omega
    have := highFix_boolVec_top hj c x' false hb
    simpa using this
  · refine Finset.sum_congr rfl fun x' _ ↦ congrArg g ?_
    have hb : x'.val + (if true then 2 ^ p else 0) < 2 ^ (m - j) := by
      simp only [ite_true]
      rw [hmj, pow_succ]
      omega
    have := highFix_boolVec_top hj c x' true hb
    simpa using this

end
end LeanVM.Protocol
