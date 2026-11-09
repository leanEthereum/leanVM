/-
  LeanVM.Guest.Batch.Cube

  Sums over the Boolean cube, multilinear functions, and the quadratic round polynomials of a
  sumcheck of a product of two multilinear functions.
-/

module

public import LeanVM.Protocol.Whir.Complete.Tables
public import LeanVM.Protocol.EndToEnd.Complete.TableMath
public import Mathlib.Algebra.Polynomial.Roots

/-!
# The Boolean cube

A point of the cube of `m` coordinates is `boolPoint m y`, the bits of `y` from the lowest, the
convention of `multilinearEval` (its first coordinate folds adjacent entries). `cubeSum n f pre`
sums `f` over the points of `n` coordinates that extend `pre`; a sumcheck's round `j`, after the
challenges `pre`, claims `cubeSum n f pre`, and splits it along the next coordinate
(`cubeSum_split`).

`Multilinear n f`: `f` is affine in each coordinate of its points of `n` coordinates. The
multilinear extension of a table (`multilinearEval`) and the equality weight (`eqEval p`) are
multilinear. Along any coordinate, a product of two multilinear functions is quadratic
(`QuadraticIn`), and so is a cube sum of such products along the next coordinate: a round's
polynomial has degree at most two, and a nonzero one has at most two roots
(`quadratic_roots`).

`E` has characteristic two: `1 - x = 1 + x`, and a difference is a sum.
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd Finset

@[expose] public section

/-! ## Cube sums -/

/-- **The sum of `f` over the cube's points of `n` coordinates extending `pre`.** -/
def cubeSum (n : ℕ) (f : List E → E) (pre : List E) : E :=
  ∑ y ∈ range (2 ^ (n - pre.length)), f (pre ++ boolPoint (n - pre.length) y)

/-- A cube sum splits along the next coordinate. -/
theorem cubeSum_split {n : ℕ} {f : List E → E} {pre : List E} (h : pre.length < n) :
    cubeSum n f pre = cubeSum n f (pre ++ [0]) + cubeSum n f (pre ++ [1]) := by
  obtain ⟨k, hk⟩ : ∃ k, n - pre.length = k + 1 := ⟨n - pre.length - 1, by omega⟩
  have hk' : n - (pre ++ [(0 : E)]).length = k := by simp; omega
  have hk'' : n - (pre ++ [(1 : E)]).length = k := by simp; omega
  rw [cubeSum, cubeSum, cubeSum, hk, hk', hk'', pow_succ', Protocol.Whir.Complete.sum_range_two_mul,
    ← sum_add_distrib]
  refine sum_congr rfl fun y _ ↦ ?_
  rw [Protocol.Whir.Complete.boolPoint_two_mul, Protocol.Whir.Complete.boolPoint_two_mul_add_one]
  simp

/-- At a full point, the cube sum is the value. -/
theorem cubeSum_full {n : ℕ} {f : List E → E} {pre : List E} (h : pre.length = n) :
    cubeSum n f pre = f pre := by
  subst h
  simp [cubeSum]

/-! ## Multilinear and quadratic functions -/

/-- **`f` is multilinear on points of `n` coordinates**: affine in each coordinate. -/
def Multilinear (n : ℕ) (f : List E → E) : Prop :=
  ∀ pre post : List E, pre.length + 1 + post.length = n → ∀ x : E,
    f (pre ++ x :: post) = (1 + x) * f (pre ++ 0 :: post) + x * f (pre ++ 1 :: post)

/-- `g` is a polynomial of degree at most two. -/
def Quadratic (g : E → E) : Prop :=
  ∃ a b c : E, ∀ x, g x = a * x ^ 2 + b * x + c

/-- `f` is quadratic along each coordinate of its points of `n` coordinates. -/
def QuadraticIn (n : ℕ) (f : List E → E) : Prop :=
  ∀ pre post : List E, pre.length + 1 + post.length = n →
    Quadratic fun x ↦ f (pre ++ x :: post)

/-- **A nonzero polynomial of degree at most two has at most two roots.** -/
theorem quadratic_roots {g : E → E} (hg : Quadratic g) (hne : ∃ x, g x ≠ 0) :
    {x | g x = 0}.ncard ≤ 2 := by
  obtain ⟨a, b, c, habc⟩ := hg
  set p : Polynomial E := .C a * .X ^ 2 + .C b * .X + .C c
  have hev : ∀ x, g x = p.eval x := fun x ↦ by simp [p, habc]
  have hp : p ≠ 0 := by
    obtain ⟨x, hx⟩ := hne
    rintro h
    exact hx (by rw [hev, h, Polynomial.eval_zero])
  have hset : {x | g x = 0} = (p.roots.toFinset : Set E) := by
    ext x
    simp [hev, Polynomial.mem_roots hp]
  rw [hset, Set.ncard_coe_finset]
  exact (Multiset.toFinset_card_le _).trans
    ((Polynomial.card_roots' p).trans Polynomial.natDegree_quadratic_le)

theorem Quadratic.sub {g g' : E → E} (hg : Quadratic g) (hg' : Quadratic g') :
    Quadratic fun x ↦ g x - g' x := by
  obtain ⟨a, b, c, h⟩ := hg
  obtain ⟨a', b', c', h'⟩ := hg'
  exact ⟨a - a', b - b', c - c', fun x ↦ by simp only [h, h']; ring⟩

/-- The equality weight of a point of `n` coordinates is multilinear. -/
theorem multilinear_eqEval {n : ℕ} {p : List E} (hp : p.length = n) :
    Multilinear n (eqEval p) := by
  intro pre post hlen x
  have hp' : p = p.take pre.length ++ p.drop pre.length := (List.take_append_drop _ _).symm
  obtain ⟨z, p₂, hz⟩ : ∃ z p₂, p.drop pre.length = z :: p₂ := by
    cases h : p.drop pre.length with
    | nil => have := congrArg List.length h; simp at this; omega
    | cons z p₂ => exact ⟨z, p₂, rfl⟩
  have hl : (p.take pre.length).length = pre.length := by simp; omega
  rw [hp', hz]
  simp only [Protocol.Whir.Complete.eqEval_append _ _ _ _ hl, Protocol.Whir.Complete.eqEval_cons]
  linear_combination (-(x * (1 + z)) * eqEval (List.take pre.length p) pre * eqEval p₂ post) *
    Protocol.Whir.Complete.two_eq_zero_E

/-- The multilinear extension of a table of `2^n` entries is multilinear. -/
theorem multilinear_multilinearEval {n : ℕ} {t : List E} (ht : t.length = 2 ^ n) :
    Multilinear n (multilinearEval t) := by
  intro pre post hlen x
  have hl : ∀ y : E, (pre ++ y :: post).length = n := fun y ↦ by simp; omega
  simp only [Protocol.Whir.Complete.multilinearEval_eq_sum n t _ ht (hl _), mul_sum,
    ← sum_add_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [multilinear_eqEval (Protocol.Whir.Complete.length_boolPoint n i) pre post hlen x]
  ring

theorem Multilinear.add {n : ℕ} {f g : List E → E} (hf : Multilinear n f) (hg : Multilinear n g) :
    Multilinear n fun y ↦ f y + g y := by
  intro pre post hlen x
  simp only [hf pre post hlen x, hg pre post hlen x]
  ring

theorem Multilinear.const_mul {n : ℕ} {f : List E → E} (a : E) (hf : Multilinear n f) :
    Multilinear n fun y ↦ a * f y := by
  intro pre post hlen x
  simp only [hf pre post hlen x]
  ring

/-- A sum of multilinear functions, one per element of a list, is multilinear. -/
theorem multilinear_sumE {α : Type} {n : ℕ} (l : List α) {g : α → List E → E}
    (hg : ∀ a ∈ l, Multilinear n (g a)) :
    Multilinear n fun y ↦ sumE (l.map fun a ↦ g a y) := by
  induction l with
  | nil => intro pre post _ x; simp [sumE]
  | cons a l ih =>
    have h := (hg a List.mem_cons_self).add (ih fun b hb ↦ hg b (List.mem_cons_of_mem a hb))
    intro pre post hlen x
    simp only [List.map_cons, Protocol.Whir.Complete.sumE_eq, List.sum_cons] at h ⊢
    exact h pre post hlen x

/-- A product of two multilinear functions is quadratic along each coordinate. -/
theorem quadraticIn_mul {n : ℕ} {u v : List E → E} (hu : Multilinear n u) (hv : Multilinear n v) :
    QuadraticIn n fun y ↦ u y * v y := by
  intro pre post hlen
  refine ⟨(u (pre ++ 0 :: post) + u (pre ++ 1 :: post)) *
      (v (pre ++ 0 :: post) + v (pre ++ 1 :: post)),
    u (pre ++ 0 :: post) * (v (pre ++ 0 :: post) + v (pre ++ 1 :: post)) +
      v (pre ++ 0 :: post) * (u (pre ++ 0 :: post) + u (pre ++ 1 :: post)),
    u (pre ++ 0 :: post) * v (pre ++ 0 :: post), fun x ↦ ?_⟩
  simp only [hu pre post hlen x, hv pre post hlen x]
  ring

theorem QuadraticIn.add {n : ℕ} {f g : List E → E} (hf : QuadraticIn n f) (hg : QuadraticIn n g) :
    QuadraticIn n fun y ↦ f y + g y := by
  intro pre post hlen
  obtain ⟨a, b, c, h⟩ := hf pre post hlen
  obtain ⟨a', b', c', h'⟩ := hg pre post hlen
  exact ⟨a + a', b + b', c + c', fun x ↦ by simp only [h, h']; ring⟩

/-- A sum of quadratics is quadratic. -/
theorem quadratic_sum {ι : Type} (s : Finset ι) {g : ι → E → E} (hg : ∀ i ∈ s, Quadratic (g i)) :
    Quadratic fun x ↦ ∑ i ∈ s, g i x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 0, 0, fun x ↦ by simp⟩
  | insert i s hi ih =>
    obtain ⟨a, b, c, h⟩ := hg i (mem_insert_self i s)
    obtain ⟨a', b', c', h'⟩ := ih fun j hj ↦ hg j (mem_insert_of_mem hj)
    exact ⟨a + a', b + b', c + c', fun x ↦ by simp only [sum_insert hi, h] at h' ⊢; rw [h']; ring⟩

/-- Along the next coordinate, a cube sum of a function quadratic along each coordinate is
quadratic. -/
theorem quadratic_cubeSum {n : ℕ} {f : List E → E} (hf : QuadraticIn n f) {pre : List E}
    (h : pre.length < n) : Quadratic fun x ↦ cubeSum n f (pre ++ [x]) := by
  have hk : ∀ x : E, n - (pre ++ [x]).length = n - pre.length - 1 := fun x ↦ by simp; omega
  simp only [cubeSum, hk, List.append_assoc, List.singleton_append]
  refine quadratic_sum _ fun y _ ↦ hf pre _ ?_
  rw [Protocol.Whir.Complete.length_boolPoint]
  omega

end
end LeanVM.Guest.Batch
