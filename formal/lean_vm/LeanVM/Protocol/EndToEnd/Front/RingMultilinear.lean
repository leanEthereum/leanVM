/-
  LeanVM.Protocol.EndToEnd.Front.RingMultilinear

  The weight of the program's ring-switching claim is the multilinear extension of its values on
  the cube: what WHIR's terminal check needs of a weight it evaluates at a random point.
-/

module

public import LeanVM.Protocol.EndToEnd.Front.RingFidelity

/-!
# The ring claim's weight is multilinear

The program's ring claim (`ringSwitchClaim`, `verifier.py:1405-1406` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`) has the weight
`W(u) = eqAbove(u) · Σ_k c_k Π_n (1 + r_n^(2^k) + u_n)`, `eqAbove` the equality kernel of the
coordinates above the placement's window. On points of `μ` coordinates every summand is a product
of one affine function per coordinate (`eq_eval` reads the window's coordinates, `eqAbove` the
coordinates above it, disjoint), and such a product is the multilinear extension of its values on
the cube (`isMultilinearFn_affineProd`, characteristic two: `eq(b, p) = 1 + b + p` on a bit `b`).
A combination of them is too, so the weight is (`isMultilinearFn_ringWeight`), whatever the point,
the coefficients and the placement.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol.Verifier
open scoped ENNReal NNReal

@[expose] public section

/-! ## The cube and products of affine functions -/

/-- Bit `i` of a cube point, as `0` or `1` in `E`. -/
def cubeBit (x i : ℕ) : E := if x.testBit i then 1 else 0

/-- **A sum over the cube of a product of one function per coordinate is the product of the
sums over each bit.** -/
theorem sum_cube_prod (G : ℕ → E → E) :
    ∀ μ : ℕ, ∑ x ∈ Finset.range (2 ^ μ), ∏ i ∈ Finset.range μ, G i (cubeBit x i) =
      ∏ i ∈ Finset.range μ, (G i 0 + G i 1)
  | 0 => by simp
  | μ + 1 => by
    rw [pow_succ, mul_two, Finset.sum_range_add, Finset.prod_range_succ]
    have hlow : ∀ x ∈ Finset.range (2 ^ μ),
        ∏ i ∈ Finset.range (μ + 1), G i (cubeBit x i) =
          (∏ i ∈ Finset.range μ, G i (cubeBit x i)) * G μ 0 := fun x hx ↦ by
      rw [Finset.prod_range_succ, cubeBit,
        Nat.testBit_lt_two_pow (Finset.mem_range.mp hx)]
      rfl
    have hhigh : ∀ x ∈ Finset.range (2 ^ μ),
        ∏ i ∈ Finset.range (μ + 1), G i (cubeBit (2 ^ μ + x) i) =
          (∏ i ∈ Finset.range μ, G i (cubeBit x i)) * G μ 1 := fun x hx ↦ by
      rw [Finset.prod_range_succ]
      congr 1
      · refine Finset.prod_congr rfl fun i hi ↦ ?_
        rw [cubeBit, cubeBit, Nat.testBit_two_pow_add_gt (Finset.mem_range.mp hi)]
      · rw [cubeBit, Nat.testBit_two_pow_add_eq,
          Nat.testBit_lt_two_pow (Finset.mem_range.mp hx)]
        rfl
    rw [Finset.sum_congr rfl hlow, Finset.sum_congr rfl hhigh, ← Finset.sum_mul, ← Finset.sum_mul,
      sum_cube_prod G μ, ← mul_add]

/-- `eq_eval` of two lists is the product over their common length. -/
theorem eqEval_eq_prod (a b : List E) :
    eqEval a b = ∏ i ∈ Finset.range (min a.length b.length),
      (1 + a.getD i 0 + b.getD i 0) := by
  induction a generalizing b with
  | nil => simp [eqEval]
  | cons x a ih =>
    cases b with
    | nil => simp [eqEval]
    | cons z b =>
      have h : eqEval (x :: a) (z :: b) = (1 + x + z) * eqEval a b := by
        simp only [eqEval, List.zipWith_cons_cons, List.foldl_cons, one_mul]
        rw [foldl_mul_eq, foldl_mul_eq]
        ring
      rw [h, ih, List.length_cons, List.length_cons, Nat.add_min_add_right,
        Finset.prod_range_succ']
      simp [mul_comm]

/-- A product of one affine function per coordinate. -/
def AffineProd (μ : ℕ) (f : List E → E) : Prop :=
  ∃ α β : ℕ → E, ∀ y : List E, y.length = μ →
    f y = ∏ i ∈ Finset.range μ, (α i + β i * y.getD i 0)

/-- The cube point of index `x`, read at a coordinate. -/
theorem boolPoint_getD (μ x i : ℕ) (hi : i < μ) : (boolPoint μ x).getD i 0 = cubeBit x i := by
  simp [boolPoint, cubeBit, List.getD_eq_getElem?_getD, hi]

/-- **A product of affine functions is multilinear.** -/
theorem isMultilinearFn_affineProd {μ : ℕ} {f : List E → E} (hf : AffineProd μ f) :
    IsMultilinearFn μ f := by
  obtain ⟨α, β, hf⟩ := hf
  intro p hp
  have hlen : ∀ x : ℕ, (boolPoint μ x).length = μ := fun x ↦ by simp [boolPoint]
  rw [hf p hp]
  have hterm : ∀ x : Fin (2 ^ μ), f (boolPoint μ x) * eqEval (boolPoint μ x) p =
      ∏ i ∈ Finset.range μ, ((α i + β i * cubeBit x i) * (1 + cubeBit x i + p.getD i 0)) :=
    fun x ↦ by
      rw [hf _ (hlen x), eqEval_eq_prod, hlen, hp, min_self, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i hi ↦ ?_
      rw [boolPoint_getD μ x i (Finset.mem_range.mp hi)]
  simp only [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun x ↦ ∏ i ∈ Finset.range μ,
    ((α i + β i * cubeBit x i) * (1 + cubeBit x i + p.getD i 0))),
    sum_cube_prod (fun i b ↦ (α i + β i * b) * (1 + b + p.getD i 0)) μ]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  simp only [mul_zero, add_zero, mul_one]
  linear_combination (-(α i + α i * p.getD i 0 + β i)) * h2

/-- Multilinear functions are closed under linear combinations. -/
theorem isMultilinearFn_sum {μ : ℕ} {ι : Type} (s : Finset ι) (c : ι → E) (f : ι → List E → E)
    (hf : ∀ k ∈ s, IsMultilinearFn μ (f k)) :
    IsMultilinearFn μ (fun y ↦ ∑ k ∈ s, c k * f k y) := by
  intro p hp
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [hf k hk p hp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  ring

/-! ## The ring claim's weight -/

/-- A product over the coordinates from `o` on, as a product over all the coordinates. -/
theorem prod_range_shift (f : ℕ → E) (o μ : ℕ) :
    ∏ i ∈ Finset.range (μ - o), f (o + i) =
      ∏ i ∈ Finset.range μ, (if o ≤ i then f i else 1) := by
  by_cases h : o ≤ μ
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_sub_cancel_left, Finset.prod_range_add]
    have e1 : ∏ i ∈ Finset.range o, (if o ≤ i then f i else 1) = 1 :=
      Finset.prod_eq_one fun i hi ↦ by
        simp only [Finset.mem_range] at hi
        simp [show ¬ o ≤ i by omega]
    rw [e1, one_mul]
    exact Finset.prod_congr rfl fun i _ ↦ by simp
  · rw [show μ - o = 0 by omega, Finset.prod_range_zero]
    exact (Finset.prod_eq_one fun i hi ↦ by
      simp only [Finset.mem_range] at hi
      simp [show ¬ o ≤ i by omega]).symm

/-- A product over the first `m ≤ μ` coordinates, as a product over all the coordinates. -/
theorem prod_range_lt (f : ℕ → E) {m μ : ℕ} (h : m ≤ μ) :
    ∏ i ∈ Finset.range m, f i = ∏ i ∈ Finset.range μ, (if i < m then f i else 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Finset.prod_range_add]
  rw [Finset.prod_eq_one (s := Finset.range d) fun i _ ↦ by simp, mul_one]
  exact Finset.prod_congr rfl fun i hi ↦ by simp [Finset.mem_range.mp hi]

/-- **A window's equality kernel times the kernel above it is a product of affine functions**: the
two read disjoint coordinates. -/
theorem affineProd_eqAbove_mul (μ : ℕ) (pl : Placement) (a : List E) :
    AffineProd μ fun y ↦ pl.eqAbove y * eqEval a (y.take pl.vars) := by
  let o := pl.low + pl.vars
  let bits := selectorPoint (pl.index >>> o) (μ - pl.low - pl.vars)
  let m := min a.length (min pl.vars μ)
  refine ⟨fun i ↦ if i < m then 1 + a.getD i 0 else if o ≤ i then 1 + bits.getD (i - o) 0 else 1,
    fun i ↦ if i < m then 1 else if o ≤ i then 1 else 0, fun y hy ↦ ?_⟩
  have hbits : bits.length = μ - o := by simp [bits, selectorPoint, o, Nat.sub_sub]
  have h1 : pl.eqAbove y = ∏ i ∈ Finset.range μ,
      (if o ≤ i then 1 + bits.getD (i - o) 0 + y.getD i 0 else 1) := by
    unfold Placement.eqAbove
    rw [eqEval_eq_prod]
    simp only [hy, List.length_drop]
    rw [show (selectorPoint (pl.index >>> (pl.low + pl.vars)) (μ - pl.low - pl.vars)) = bits from
      rfl, hbits, show μ - (pl.low + pl.vars) = μ - o from rfl, min_self]
    rw [← prod_range_shift (fun i ↦ 1 + bits.getD (i - o) 0 + y.getD i 0) o μ]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    simp [List.getD_eq_getElem?_getD]
    rfl
  have h2 : eqEval a (y.take pl.vars) = ∏ i ∈ Finset.range μ,
      (if i < m then 1 + a.getD i 0 + y.getD i 0 else 1) := by
    rw [eqEval_eq_prod, List.length_take, hy]
    rw [prod_range_lt _ (show min a.length (min pl.vars μ) ≤ μ by omega)]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    split_ifs with hi
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
      simp [show i < pl.vars by omega]
    · rfl
  show pl.eqAbove y * eqEval a (y.take pl.vars) = _
  rw [h1, h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  by_cases hm : i < m
  · have : ¬ o ≤ i := by simp only [o, m] at hm ⊢; omega
    simp [hm, this]
  · by_cases ho : o ≤ i
    · simp [hm, ho]
    · simp [hm, ho]

/-- **The ring claim's weight is multilinear**: `u ↦ eqAbove(u) · Σ_k c_k eq(r^(2^k), u_window)`,
for any placement, point and coefficients. -/
theorem isMultilinearFn_ringWeight (μ : ℕ) (pl : Placement) (r cs : List E) :
    IsMultilinearFn μ fun y ↦ pl.eqAbove y * ringWeight r (y.take pl.vars) cs := by
  have h : (fun y ↦ pl.eqAbove y * ringWeight r (y.take pl.vars) cs) = fun y ↦
      ∑ k ∈ Finset.range cs.length, cs.getD k 0 *
        (pl.eqAbove y * eqEval (r.map (· ^ 2 ^ k)) (y.take pl.vars)) := by
    funext y
    rw [ringWeight_eq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  rw [h]
  exact isMultilinearFn_sum _ _ _ fun k _ ↦
    isMultilinearFn_affineProd (affineProd_eqAbove_mul μ pl _)

/-- **The program's ring claim has a multilinear weight** (WHIR evaluates it at its terminal
point). -/
theorem isMultilinearFn_ringSwitchClaim (layout : LeanVM.Protocol.Verifier.Layout) (target : E)
    (point cs : List E) :
    IsMultilinearFn layout.stackLog
      (ringSwitchClaim layout target fun rPrime ↦ ringWeight point rPrime cs).1 :=
  isMultilinearFn_ringWeight _ _ _ _

end
end LeanVM.Protocol.EndToEnd.Front
