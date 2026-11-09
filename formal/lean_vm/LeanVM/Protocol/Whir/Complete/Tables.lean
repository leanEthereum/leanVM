/-
  LeanVM.Protocol.Whir.Complete.Tables

  Value tables on the cube and the verifier's list arithmetic on them: folding, multilinear
  evaluation, the equality kernel, the sumcheck round polynomial of a product of two multilinear
  tables, and the functions that are their own multilinear extensions.
-/

module

public import LeanVM.Protocol.Verifier
public import LeanVM.Protocol.EndToEnd.Claims

/-!
# Tables on the cube

The honest WHIR prover holds two value tables on the cube `{0,1}^m` (index `i` is the cube point
`boolPoint m i`, bit `0` first): the message `g` and the weight `W` of the running claim
`Σ_x W(x)·g(x)`. Everything the verifier computes about them is a function of
`LeanVM.Protocol.Verifier` on lists, and this module proves what those functions compute.

* `foldPairs r t` fixes the first coordinate at `r`; `foldAll t r` fixes the first `|r|`
  coordinates (`getD_foldAll`: entry `x` is `Σ_j eq(j, r)·t[j + 2^|r|·x]`), so `multilinearEval t p`
  is the multilinear extension `Σ_i t[i]·eq(i, p)` (`multilinearEval_eq_sum`).
* `getD_eqKernel`: entry `j` of `eqKernel p` is `eq(j, p)`.
* `roundC0 W g`, `roundC2 W g`: the constant and quadratic coefficients of the round polynomial
  `h(X) = Σ_x (W(0,x)(1+X) + W(1,x)X)·(g(0,x)(1+X) + g(1,x)X)`, the two scalars the verifier
  reads; `roundQuad claim W g` is the polynomial the verifier builds from them
  (`sumcheckRoundPoly 3 claim none`). `polyEval_roundQuad`: when `claim = Σ W·g`, its value at `c`
  is the sum of the folded product, `Σ (foldPairs c W)·(foldPairs c g)`.
* `axpy s W T = W + s·T`: every one of these functions is linear in the weight table.
* `IsMultilinearFn` (`LeanVM.Protocol.EndToEnd.Claims`) holds for products of affine factors
  (`affProd`), hence for `eqEval z`, for linear combinations, and for a function of a rotated
  point (`isMultilinearFn_rotate`). Such a function is the multilinear extension of its table
  (`multilinearEval_tableOf`).

All of it is characteristic two: `E` has `1 + 1 = 0`.
-/

namespace LeanVM.Protocol.Whir.Complete

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd Finset

@[expose] public section

/-- `2 = 0` in `E`. -/
theorem two_eq_zero_E : (2 : E) = 0 := CharTwo.two_eq_zero

/-- `1 + 1 = 0` in `E`. -/
theorem one_add_one_E : (1 : E) + 1 = 0 := by
  rw [one_add_one_eq_two, two_eq_zero_E]

/-! ## Folds as sums -/

theorem foldl_add_eq (l : List E) (a : E) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.sum_cons, add_assoc]

theorem foldl_mul_eq (l : List E) (a : E) : l.foldl (· * ·) a = a * l.prod := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.prod_cons, mul_assoc]

@[simp] theorem dot_nil_left (u : List E) : dot [] u = 0 := by simp [dot]

@[simp] theorem dot_nil_right (t : List E) : dot t [] = 0 := by simp [dot]

theorem dot_cons (a x : E) (t u : List E) : dot (a :: t) (x :: u) = a * x + dot t u := by
  simp only [dot, List.zipWith_cons_cons, foldl_add_eq, List.sum_cons, zero_add]

theorem sumE_eq (l : List E) : sumE l = l.sum := by
  rw [sumE, foldl_add_eq, zero_add]

/-- `dot` of two lists of equal length as a sum over the indices. -/
theorem dot_eq_sum : ∀ (t u : List E), t.length = u.length →
    dot t u = ∑ i ∈ range t.length, t.getD i 0 * u.getD i 0
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | a :: t, x :: u, h => by
    rw [dot_cons, dot_eq_sum t u (by simpa using h), List.length_cons, sum_range_succ']
    simp [add_comm]

@[simp] theorem eqEval_nil_left (b : List E) : eqEval [] b = 1 := by simp [eqEval]

@[simp] theorem eqEval_nil_right (a : List E) : eqEval a [] = 1 := by simp [eqEval]

/-- The equality kernel peels its first coordinate. -/
theorem eqEval_cons (x z : E) (a b : List E) :
    eqEval (x :: a) (z :: b) = (1 + x + z) * eqEval a b := by
  simp only [eqEval, List.zipWith_cons_cons, foldl_mul_eq, List.prod_cons, one_mul]

/-- The equality kernel is symmetric. -/
theorem eqEval_comm : ∀ (a b : List E), eqEval a b = eqEval b a
  | [], b => by simp
  | _ :: _, [] => by simp
  | x :: a, z :: b => by rw [eqEval_cons, eqEval_cons, eqEval_comm a b]; ring

/-- The equality kernel of concatenated points is the product. -/
theorem eqEval_append : ∀ (a₁ a₂ b₁ b₂ : List E), a₁.length = b₁.length →
    eqEval (a₁ ++ a₂) (b₁ ++ b₂) = eqEval a₁ b₁ * eqEval a₂ b₂
  | [], _, [], _, _ => by simp
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h
  | x :: a₁, a₂, z :: b₁, b₂, h => by
    simp only [List.cons_append, eqEval_cons, eqEval_append a₁ a₂ b₁ b₂ (by simpa using h)]
    ring

/-! ## Cube points -/

theorem length_boolPoint (m x : ℕ) : (boolPoint m x).length = m := by simp [boolPoint]

/-- The first coordinate of a cube point is its low bit. -/
theorem boolPoint_succ (m x : ℕ) :
    boolPoint (m + 1) x = (if x.testBit 0 then 1 else 0) :: boolPoint m (x / 2) := by
  simp only [boolPoint, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ ↦ ?_
  simp [Nat.testBit_div_two]

theorem boolPoint_two_mul (m j : ℕ) : boolPoint (m + 1) (2 * j) = 0 :: boolPoint m j := by
  rw [boolPoint_succ]
  simp [Nat.testBit_zero, Nat.mul_div_cancel_left j (by norm_num : 0 < 2)]

theorem boolPoint_two_mul_add_one (m j : ℕ) :
    boolPoint (m + 1) (2 * j + 1) = 1 :: boolPoint m j := by
  rw [boolPoint_succ]
  have : (2 * j + 1) / 2 = j := by omega
  simp [Nat.testBit_zero, this]

@[simp] theorem boolPoint_zero (x : ℕ) : boolPoint 0 x = [] := rfl

/-- A cube point of `n + k` coordinates whose index is `y + 2^n·z` is `y`'s point, then `z`'s. -/
theorem boolPoint_add (n k y z : ℕ) (hy : y < 2 ^ n) :
    boolPoint (n + k) (y + 2 ^ n * z) = boolPoint n y ++ boolPoint k z := by
  simp only [boolPoint, List.range_add, List.map_append, List.map_map]
  rw [show y + 2 ^ n * z = 2 ^ n * z + y by ring]
  congr 1
  · refine List.map_congr_left fun i hi ↦ ?_
    rw [Nat.testBit_two_pow_mul_add _ hy]
    simp [List.mem_range.mp hi]
  · refine List.map_congr_left fun i _ ↦ ?_
    simp only [Function.comp_apply]
    rw [Nat.testBit_two_pow_mul_add _ hy]
    simp

/-! ## Sums over the cube -/

theorem sum_range_two_mul (f : ℕ → E) (n : ℕ) :
    ∑ i ∈ range (2 * n), f i = ∑ j ∈ range n, (f (2 * j) + f (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, add_assoc]

/-- `y + N·z < N·M` for `y < N` and `z < M`. -/
theorem add_mul_lt {y z N M : ℕ} (hy : y < N) (hz : z < M) : y + N * z < N * M := by
  calc y + N * z < N + N * z := by omega
    _ = N * (z + 1) := by ring
    _ ≤ N * M := Nat.mul_le_mul_left _ hz

/-! ## Folding -/

theorem length_foldPairs (r : E) : ∀ t : List E, (foldPairs r t).length = t.length / 2
  | [] => by simp [foldPairs]
  | [_] => by simp [foldPairs]
  | a :: b :: t => by
    simp only [foldPairs, List.length_cons, length_foldPairs r t]
    omega

/-- Entry `j` of a fold: the pair `(t[2j], t[2j+1])` interpolated at `r`. -/
theorem getD_foldPairs (r : E) : ∀ (t : List E) (j : ℕ), 2 * j + 1 < t.length →
    (foldPairs r t).getD j 0 = t.getD (2 * j) 0 * (1 + r) + t.getD (2 * j + 1) 0 * r
  | [], _, h => by simp at h
  | [_], _, h => by simp at h
  | a :: b :: t, 0, _ => by simp [foldPairs]
  | a :: b :: t, j + 1, h => by
    simp only [foldPairs, List.getD_cons_succ, List.length_cons] at h ⊢
    rw [getD_foldPairs r t j (by omega)]
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
    simp

/-- Fix the first `|r|` coordinates of a table at `r`, one at a time. -/
def foldAll (t r : List E) : List E := r.foldl (fun cur c ↦ foldPairs c cur) t

theorem multilinearEval_eq_foldAll (t r : List E) :
    multilinearEval t r = (foldAll t r).headD 0 := rfl

@[simp] theorem foldAll_nil (t : List E) : foldAll t [] = t := rfl

theorem foldAll_cons (t : List E) (c : E) (r : List E) :
    foldAll t (c :: r) = foldAll (foldPairs c t) r := rfl

theorem foldAll_append (t r r' : List E) : foldAll t (r ++ r') = foldAll (foldAll t r) r' := by
  simp [foldAll, List.foldl_append]

theorem foldAll_concat (t r : List E) (c : E) :
    foldAll t (r ++ [c]) = foldPairs c (foldAll t r) := by
  rw [foldAll_append]; rfl

theorem multilinearEval_cons (t : List E) (c : E) (p : List E) :
    multilinearEval t (c :: p) = multilinearEval (foldPairs c t) p := rfl

/-- Fixing `|r|` coordinates of a table on `|r| + n` variables leaves `2^n` entries. -/
theorem length_foldAll : ∀ (r t : List E) (n : ℕ), t.length = 2 ^ (r.length + n) →
    (foldAll t r).length = 2 ^ n
  | [], t, n, h => by simpa using h
  | c :: r, t, n, h => by
    rw [foldAll_cons]
    refine length_foldAll r _ n ?_
    rw [length_foldPairs, h, List.length_cons, show r.length + 1 + n = r.length + n + 1 by ring,
      pow_succ, Nat.mul_div_cancel _ (by norm_num)]

/-- **Partial evaluation.** Fixing the first `k = |r|` coordinates at `r` leaves at `x` the sum
`Σ_j eq(j, r)·t[j + 2^k·x]`. -/
theorem getD_foldAll : ∀ (r t : List E) (n x : ℕ), t.length = 2 ^ (r.length + n) → x < 2 ^ n →
    (foldAll t r).getD x 0 =
      ∑ j ∈ range (2 ^ r.length), eqEval (boolPoint r.length j) r * t.getD (j + 2 ^ r.length * x) 0
  | [], t, n, x, _, _ => by simp
  | c :: r, t, n, x, h, hx => by
    rw [foldAll_cons]
    have hlen : (foldPairs c t).length = 2 ^ (r.length + n) := by
      rw [length_foldPairs, h, List.length_cons, show r.length + 1 + n = r.length + n + 1 by ring,
        pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    rw [getD_foldAll r _ n x hlen hx, List.length_cons, pow_succ, mul_comm (2 ^ r.length) 2,
      sum_range_two_mul]
    refine sum_congr rfl fun j hj ↦ ?_
    have hj' := mem_range.mp hj
    have hlt : j + 2 ^ r.length * x < 2 ^ (r.length + n) := by
      rw [pow_add]; exact add_mul_lt hj' hx
    rw [getD_foldPairs c t _ (by rw [h, List.length_cons, show r.length + 1 + n =
      r.length + n + 1 by ring, pow_succ]; omega), boolPoint_two_mul,
      boolPoint_two_mul_add_one, eqEval_cons, eqEval_cons]
    have e1 : 2 * (j + 2 ^ r.length * x) = 2 * j + 2 * 2 ^ r.length * x := by ring
    have e2 : 2 * (j + 2 ^ r.length * x) + 1 = 2 * j + 1 + 2 * 2 ^ r.length * x := by ring
    rw [e2, e1]
    linear_combination (-(eqEval (boolPoint r.length j) r *
      t.getD (2 * j + 1 + 2 * 2 ^ r.length * x) 0)) * two_eq_zero_E

/-- **The multilinear extension.** `multilinearEval t p = Σ_i t[i]·eq(i, p)`. -/
theorem multilinearEval_eq_sum (m : ℕ) (t p : List E) (ht : t.length = 2 ^ m)
    (hp : p.length = m) :
    multilinearEval t p = ∑ i ∈ range (2 ^ m), t.getD i 0 * eqEval (boolPoint m i) p := by
  subst hp
  rw [multilinearEval_eq_foldAll, List.headD_eq_getD,
    getD_foldAll p t 0 0 (by simpa using ht) (by simp)]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [mul_comm, eqEval_comm]
  simp

/-! ## The equality kernel -/

/-- One step of `eqKernel`. -/
private theorem eqKernel_step (out : List E) (r : E) (p : List E) :
    p.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r))
      (out.map (· * (1 + r)) ++ out.map (· * r)) =
    (r :: p).foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) out := rfl

private theorem eqKernel_general : ∀ (p out : List E),
    (p.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) out).length =
      out.length * 2 ^ p.length ∧
    ∀ i j, i < out.length → j < 2 ^ p.length →
      (p.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) out).getD
        (i + out.length * j) 0 = out.getD i 0 * eqEval (boolPoint p.length j) p
  | [], out => by
    refine ⟨by simp, fun i j hi hj ↦ ?_⟩
    obtain rfl : j = 0 := by simpa using hj
    simp
  | r :: p, out => by
    obtain ⟨hl, hg⟩ := eqKernel_general p (out.map (· * (1 + r)) ++ out.map (· * r))
    simp only [List.length_append, List.length_map] at hl hg
    refine ⟨by rw [List.foldl_cons, hl, List.length_cons, pow_succ]; ring, fun i j hi hj ↦ ?_⟩
    rw [List.foldl_cons]
    rw [List.length_cons, pow_succ] at hj
    rcases Nat.even_or_odd' j with ⟨j', rfl | rfl⟩
    · have := hg i j' (by omega) (by omega)
      rw [show i + out.length * (2 * j') = i + (out.length + out.length) * j' by ring, this,
        List.length_cons, boolPoint_two_mul, eqEval_cons]
      rw [List.getD_append _ _ _ _ (by simpa using hi)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
      simp; ring
    · have := hg (i + out.length) j' (by omega) (by omega)
      rw [show i + out.length * (2 * j' + 1) = i + out.length + (out.length + out.length) * j' by
        ring, this, List.length_cons, boolPoint_two_mul_add_one, eqEval_cons]
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp only [List.length_map, Nat.add_sub_cancel, List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_eq_getElem hi]
      simp only [Option.map_some, Option.getD_some]
      rw [one_add_one_E, zero_add]; ring

/-- The equality kernel has `2^|p|` entries. -/
theorem length_eqKernel (p : List E) : (eqKernel p).length = 2 ^ p.length := by
  have := (eqKernel_general p [1]).1
  simp only [List.length_singleton, one_mul] at this
  exact this

/-- Entry `j` of the equality kernel is `eq(j, p)`. -/
theorem getD_eqKernel (p : List E) (j : ℕ) (hj : j < 2 ^ p.length) :
    (eqKernel p).getD j 0 = eqEval (boolPoint p.length j) p := by
  have := (eqKernel_general p [1]).2 0 j (by simp) hj
  simpa [eqKernel] using this

/-- Pairing a table of `2^|p|` entries with the equality kernel at `p` is its multilinear
extension at `p`. -/
theorem dot_eqKernel (t p : List E) (ht : t.length = 2 ^ p.length) :
    dot t (eqKernel p) =
      ∑ j ∈ range (2 ^ p.length), t.getD j 0 * eqEval (boolPoint p.length j) p := by
  rw [dot_eq_sum _ _ (by rw [ht, length_eqKernel]), ht]
  exact sum_congr rfl fun j hj ↦ by rw [getD_eqKernel p j (mem_range.mp hj)]

/-! ## The round polynomial -/

/-- The constant coefficient `h(0) = Σ_x W(0,x)·g(0,x)` of the round polynomial. -/
def roundC0 : List E → List E → E
  | w0 :: _ :: ws, g0 :: _ :: gs => w0 * g0 + roundC0 ws gs
  | _, _ => 0

/-- The quadratic coefficient `Σ_x (W(0,x) + W(1,x))·(g(0,x) + g(1,x))` of the round
polynomial. -/
def roundC2 : List E → List E → E
  | w0 :: w1 :: ws, g0 :: g1 :: gs => (w0 + w1) * (g0 + g1) + roundC2 ws gs
  | _, _ => 0

/-- The round polynomial the verifier builds from the two scalars `roundC0`, `roundC2` and the
claim (`sumcheckRoundPoly 3 claim none`): the linear coefficient is `claim + c2`. -/
def roundQuad (claim : E) (W g : List E) : List E :=
  [roundC0 W g, claim + sumE [roundC2 W g], roundC2 W g]

theorem polyEval_three (a b d c : E) : polyEval [a, b, d] c = a + b * c + d * c ^ 2 := by
  simp [polyEval]; ring

/-- **The sumcheck round.** If the claim is `Σ W·g`, the round polynomial at `c` is the sum of
the product of the tables with their first coordinate fixed at `c`. -/
theorem polyEval_roundQuad (c : E) : ∀ (W g : List E), W.length = g.length → Even W.length →
    polyEval (roundQuad (dot W g) W g) c = dot (foldPairs c W) (foldPairs c g)
  | [], [], _, _ => by simp [roundQuad, roundC0, roundC2, polyEval, sumE, foldPairs]
  | [_], _, _, he => by simp at he
  | w0 :: w1 :: ws, g0 :: g1 :: gs, hl, he => by
    have ih := polyEval_roundQuad c ws gs (by simpa using hl)
      (by simpa [Nat.even_add_one] using he)
    simp only [roundQuad, polyEval_three, sumE_eq, List.sum_cons, List.sum_nil, add_zero] at ih ⊢
    simp only [roundC0, roundC2, dot_cons, foldPairs]
    linear_combination ih + (w1 * g1 * c) * two_eq_zero_E
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _ :: _, [], hl, _ => by simp at hl
  | _ :: _ :: _, [_], hl, _ => by simp at hl

/-! ## Linearity in the weight -/

/-- `W + s·T`, entrywise. -/
def axpy (s : E) (W T : List E) : List E := List.zipWith (fun a b ↦ a + s * b) W T

theorem length_axpy (s : E) (W T : List E) (h : W.length = T.length) :
    (axpy s W T).length = W.length := by
  simp [axpy, h]

/-- `roundC0` is linear in the weight table. -/
theorem roundC0_axpy (s : E) : ∀ (W T g : List E), W.length = T.length →
    roundC0 (axpy s W T) g = roundC0 W g + s * roundC0 T g
  | [], [], g, _ => by simp [axpy, roundC0]
  | [], _ :: _, _, h => by simp at h
  | [_], [], _, h => by simp at h
  | [_], [_], g, _ => by simp [axpy, roundC0]
  | [_], _ :: _ :: _, _, h => by simp at h
  | _ :: _ :: _, [], _, h => by simp at h
  | _ :: _ :: _, [_], _, h => by simp at h
  | w0 :: w1 :: ws, t0 :: t1 :: ts, g, h =>
    match g with
    | [] => by simp [axpy, roundC0]
    | [_] => by simp [axpy, roundC0]
    | g0 :: g1 :: gs => by
      have ih := roundC0_axpy s ws ts gs (by simpa using h)
      simp only [axpy] at ih ⊢
      simp only [List.zipWith_cons_cons, roundC0]
      rw [ih]; ring

/-- `roundC2` is linear in the weight table. -/
theorem roundC2_axpy (s : E) : ∀ (W T g : List E), W.length = T.length →
    roundC2 (axpy s W T) g = roundC2 W g + s * roundC2 T g
  | [], [], g, _ => by simp [axpy, roundC2]
  | [], _ :: _, _, h => by simp at h
  | [_], [], _, h => by simp at h
  | [_], [_], g, _ => by simp [axpy, roundC2]
  | [_], _ :: _ :: _, _, h => by simp at h
  | _ :: _ :: _, [], _, h => by simp at h
  | _ :: _ :: _, [_], _, h => by simp at h
  | w0 :: w1 :: ws, t0 :: t1 :: ts, g, h =>
    match g with
    | [] => by simp [axpy, roundC2]
    | [_] => by simp [axpy, roundC2]
    | g0 :: g1 :: gs => by
      have ih := roundC2_axpy s ws ts gs (by simpa using h)
      simp only [axpy] at ih ⊢
      simp only [List.zipWith_cons_cons, roundC2]
      rw [ih]; ring

/-- `dot` is linear in its first argument. -/
theorem dot_axpy (s : E) : ∀ (W T g : List E), W.length = T.length →
    dot (axpy s W T) g = dot W g + s * dot T g
  | [], [], _, _ => by simp [axpy]
  | _ :: _, [], _, h => by simp at h
  | [], _ :: _, _, h => by simp at h
  | _ :: _, _ :: _, [], _ => by simp [axpy]
  | w :: ws, t :: ts, x :: g, h => by
    have ih := dot_axpy s ws ts g (by simpa using h)
    simp only [axpy] at ih ⊢
    simp only [List.zipWith_cons_cons, dot_cons]
    rw [ih]; ring

/-- Folding is linear. -/
theorem foldPairs_axpy (s c : E) : ∀ (W T : List E), W.length = T.length →
    foldPairs c (axpy s W T) = axpy s (foldPairs c W) (foldPairs c T)
  | [], [], _ => rfl
  | [_], [_], _ => rfl
  | w0 :: w1 :: ws, t0 :: t1 :: ts, h => by
    have ih := foldPairs_axpy s c ws ts (by simpa using h)
    simp only [axpy] at ih ⊢
    simp only [List.zipWith_cons_cons, foldPairs]
    rw [ih]
    congr 1; ring
  | _ :: _, [], h => by simp at h
  | [], _ :: _, h => by simp at h
  | _ :: _ :: _, [_], h => by simp at h
  | [_], _ :: _ :: _, h => by simp at h

/-- The multilinear extension is linear in the table. -/
theorem multilinearEval_axpy (s : E) : ∀ (p W T : List E), W.length = T.length →
    multilinearEval (axpy s W T) p = multilinearEval W p + s * multilinearEval T p
  | [], [], [], _ => by simp [multilinearEval, axpy]
  | [], w :: _, t :: _, _ => by simp [multilinearEval, axpy]
  | [], _ :: _, [], h => by simp at h
  | [], [], _ :: _, h => by simp at h
  | c :: p, W, T, h => by
    rw [multilinearEval_cons, foldPairs_axpy s c W T h, multilinearEval_axpy s p _ _
      (by rw [length_foldPairs, length_foldPairs, h])]
    rfl

/-! ## Tables of functions -/

/-- The table of a function on the cube `{0,1}^m`. -/
def tableOf (m : ℕ) (w : List E → E) : List E := (List.range (2 ^ m)).map fun i ↦ w (boolPoint m i)

@[simp] theorem length_tableOf (m : ℕ) (w : List E → E) : (tableOf m w).length = 2 ^ m := by
  simp [tableOf]

theorem getD_tableOf (m : ℕ) (w : List E → E) (i : ℕ) (hi : i < 2 ^ m) :
    (tableOf m w).getD i 0 = w (boolPoint m i) := by
  simp [tableOf, hi]

/-- `IsMultilinearFn` with the sum over the cube as a sum over the indices. -/
theorem isMultilinearFn_iff (m : ℕ) (w : List E → E) :
    IsMultilinearFn m w ↔ ∀ p : List E, p.length = m →
      w p = ∑ x ∈ range (2 ^ m), w (boolPoint m x) * eqEval (boolPoint m x) p := by
  unfold IsMultilinearFn
  refine forall_congr' fun p ↦ imp_congr_right fun _ ↦ ?_
  rw [Fin.sum_univ_eq_sum_range (fun x ↦ w (boolPoint m x) * eqEval (boolPoint m x) p)]

/-- **A multilinear function is the extension of its table.** -/
theorem multilinearEval_tableOf {m : ℕ} {w : List E → E} (hw : IsMultilinearFn m w)
    (p : List E) (hp : p.length = m) : multilinearEval (tableOf m w) p = w p := by
  rw [multilinearEval_eq_sum m _ p (by simp) hp, (isMultilinearFn_iff m w).mp hw p hp]
  exact sum_congr rfl fun i hi ↦ by rw [getD_tableOf _ _ _ (mem_range.mp hi)]

/-- Pairing a function's table with a table. -/
theorem dot_tableOf (m : ℕ) (w : List E → E) (g : List E) (hg : g.length = 2 ^ m) :
    dot (tableOf m w) g = ∑ i ∈ range (2 ^ m), w (boolPoint m i) * g.getD i 0 := by
  rw [dot_eq_sum _ _ (by simp [hg]), length_tableOf]
  exact sum_congr rfl fun i hi ↦ by rw [getD_tableOf _ _ _ (mem_range.mp hi)]

/-! ## Multilinear functions -/

theorem isMultilinearFn_congr {m : ℕ} {w w' : List E → E} (hw : IsMultilinearFn m w)
    (h : ∀ p : List E, p.length = m → w p = w' p) : IsMultilinearFn m w' := by
  rw [isMultilinearFn_iff] at hw ⊢
  intro p hp
  rw [← h p hp, hw p hp]
  exact sum_congr rfl fun x _ ↦ by rw [h _ (length_boolPoint m x)]

theorem isMultilinearFn_add {m : ℕ} {w w' : List E → E} (hw : IsMultilinearFn m w)
    (hw' : IsMultilinearFn m w') : IsMultilinearFn m fun p ↦ w p + w' p := by
  rw [isMultilinearFn_iff] at hw hw' ⊢
  intro p hp
  rw [hw p hp, hw' p hp, ← sum_add_distrib]
  exact sum_congr rfl fun x _ ↦ by ring

theorem isMultilinearFn_const_mul {m : ℕ} {w : List E → E} (hw : IsMultilinearFn m w) (a : E) :
    IsMultilinearFn m fun p ↦ a * w p := by
  rw [isMultilinearFn_iff] at hw ⊢
  intro p hp
  rw [hw p hp, mul_sum]
  exact sum_congr rfl fun x _ ↦ by ring

theorem isMultilinearFn_const_zero (m : ℕ) : IsMultilinearFn m fun _ ↦ 0 := by
  rw [isMultilinearFn_iff]; intro p _; simp

/-- A linear combination over a list of multilinear functions is multilinear. -/
theorem isMultilinearFn_list_sum {ι : Type} {m : ℕ} (L : List ι) (c : ι → E)
    (w : ι → List E → E) (hw : ∀ i ∈ L, IsMultilinearFn m (w i)) :
    IsMultilinearFn m fun p ↦ (L.map fun i ↦ c i * w i p).sum := by
  induction L with
  | nil => simpa using isMultilinearFn_const_zero m
  | cons i L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact isMultilinearFn_add (isMultilinearFn_const_mul (hw i (by simp)) (c i))
      (ih fun j hj ↦ hw j (by simp [hj]))

/-- A product of affine factors, the `i`-th factor `a i + b i·p_i`. -/
def affProd (a b : ℕ → E) : List E → E
  | [] => 1
  | c :: p => (a 0 + b 0 * c) * affProd (fun i ↦ a (i + 1)) (fun i ↦ b (i + 1)) p

/-- **A product of affine factors is multilinear.** -/
theorem isMultilinearFn_affProd (m : ℕ) : ∀ (a b : ℕ → E), IsMultilinearFn m (affProd a b) := by
  induction m with
  | zero =>
    intro a b
    rw [isMultilinearFn_iff]
    intro p hp
    obtain rfl : p = [] := List.eq_nil_of_length_eq_zero hp
    simp [affProd]
  | succ m ih =>
    intro a b
    rw [isMultilinearFn_iff]
    intro p hp
    obtain ⟨c, p, rfl⟩ : ∃ c p', p = c :: p' := List.exists_cons_of_length_eq_add_one hp
    have hp' : p.length = m := by simpa using hp
    have h := (isMultilinearFn_iff m _).mp (ih (fun i ↦ a (i + 1)) (fun i ↦ b (i + 1))) p hp'
    rw [pow_succ, mul_comm, sum_range_two_mul]
    simp only [boolPoint_two_mul, boolPoint_two_mul_add_one, affProd, eqEval_cons]
    rw [h, mul_sum]
    refine sum_congr rfl fun x _ ↦ ?_
    linear_combination (-(a 0 * c + a 0 + b 0) * affProd (fun i ↦ a (i + 1)) (fun i ↦ b (i + 1))
      (boolPoint m x) * eqEval (boolPoint m x) p) * two_eq_zero_E

/-- The equality kernel at `z` as a product of affine factors. -/
theorem eqEval_eq_affProd : ∀ (z p : List E), z.length = p.length →
    eqEval z p = affProd (fun i ↦ 1 + z.getD i 0) (fun _ ↦ 1) p
  | [], [], _ => by simp [affProd]
  | _ :: _, [], h => by simp at h
  | [], _ :: _, h => by simp at h
  | x :: z, c :: p, h => by
    rw [eqEval_cons, affProd, eqEval_eq_affProd z p (by simpa using h)]
    simp

/-- `eq(z, ·)` is multilinear. -/
theorem isMultilinearFn_eqEval (z : List E) : IsMultilinearFn z.length (eqEval z) :=
  isMultilinearFn_congr (isMultilinearFn_affProd z.length _ _)
    fun p hp ↦ (eqEval_eq_affProd z p hp.symm).symm

/-! ## Rotating the coordinates -/

/-- The index of the rotated cube point: `i ↦ ⌊i / 2^k⌋ + 2^n·(i mod 2^k)`. -/
def rotIndex (k n i : ℕ) : ℕ := i / 2 ^ k + 2 ^ n * (i % 2 ^ k)

/-- The rotated index stays on the cube. -/
theorem rotIndex_lt {k n i : ℕ} (hi : i < 2 ^ (k + n)) : rotIndex k n i < 2 ^ (n + k) := by
  rw [rotIndex, pow_add]
  refine add_mul_lt ?_ (Nat.mod_lt _ (by positivity))
  rw [Nat.div_lt_iff_lt_mul (by positivity), mul_comm, ← pow_add]
  exact hi

/-- Rotating back undoes the rotation. -/
theorem rotIndex_rotIndex {k n i : ℕ} (hi : i < 2 ^ (k + n)) :
    rotIndex n k (rotIndex k n i) = i := by
  have hq : i / 2 ^ k < 2 ^ n := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), mul_comm, ← pow_add]; exact hi
  simp only [rotIndex]
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hq, zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hq, Nat.mod_add_div]

/-- The cube point of the rotated index is the rotated point. -/
theorem boolPoint_rotIndex (k n i : ℕ) (hi : i < 2 ^ (k + n)) :
    boolPoint (n + k) (rotIndex k n i) =
      (boolPoint (k + n) i).drop k ++ (boolPoint (k + n) i).take k := by
  have hq : i / 2 ^ k < 2 ^ n := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), mul_comm, ← pow_add]; exact hi
  have hsplit : boolPoint (k + n) i = boolPoint k (i % 2 ^ k) ++ boolPoint n (i / 2 ^ k) := by
    conv_lhs => rw [← Nat.mod_add_div i (2 ^ k)]
    exact boolPoint_add k n _ _ (Nat.mod_lt _ (by positivity))
  rw [rotIndex, boolPoint_add n k _ _ hq, hsplit]
  simp [length_boolPoint]

/-- Rotating both points keeps the equality kernel. -/
theorem eqEval_rotate (k : ℕ) (a b : List E) (h : a.length = b.length) :
    eqEval (a.drop k ++ a.take k) (b.drop k ++ b.take k) = eqEval a b := by
  rw [eqEval_append _ _ _ _ (by simp [h]), mul_comm, ← eqEval_append _ _ _ _ (by simp [h]),
    List.take_append_drop, List.take_append_drop]

/-- Reindex a sum over the cube by the rotation. -/
theorem sum_rotIndex (k n : ℕ) (f : ℕ → E) :
    ∑ i ∈ range (2 ^ (k + n)), f (rotIndex k n i) = ∑ x ∈ range (2 ^ (n + k)), f x := by
  refine sum_nbij' (rotIndex k n) (rotIndex n k) (fun i hi ↦ ?_) (fun x hx ↦ ?_)
    (fun i hi ↦ ?_) (fun x hx ↦ ?_) (fun _ _ ↦ rfl)
  · exact mem_range.mpr (rotIndex_lt (mem_range.mp hi))
  · exact mem_range.mpr (rotIndex_lt (mem_range.mp hx))
  · exact rotIndex_rotIndex (mem_range.mp hi)
  · exact rotIndex_rotIndex (mem_range.mp hx)

/-- **A function of the rotated point is multilinear** when the function is. -/
theorem isMultilinearFn_rotate {k n : ℕ} {w : List E → E} (hw : IsMultilinearFn (n + k) w) :
    IsMultilinearFn (k + n) fun p ↦ w (p.drop k ++ p.take k) := by
  rw [isMultilinearFn_iff] at hw ⊢
  intro p hp
  rw [hw _ (by simp [hp]), ← sum_rotIndex k n]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [boolPoint_rotIndex k n i (mem_range.mp hi), eqEval_rotate _ _ _
    (by rw [length_boolPoint, hp])]

end
end LeanVM.Protocol.Whir.Complete
