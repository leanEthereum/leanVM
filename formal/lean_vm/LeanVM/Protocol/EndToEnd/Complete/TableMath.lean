/-
  LeanVM.Protocol.EndToEnd.Complete.TableMath

  The multilinear facts the table sumcheck's honest prover rests on: functions of a point that are
  polynomials of bounded degree in each coordinate, the table weights of the verifier as products
  of one factor per coordinate, the multilinear extension at cube points, and the cube sum of the
  high-coordinate product.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.Sumcheck
public import LeanVM.Protocol.Verifier

/-!
# Multilinear facts for the table sumcheck

Nothing is transcribed. The table sumcheck of the verifier program
(`LeanVM.Protocol.Verifier.tableSumcheck`, `python-verifier/verifier.py:599-628` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`) sums, over the cube of `n` coordinates, a summand built
from the tables' weights (`tableWeights`), the columns' multilinear extensions and degree-two
forms. Its honest prover needs:

* `CoordPoly d n f`: on points of `n` coordinates, `f` is a polynomial of degree at most `d` in
  each coordinate, the others fixed (`PolyLE`); closed under sums, products and constants.
  `coordPoly_prod_range`: a product of one affine factor per coordinate has degree one in each;
  `coordPoly_multilinearEval_take`: the extension of a table at the first `h` coordinates.
* `eqEval_eq_prod_range`: `eq_eval` as a product over the coordinates.
* `getD_tableWeights`: the verifier's weight of a table of log-height `h` at a point is
  `Π_{v < h} (1 + e_v + r_v) · Π_{h ≤ v} r_v`.
* `multilinearEval_boolPoint_getD`: the extension at a cube point reads the entry.
* `sum_prod_bits`: `Σ_z Π_v z_v = 1` over the cube: only the all-ones corner survives.
-/

namespace LeanVM.Protocol.EndToEnd.Complete

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Whir.Complete
open LeanVM.Protocol.EndToEnd Finset

@[expose] public section

/-! ## Polynomials in each coordinate -/

/-- On points of `n` coordinates, `f` is a polynomial of degree at most `d` in each coordinate
with the others fixed. -/
def CoordPoly (d n : ℕ) (f : List E → E) : Prop :=
  ∀ r : List E, r.length = n → ∀ v < n, PolyLE d fun x ↦ f (r.set v x)

namespace CoordPoly

variable {d d' n : ℕ} {f g : List E → E}

/-- A constant has every degree. -/
theorem const (d n : ℕ) (a : E) : CoordPoly d n fun _ ↦ a :=
  fun _ _ _ _ ↦ PolyLE.const d a

/-- A larger degree bound. -/
theorem mono (h : CoordPoly d n f) (hd : d ≤ d') : CoordPoly d' n f :=
  fun r hr v hv ↦ (h r hr v hv).mono hd

/-- A function equal on points of `n` coordinates. -/
theorem congr (h : CoordPoly d n f) (hfg : ∀ r, r.length = n → f r = g r) : CoordPoly d n g :=
  fun r hr v hv ↦ (h r hr v hv).congr fun x ↦ hfg _ (by simpa using hr)

/-- Sums. -/
theorem add (hf : CoordPoly d n f) (hg : CoordPoly d n g) : CoordPoly d n fun r ↦ f r + g r :=
  fun r hr v hv ↦ (hf r hr v hv).add (hg r hr v hv)

/-- Products add degrees. -/
theorem mul (hf : CoordPoly d n f) (hg : CoordPoly d' n g) :
    CoordPoly (d + d') n fun r ↦ f r * g r :=
  fun r hr v hv ↦ (hf r hr v hv).mul (hg r hr v hv)

/-- A constant multiple. -/
theorem const_mul (hf : CoordPoly d n f) (a : E) : CoordPoly d n fun r ↦ a * f r :=
  fun r hr v hv ↦ (hf r hr v hv).const_mul a

/-- Finite sums. -/
theorem sum {ι : Type} (s : Finset ι) {F : ι → List E → E} (h : ∀ i ∈ s, CoordPoly d n (F i)) :
    CoordPoly d n fun r ↦ ∑ i ∈ s, F i r :=
  fun r hr v hv ↦ PolyLE.sum s fun i hi ↦ h i hi r hr v hv

/-- Sums of a list of functions. -/
theorem list_sum : ∀ (fs : List (List E → E)), (∀ f ∈ fs, CoordPoly d n f) →
    CoordPoly d n fun r ↦ (fs.map fun f ↦ f r).sum
  | [], _ => (const d n 0).congr fun _ _ ↦ by simp
  | f :: fs, h => ((h f (by simp)).add (list_sum fs fun g hg ↦ h g (by simp [hg]))).congr
      fun _ _ ↦ by simp

/-- `dot` of fixed coefficients against functions of degree `d`. -/
theorem dot_map : ∀ (c : List E) (fs : List (List E → E)), (∀ f ∈ fs, CoordPoly d n f) →
    CoordPoly d n fun r ↦ dot c (fs.map fun f ↦ f r)
  | [], _, _ => (const d n 0).congr fun _ _ ↦ by simp
  | _ :: _, [], _ => (const d n 0).congr fun _ _ ↦ by simp
  | a :: c, f :: fs, h => (((h f (by simp)).const_mul a).add
      (dot_map c fs fun g hg ↦ h g (by simp [hg]))).congr fun _ _ ↦ by
        simp only [List.map_cons, dot_cons]

/-- A coordinate of the point has degree one. -/
theorem getD (n i : ℕ) : CoordPoly 1 n fun r ↦ r.getD i 0 := by
  intro r _ v _
  by_cases hvi : v = i
  · subst hvi
    refine PolyLE.id.congr fun x ↦ ?_
    by_cases hv : v < r.length
    · simp [List.getD_eq_getElem?_getD, List.getElem?_set_self hv]
    · simp_all
  · exact (PolyLE.const 1 (r.getD i 0)).congr fun x ↦ by
      simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne hvi]

end CoordPoly

/-- A product of one factor per coordinate, each a polynomial of degree at most one in its
coordinate, has degree one in each coordinate. -/
theorem coordPoly_prod_range (n : ℕ) (g : ℕ → E → E) (hg : ∀ v, PolyLE 1 (g v)) :
    CoordPoly 1 n fun r ↦ ∏ v ∈ range n, g v (r.getD v 0) := by
  intro r hr u hu
  have hmem : u ∈ range n := mem_range.mpr hu
  refine ((hg u).mul (PolyLE.const 0 (∏ v ∈ (range n).erase u, g v (r.getD v 0)))).congr
    fun x ↦ ?_
  show _ = ∏ v ∈ range n, g v ((r.set u x).getD v 0)
  rw [← mul_prod_erase _ _ hmem]
  congr 1
  · simp [List.getD_eq_getElem?_getD, List.getElem?_set_self (hr ▸ hu)]
  · refine prod_congr rfl fun v hv ↦ ?_
    have hvu : u ≠ v := fun h ↦ (mem_erase.mp hv).1 h.symm
    simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne hvu]

/-! ## The equality kernel as a product -/

/-- An entry below the cut of a prefix is the list's. -/
theorem getD_take_of_lt (l : List E) {h v : ℕ} (hv : v < h) : (l.take h).getD v 0 = l.getD v 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hv, ↓reduceIte]

/-- `eq_eval` of two points of `h` coordinates is the product over the coordinates. -/
theorem eqEval_eq_prod_range : ∀ (a p : List E) (h : ℕ), a.length = h → p.length = h →
    eqEval a p = ∏ v ∈ range h, (1 + a.getD v 0 + p.getD v 0)
  | [], [], _, ha, _ => by subst ha; simp
  | [], _ :: _, _, ha, hp => by simp at ha hp; omega
  | _ :: _, [], _, ha, hp => by simp at ha hp; omega
  | x :: a, z :: p, h, ha, hp => by
    simp only [List.length_cons] at ha hp
    subst ha
    rw [eqEval_cons, eqEval_eq_prod_range a p a.length rfl (by omega), prod_range_succ']
    simp [mul_comm]

/-- The extension of a table of `2^h` entries at the first `h` coordinates of a point of `n ≥ h`
coordinates has degree one in each coordinate. -/
theorem coordPoly_multilinearEval_take {h n : ℕ} (hn : h ≤ n) (t : List E)
    (ht : t.length = 2 ^ h) : CoordPoly 1 n fun r ↦ multilinearEval t (r.take h) := by
  have key : ∀ r : List E, r.length = n → multilinearEval t (r.take h) =
      ∑ i ∈ range (2 ^ h), t.getD i 0 * ∏ v ∈ range n,
        (if v < h then 1 + (boolPoint h i).getD v 0 + r.getD v 0 else 1) := by
    intro r hr
    rw [multilinearEval_eq_sum h t _ ht (by simp; omega)]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [eqEval_eq_prod_range _ _ h (length_boolPoint h i) (by simp; omega)]
    refine congrArg (t.getD i 0 * ·) ?_
    rw [← prod_range_mul_prod_Ico _ hn]
    have hone : ∏ v ∈ Ico h n,
        (if v < h then 1 + (boolPoint h i).getD v 0 + r.getD v 0 else (1 : E)) = 1 :=
      prod_eq_one fun v hv ↦ by simp [(mem_Ico.mp hv).1.not_gt]
    rw [hone, mul_one]
    refine prod_congr rfl fun v hv ↦ ?_
    have hv' := mem_range.mp hv
    simp only [hv', ↓reduceIte, getD_take_of_lt r hv']
  have hfac : ∀ i v, PolyLE 1
      (fun c ↦ if v < h then 1 + (boolPoint h i).getD v 0 + c else (1 : E)) := by
    intro i v
    by_cases hv : v < h
    · simp only [hv, ↓reduceIte]
      exact (PolyLE.affine (1 + (boolPoint h i).getD v 0) 1).congr fun x ↦ by ring
    · simp only [hv, ↓reduceIte]
      exact PolyLE.const 1 1
  have hsum := CoordPoly.sum (n := n) (d := 1) (range (2 ^ h))
    (F := fun i r ↦ t.getD i 0 * ∏ v ∈ range n,
      (fun v c ↦ if v < h then 1 + (boolPoint h i).getD v 0 + c else (1 : E)) v (r.getD v 0))
    fun i _ ↦ (coordPoly_prod_range n
      (fun v c ↦ if v < h then 1 + (boolPoint h i).getD v 0 + c else (1 : E))
      (hfac i)).const_mul (t.getD i 0)
  exact hsum.congr fun r hr ↦ (key r hr).symm

/-! ## Cube points -/

/-- The extension of a table of `2^m` entries at a cube point reads the entry. -/
theorem multilinearEval_boolPoint_getD : ∀ (m : ℕ) (t : List E) (y : ℕ), t.length = 2 ^ m →
    y < 2 ^ m → multilinearEval t (boolPoint m y) = t.getD y 0
  | 0, t, y, ht, hy => by
    obtain rfl : y = 0 := by simpa using hy
    obtain ⟨a, rfl⟩ : ∃ a, t = [a] := by
      match t, ht with
      | [a], _ => exact ⟨a, rfl⟩
    rfl
  | m + 1, t, y, ht, hy => by
    rw [boolPoint_succ, multilinearEval_cons,
      multilinearEval_boolPoint_getD m _ (y / 2) (by rw [length_foldPairs, ht, pow_succ]; omega)
        (by rw [pow_succ] at hy; omega),
      getD_foldPairs _ _ _ (by rw [ht, pow_succ] at *; omega)]
    rcases Nat.even_or_odd' y with ⟨j, rfl | rfl⟩
    · have h1 : (2 * j).testBit 0 = false := by simp [Nat.testBit_zero]
      have h2 : 2 * j / 2 = j := by omega
      simp [h1, h2]
    · have h1 : (2 * j + 1).testBit 0 = true := by simp [Nat.testBit_zero]
      have h2 : (2 * j + 1) / 2 = j := by omega
      simp only [h1, ↓reduceIte, h2]
      rw [one_add_one_E]
      ring

/-- Over the cube, the product of all coordinates sums to one: only the all-ones corner. -/
theorem sum_prod_bits : ∀ m : ℕ,
    ∑ z ∈ range (2 ^ m), ∏ v ∈ range m, (boolPoint m z).getD v 0 = 1
  | 0 => by simp
  | m + 1 => by
    rw [pow_succ, mul_comm, sum_range_two_mul]
    rw [← sum_prod_bits m]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [boolPoint_two_mul, boolPoint_two_mul_add_one, prod_range_succ', prod_range_succ']
    simp

/-! ## The verifier's table weights -/

/-- The factor of coordinate `v` in the weight of a table of log-height `h`. -/
def weightFactor (e : List E) (h v : ℕ) (c : E) : E :=
  if v < h then 1 + e.getD v 0 + c else c

private theorem foldl_weights (heights : List ℕ) (e : List E) :
    ∀ (r : List E) (k : ℕ) (W : List E), W.length = heights.length →
      (r.zipIdx k).foldl (fun weights (challenge, coord) ↦
        List.zipWith (fun weight height ↦ weight *
          if coord < height then 1 + e.getD coord 0 + challenge else challenge) weights heights)
        W = List.zipWith (fun w height ↦ w * ∏ i ∈ range r.length,
          weightFactor e height (k + i) (r.getD i 0)) W heights
  | [], k, W, hW => by
    simp only [List.zipIdx_nil, List.foldl_nil, List.length_nil, prod_range_zero, mul_one]
    apply List.ext_getElem (by simp [hW])
    intro i h1 h2
    simp
  | c :: r, k, W, hW => by
    rw [List.zipIdx_cons, List.foldl_cons,
      foldl_weights heights e r (k + 1) _ (by simp [hW])]
    apply List.ext_getElem (by simp [hW])
    intro i h1 h2
    simp only [List.getElem_zipWith, List.length_cons]
    rw [prod_range_succ', mul_assoc]
    refine congrArg (W[i]'(by simp_all) * ·) ?_
    rw [mul_comm]
    refine congrArg₂ (· * ·) (prod_congr rfl fun j _ ↦ ?_) ?_
    · rw [show k + (j + 1) = k + 1 + j by ring]
      rfl
    · simp [weightFactor]

/-- The verifier's weights, one per table. -/
theorem length_tableWeights (heights : List ℕ) (e r : List E) :
    (tableWeights heights e r).length = heights.length := by
  rw [tableWeights, foldl_weights heights e r 0 _ (by simp)]
  simp

/-- **The verifier's table weight** of a table of log-height `h` at `r`:
`Π_{v < h} (1 + e_v + r_v) · Π_{h ≤ v} r_v`. -/
theorem getD_tableWeights (heights : List ℕ) (e r : List E) (t : ℕ) (ht : t < heights.length) :
    (tableWeights heights e r).getD t 0 =
      ∏ v ∈ range r.length, weightFactor e (heights.getD t 0) v (r.getD v 0) := by
  rw [tableWeights, foldl_weights heights e r 0 _ (by simp)]
  rw [List.getD_eq_getElem _ _ (by simpa using ht), List.getElem_zipWith,
    List.getD_eq_getElem _ _ ht]
  simp

/-- The weight of a table has degree one in each coordinate. -/
theorem coordPoly_weight (e : List E) (h n : ℕ) :
    CoordPoly 1 n fun r ↦ ∏ v ∈ range n, weightFactor e h v (r.getD v 0) :=
  coordPoly_prod_range n _ fun v ↦ by
    unfold weightFactor
    by_cases hv : v < h
    · simp only [hv, ↓reduceIte]
      exact (PolyLE.affine (1 + e.getD v 0) 1).congr fun x ↦ by ring
    · simp only [hv, ↓reduceIte]
      exact PolyLE.id

/-- On a cube point split at `h`, the weight of a table of log-height `h` is the equality weight
of the low part against `e`'s first `h` coordinates times the product of the high coordinates. -/
theorem prod_weightFactor_boolPoint (e : List E) {h n : ℕ} (hn : h ≤ n) (he : h ≤ e.length)
    (y z : ℕ) (hy : y < 2 ^ h) :
    ∏ v ∈ range n, weightFactor e h v ((boolPoint n (y + 2 ^ h * z)).getD v 0) =
      eqEval (e.take h) (boolPoint h y) *
        ∏ v ∈ range (n - h), (boolPoint (n - h) z).getD v 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = h + k := ⟨n - h, by omega⟩
  rw [boolPoint_add h k y z hy, prod_range_add, Nat.add_sub_cancel_left,
    eqEval_eq_prod_range _ _ h (by simp; omega) (length_boolPoint h y)]
  refine congrArg₂ (· * ·) (prod_congr rfl fun v hv ↦ ?_) (prod_congr rfl fun v _ ↦ ?_)
  · have hv' := mem_range.mp hv
    unfold weightFactor
    simp only [hv', ↓reduceIte, getD_take_of_lt e hv']
    rw [List.getD_append _ _ _ _ (by rw [length_boolPoint]; exact hv')]
  · unfold weightFactor
    simp only [show ¬ h + v < h by omega, ↓reduceIte]
    rw [List.getD_append_right _ _ _ _ (by rw [length_boolPoint]; omega), length_boolPoint,
      Nat.add_sub_cancel_left]

/-! ## The number of rounds -/

/-- `foldl max` bounds its start and every entry. -/
theorem le_foldl_max : ∀ (l : List ℕ) (init : ℕ), init ≤ l.foldl max init ∧
    ∀ a ∈ l, a ≤ l.foldl max init
  | [], init => ⟨le_rfl, by simp⟩
  | b :: l, init => by
    obtain ⟨h1, h2⟩ := le_foldl_max l (max init b)
    refine ⟨(le_max_left _ _).trans h1, fun a ha ↦ ?_⟩
    rcases List.mem_cons.mp ha with rfl | ha
    · exact (le_max_right _ _).trans h1
    · exact h2 a ha

end
end LeanVM.Protocol.EndToEnd.Complete
