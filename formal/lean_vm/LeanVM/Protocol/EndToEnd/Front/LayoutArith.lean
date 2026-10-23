/-
  LeanVM.Protocol.EndToEnd.Front.LayoutArith

  The Python verifier's multilinear helpers are the multilinear algebra of the oracle protocol:
  `multilinear_eval` is the multilinear extension, `eq_eval` against a cube point is the Lagrange
  basis, `_selector_point` is the cube point of an index, and a column claim placed on the stack
  means the stack's extension at the placed point.
-/

module

public import LeanVM.Protocol.EndToEnd.Claims
public import LeanVM.Protocol.ToCompPoly.Multilinear

/-!
# The verifier's arithmetic as multilinear algebra

The verifier program (`LeanVM.Protocol.Verifier`, transcribed from `python-verifier/verifier.py`
at leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`) computes with lists of `E`; the oracle
protocol computes with CompPoly's tables `CMlPolynomialEval` and their extension `evalMle`. This
module proves the two agree where the verifier calls them:

* `multilinearEval_eq_evalMle`: `multilinear_eval(mle, point)` is `evalMle` of the table at the
  point, the first coordinate the lowest bit (both fold adjacent entries first);
* `eqEval_boolPoint`: `eq_eval(point, x)` at the cube point of index `x` is the Lagrange basis of
  `point` at `x` (characteristic two: `1 + z = 1 - z`);
* `selectorPoint_eq_boolPoint`: `_selector_point(n, len)` is the cube point of `n`;
* `stackClaim_holds_eqEval_iff`: the stack claim `(eq_eval(point, ·), v)` holds of a stack exactly
  when the stack's extension at `point` is `v`.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters LeanVM.Protocol.Verifier CompPoly CMlPolynomialEval

@[expose] public section

/-! ## Integers -/

/-- `E(0)` is zero. -/
theorem eOfNat_zero : eOfNat 0 = 0 := by
  unfold eOfNat
  rw [show K.ofBits 0 = 0 by decide +kernel]
  simp

/-- `E(1)` is one. -/
theorem eOfNat_one : eOfNat 1 = 1 := by
  unfold eOfNat
  rw [show K.ofBits 1 = 1 by decide +kernel]
  simp

/-- `E(b)` of a bit is the bit as `0`/`1`. -/
theorem eOfNat_bit (n i : ℕ) : eOfNat ((n >>> i) % 2) = if n.testBit i then 1 else 0 := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ i) with h | h <;>
    simp [h, eOfNat_zero, eOfNat_one]

/-- `_selector_point(n, len)` is the cube point of `n` on `len` coordinates. -/
theorem selectorPoint_eq_boolPoint (n len : ℕ) : selectorPoint n len = boolPoint len n := by
  simp only [selectorPoint, boolPoint, eOfNat_bit]

/-- The cube point of `n` has `len` coordinates. -/
@[simp] theorem length_boolPoint (len n : ℕ) : (boolPoint len n).length = len := by
  simp [boolPoint]

/-- Coordinate `i` of the cube point of `n` is bit `i` of `n`. -/
theorem getElem_boolPoint (len n i : ℕ) (h : i < (boolPoint len n).length) :
    (boolPoint len n)[i] = if n.testBit i then 1 else 0 := by
  simp [boolPoint]

/-- The cube point of a table index is `boolVec`. -/
theorem boolPoint_eq_toList_boolVec {m : ℕ} (x : Fin (2 ^ m)) :
    boolPoint m x = (boolVec x : Vector E m).toList := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [boolPoint, boolVec]

/-! ## Multilinear evaluation -/

/-- One fold of `multilinear_eval` halves the table. -/
theorem length_foldPairs (r : E) (l : List E) : (foldPairs r l).length = l.length / 2 := by
  induction l using foldPairs.induct with
  | case1 a b rest ih => simp [foldPairs, ih]; omega
  | case2 l h =>
    rcases l with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp [foldPairs]
    · simp [foldPairs]
    · exact absurd rfl (h a b rest)

/-- Entry `i` of one fold of `multilinear_eval`: the pair `(2i, 2i + 1)` interpolated. -/
theorem getElem_foldPairs (r : E) (l : List E) (i : ℕ) (hi : i < (foldPairs r l).length) :
    (foldPairs r l)[i] = l[2 * i]'(by rw [length_foldPairs] at hi; omega) * (1 + r) +
      l[2 * i + 1]'(by rw [length_foldPairs] at hi; omega) * r := by
  induction l using foldPairs.induct generalizing i with
  | case1 a b rest ih =>
    rcases i with _ | i
    · simp [foldPairs]
    · simp only [foldPairs, List.getElem_cons_succ]
      rw [ih i (by simp [foldPairs] at hi; omega)]
      simp only [show 2 * (i + 1) = 2 * i + 1 + 1 by omega, List.getElem_cons_succ]
  | case2 l h =>
    exfalso
    rcases l with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp [foldPairs] at hi
    · simp [foldPairs] at hi
    · exact h a b rest rfl

/-- One fold of `multilinear_eval` is one layer of `evalMle`. -/
theorem foldPairs_toList {n : ℕ} (v : Vector E (2 ^ (n + 1))) (r : E) :
    foldPairs r v.toList = (evalMleLayer v r).toList := by
  apply List.ext_getElem
  · simp [length_foldPairs, pow_succ]
  · intro i h1 h2
    rw [getElem_foldPairs]
    simp only [Vector.getElem_toList]
    have hi : i < 2 ^ n := by simpa using h2
    have := evalMleLayer_get v r ⟨i, hi⟩
    simp only [Vector.get_eq_getElem] at this
    rw [this, CharTwo.sub_eq_add]
    ring

/-- `multilinear_eval` folds the first coordinate, then evaluates the rest. -/
theorem multilinearEval_cons (mle : List E) (r : E) (rs : List E) :
    multilinearEval mle (r :: rs) = multilinearEval (foldPairs r mle) rs := rfl

/-- A vector is its head followed by its tail. -/
theorem Vector.toList_eq_head_cons {α : Type} {n : ℕ} (x : Vector α (n + 1)) :
    x.toList = x.head :: x.tail.toList := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rcases i with _ | i
  · simp [Vector.head]
  · simp [Nat.add_comm]

/-- **`multilinear_eval` is the multilinear extension**: on a table of `2^n` entries and a point
of `n` coordinates, the Python's fold is CompPoly's `evalMle`. -/
theorem multilinearEval_eq_evalMle {n : ℕ} (v : Vector E (2 ^ n)) (x : Vector E n) :
    multilinearEval v.toList x.toList = evalMle v x := by
  induction n with
  | zero =>
    rw [evalMle_zero]
    have hx : x.toList = [] := by simp
    rw [hx]
    have : v.toList = [v.get ⟨0, by norm_num⟩] := by
      apply List.ext_getElem (by simp)
      intro i h1 h2
      simp only [List.length_cons, List.length_nil] at h2
      obtain rfl : i = 0 := by omega
      simp [Vector.get_eq_getElem]
    rw [this]
    rfl
  | succ n ih =>
    rw [Vector.toList_eq_head_cons x, multilinearEval_cons, foldPairs_toList, ih, evalMle_succ]

/-! ## The equality kernel -/

/-- `eq_eval` is a product over the zipped coordinates. -/
theorem eqEval_eq_list_prod (left right : List E) :
    eqEval left right = (List.zipWith (fun x z ↦ 1 + x + z) left right).prod := by
  rw [eqEval, List.prod_eq_foldl]

/-- **`eq_eval` at a cube point is the Lagrange basis**: `eq_eval(z, x)`, `x` the cube point of
index `x`, is the Lagrange basis of `z` at `x`. -/
theorem eqEval_boolPoint {n : ℕ} (z : Vector E n) (x : Fin (2 ^ n)) :
    eqEval z.toList (boolPoint n x) = (lagrangeBasis z)[x] := by
  rw [eqEval_eq_list_prod, Fin.getElem_fin, lagrangeBasis_getElem_nat]
  have hl : List.zipWith (fun x z ↦ 1 + x + z) z.toList (boolPoint n x) =
      List.ofFn fun b : Fin n ↦ if x.val.testBit b then z[b] else 1 - z[b] := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_zipWith, Vector.getElem_toList, getElem_boolPoint, List.getElem_ofFn]
    simp only [Fin.getElem_fin]
    split_ifs
    · linear_combination CharTwo.add_self_eq_zero (1 : E)
    · rw [add_zero, CharTwo.sub_eq_add, add_comm]
  rw [hl, List.prod_ofFn]

/-! ## Equality claims on the stack -/

/-- **An equality claim on the stack**: the stack claim `(eq_eval(z, ·), v)` holds of `q` exactly
when the stack's extension at `z` is `v`. -/
theorem stackClaim_holds_eqEval_iff {μ : ℕ} (z : Vector E μ) (v : E) (q : Column μ) :
    StackClaim.Holds μ (fun x ↦ eqEval z.toList x, v) q ↔
      eval₂Mle q.values (algebraMap K E) z = v := by
  unfold StackClaim.Holds
  rw [eval₂Mle, evalMle_eq_sum]
  refine Eq.congr_left (Finset.sum_congr rfl fun x _ ↦ ?_)
  change eqEval z.toList (boolPoint μ x) * _ = _
  rw [eqEval_boolPoint, mul_comm]
  simp [CMlPolynomialEval.map, Vector.getD, x.isLt]

/-- `stackClaim_holds_eqEval_iff` for a point given as a list of the right length. -/
theorem stackClaim_holds_eqEval_list_iff {μ : ℕ} (z : List E) (hz : z.length = μ) (v : E)
    (q : Column μ) :
    StackClaim.Holds μ (fun x ↦ eqEval z x, v) q ↔
      eval₂Mle q.values (algebraMap K E) ⟨z.toArray, by simpa using hz⟩ = v :=
  stackClaim_holds_eqEval_iff ⟨z.toArray, by simpa using hz⟩ v q

end
end LeanVM.Protocol.EndToEnd.Front
