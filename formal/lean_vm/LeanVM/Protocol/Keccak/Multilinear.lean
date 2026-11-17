/-
  LeanVM.Protocol.Keccak.Multilinear

  Equality weights at a point, the verifier's `eq_kernel`, `multilinear_eval` and `dot` read as
  sums over the hypercube, and the polynomial dependence of such sums on one coordinate.
-/

module

public import LeanVM.Protocol.Keccak.Linear
public import LeanVM.Protocol.EndToEnd.Complete.Sumcheck

/-!
# Multilinear sums

The verifier's points are lists, the first coordinate the lowest bit of an index
(`eq_kernel`, `crates/verifier/src/multilinear.rs`). Here:

* `eqAt pt w = Π_k eq(pt_k, bit k of w)`, defined coordinate by coordinate from the first;
  `eqKernel_getD`: the verifier's `eqKernel pt` lists `eqAt pt w` for `w < 2^|pt|`;
  `sum_eqAt`: the weights sum to one; `eqAt_append`: a point split in two;
* `bitsE z m`: the hypercube point of index `z`, `eqAt_bitsE`: equality weights at a cube point
  are an indicator;
* `multilinearEval_eq`, `dot_eqKernel`: the verifier's evaluation and inner product as sums;
* `polyLE_eqAt`: `eqAt` is affine in each coordinate, so a sum of products of `k` multilinear
  extensions is a polynomial of degree `k` in any one coordinate (`PolyLE`).
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Complete Finset

@[expose] public section

/-! ## Equality weights -/

/-- The equality weight of index `w` at the point `pt`, the first coordinate on the lowest bit. -/
def eqAt : List E → ℕ → E
  | [], _ => 1
  | r :: rs, w => (if w % 2 = 1 then r else 1 + r) * eqAt rs (w / 2)

@[simp] theorem eqAt_nil (w : ℕ) : eqAt [] w = 1 := rfl

theorem eqAt_cons (r : E) (rs : List E) (w : ℕ) :
    eqAt (r :: rs) w = (if w % 2 = 1 then r else 1 + r) * eqAt rs (w / 2) := rfl

/-- Only the low `|pt|` bits matter. -/
theorem eqAt_mod : ∀ (pt : List E) (w : ℕ), eqAt pt w = eqAt pt (w % 2 ^ pt.length)
  | [], _ => rfl
  | r :: rs, w => by
    rw [eqAt_cons, eqAt_cons, List.length_cons, pow_succ, mul_comm (2 ^ rs.length) 2,
      Nat.mod_mul_right_mod, Nat.mod_mul_right_div_self, ← eqAt_mod rs]

/-- A point split in two. -/
theorem eqAt_append : ∀ (a b : List E) (w : ℕ), eqAt (a ++ b) w = eqAt a w * eqAt b (w / 2 ^ a.length)
  | [], b, w => by simp
  | r :: a, b, w => by
    rw [List.cons_append, eqAt_cons, eqAt_cons, eqAt_append a b, List.length_cons, pow_succ,
      Nat.div_div_eq_div_mul, mul_comm (2 ^ a.length) 2, mul_assoc]

/-- Sums over `2N` indices pair them. -/
theorem sum_range_two_mul (N : ℕ) (F : ℕ → E) :
    ∑ w ∈ range (2 * N), F w = ∑ w ∈ range N, (F (2 * w) + F (2 * w + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, add_assoc]

/-- Sums over the cube of `m + 1` coordinates split on the first. -/
theorem sum_cube_succ (m : ℕ) (F : ℕ → E) :
    ∑ w ∈ range (2 ^ (m + 1)), F w = ∑ w ∈ range (2 ^ m), (F (2 * w) + F (2 * w + 1)) := by
  rw [pow_succ, mul_comm, sum_range_two_mul]

/-- The equality weights sum to one. -/
theorem sum_eqAt : ∀ pt : List E, ∑ w ∈ range (2 ^ pt.length), eqAt pt w = 1
  | [] => by simp
  | r :: rs => by
    rw [List.length_cons, sum_cube_succ, ← sum_eqAt rs, Finset.sum_congr rfl fun w _ ↦ ?_]
    rw [eqAt_cons, eqAt_cons]
    have h1 : 2 * w % 2 = 0 := by omega
    have h2 : (2 * w + 1) % 2 = 1 := by omega
    have h3 : 2 * w / 2 = w := by omega
    have h4 : (2 * w + 1) / 2 = w := by omega
    simp only [h1, h2, h3, h4, ite_true, zero_ne_one, ite_false]
    rw [← add_mul, add_assoc, CharTwo.add_self_eq_zero, add_zero, one_mul]

/-! ## `eq_kernel` -/

theorem eqKernel_append (pt : List E) (r : E) :
    eqKernel (pt ++ [r]) = (eqKernel pt).map (· * (1 + r)) ++ (eqKernel pt).map (· * r) := by
  unfold eqKernel
  rw [List.foldl_concat]

theorem eqKernel_length : ∀ pt : List E, (eqKernel pt).length = 2 ^ pt.length := by
  intro pt
  induction pt using List.reverseRecOn with
  | nil => rfl
  | append_singleton pt r ih =>
    rw [eqKernel_append, List.length_append, List.length_map, List.length_map, ih,
      List.length_append, List.length_singleton, pow_succ]
    ring

theorem getD_map_mul (l : List E) (c : E) (w : ℕ) :
    (l.map (· * c)).getD w 0 = l.getD w 0 * c := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[w]? <;> simp

/-- **`eq_kernel` lists the equality weights.** -/
theorem eqKernel_getD : ∀ (pt : List E) (w : ℕ),
    (eqKernel pt).getD w 0 = if w < 2 ^ pt.length then eqAt pt w else 0 := by
  intro pt
  induction pt using List.reverseRecOn with
  | nil =>
    intro w
    rcases w with _ | w
    · rfl
    · simp [eqKernel, List.getD_eq_getElem?_getD]
  | append_singleton pt r ih =>
    intro w
    have hlen := eqKernel_length pt
    have hp : 2 ^ (pt.length + 1) = 2 ^ pt.length + 2 ^ pt.length := by rw [pow_succ]; ring
    rw [eqKernel_append, List.length_append, List.length_singleton, eqAt_append]
    by_cases hw : w < 2 ^ pt.length
    · rw [List.getD_append _ _ _ _ (by simpa [hlen] using hw), getD_map_mul, ih,
        ite_eq_left hw, ite_eq_left (by omega), Nat.div_eq_of_lt hw]
      simp [eqAt]
    · rw [List.getD_append_right _ _ _ _ (by simp [hlen]; omega), List.length_map, hlen,
        getD_map_mul, ih]
      by_cases hw2 : w < 2 ^ (pt.length + 1)
      · have hq : w / 2 ^ pt.length = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
        rw [ite_eq_left hw2, hq, ite_eq_left (by omega), eqAt_mod pt w,
          eqAt_mod pt (w - 2 ^ pt.length), ← Nat.mod_eq_sub_mod (by omega)]
        simp [eqAt]
      · rw [ite_eq_right hw2, ite_eq_right (by omega), zero_mul]

/-! ## Cube points -/

/-- The cube point of index `z`, `m` coordinates, the lowest bit first. -/
def bitsE : ℕ → ℕ → List E
  | _, 0 => []
  | z, m + 1 => (if z % 2 = 1 then 1 else 0) :: bitsE (z / 2) m

@[simp] theorem bitsE_length : ∀ (z m : ℕ), (bitsE z m).length = m
  | _, 0 => rfl
  | z, m + 1 => by simp [bitsE, bitsE_length (z / 2) m]

theorem bitsE_two_mul (z m : ℕ) : bitsE (2 * z) (m + 1) = 0 :: bitsE z m := by
  simp [bitsE, Nat.mul_mod_right, Nat.mul_div_cancel_left z (by norm_num : 0 < 2)]

theorem bitsE_two_mul_add_one (z m : ℕ) : bitsE (2 * z + 1) (m + 1) = 1 :: bitsE z m := by
  have h1 : (2 * z + 1) % 2 = 1 := by omega
  have h2 : (2 * z + 1) / 2 = z := by omega
  simp [bitsE, h1, h2]

/-- **Equality weights at a cube point** pick the index. -/
theorem eqAt_bitsE_lt : ∀ {m z w : ℕ}, z < 2 ^ m → w < 2 ^ m →
    eqAt (bitsE z m) w = if w = z then 1 else 0
  | 0, z, w, hz, hw => by
    have : z = 0 := by simpa using hz
    have : w = 0 := by simpa using hw
    subst z; subst w; simp [bitsE]
  | m + 1, z, w, hz, hw => by
    rw [bitsE, eqAt_cons, eqAt_bitsE_lt (m := m) (by rw [pow_succ] at hz; omega)
      (by rw [pow_succ] at hw; omega)]
    have key : w = z ↔ (w % 2 = z % 2 ∧ w / 2 = z / 2) := by omega
    by_cases h : w / 2 = z / 2
    · rcases Nat.mod_two_eq_zero_or_one z with hz2 | hz2 <;>
        rcases Nat.mod_two_eq_zero_or_one w with hw2 | hw2 <;>
        simp [hz2, hw2, h, key, CharTwo.add_self_eq_zero]
    · simp [h, key]

/-- A sum weighted by equality weights at a cube point picks the index. -/
theorem sum_eqAt_bitsE {m z : ℕ} (hz : z < 2 ^ m) (F : ℕ → E) :
    ∑ w ∈ range (2 ^ m), eqAt (bitsE z m) w * F w = F z := by
  rw [Finset.sum_eq_single z]
  · rw [eqAt_bitsE_lt hz hz, ite_eq_left rfl, one_mul]
  · intro w hw hne
    rw [eqAt_bitsE_lt hz (Finset.mem_range.1 hw), ite_eq_right hne, zero_mul]
  · intro h; exact absurd (Finset.mem_range.2 hz) h

/-! ## The verifier's evaluations -/

theorem foldPairs_getD (r : E) : ∀ (l : List E) (w : ℕ), 2 * w + 1 < l.length →
    (foldPairs r l).getD w 0 = l.getD (2 * w) 0 * (1 + r) + l.getD (2 * w + 1) 0 * r
  | a :: b :: rest, 0, _ => by simp [foldPairs]
  | a :: b :: rest, w + 1, h => by
    have e1 : 2 * (w + 1) = 2 * w + 1 + 1 := by ring
    rw [e1]
    simp only [foldPairs, List.getD_cons_succ]
    exact foldPairs_getD r rest w (by simp at h; omega)
  | [], _, h => by simp at h
  | [_], _, h => by simp at h

theorem foldPairs_length (r : E) : ∀ l : List E, (foldPairs r l).length = l.length / 2
  | a :: b :: rest => by
    simp only [foldPairs, List.length_cons, foldPairs_length r rest]; omega
  | [] => rfl
  | [_] => by simp [foldPairs]

/-- **`multilinear_eval`** of a table of `2^|pt|` entries is its equality-weighted sum. -/
theorem multilinearEval_eq : ∀ (pt mle : List E), mle.length = 2 ^ pt.length →
    multilinearEval mle pt = ∑ w ∈ range (2 ^ pt.length), eqAt pt w * mle.getD w 0
  | [], mle, h => by
    rcases mle with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp at h
    · simp [multilinearEval]
    · simp at h
  | r :: rs, mle, h => by
    have hl : (foldPairs r mle).length = 2 ^ rs.length := by
      rw [foldPairs_length, h, List.length_cons, pow_succ]; omega
    have step : multilinearEval mle (r :: rs) = multilinearEval (foldPairs r mle) rs := rfl
    rw [step, multilinearEval_eq rs _ hl, List.length_cons, sum_cube_succ]
    refine Finset.sum_congr rfl fun w hw ↦ ?_
    have hw' := Finset.mem_range.1 hw
    rw [foldPairs_getD r mle w (by rw [h, List.length_cons, pow_succ]; omega), eqAt_cons,
      eqAt_cons]
    have h1 : 2 * w % 2 = 0 := by omega
    have h2 : (2 * w + 1) % 2 = 1 := by omega
    have h3 : 2 * w / 2 = w := by omega
    have h4 : (2 * w + 1) / 2 = w := by omega
    simp only [h1, h2, h3, h4, ite_true, zero_ne_one, ite_false]
    ring

/-- `dot` of two lists of the same length is the sum of the products. -/
theorem dot_eq : ∀ (a b : List E), a.length = b.length →
    dot a b = ∑ j ∈ range a.length, a.getD j 0 * b.getD j 0 := by
  intro a b h
  unfold dot
  rw [← sumE, sumE_eq_sum]
  induction a generalizing b with
  | nil => simp
  | cons x a ih =>
    rcases b with _ | ⟨y, b⟩
    · simp at h
    · simp only [List.zipWith_cons_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ']
      rw [ih b (by simpa using h)]
      simp [add_comm]

/-- **The verifier's `dot(eq[:n], w)`**: the equality-weighted sum of `w`. -/
theorem dot_eqKernel (pt w : List E) (hn : w.length ≤ 2 ^ pt.length) :
    dot ((eqKernel pt).take w.length) w = ∑ j ∈ range w.length, eqAt pt j * w.getD j 0 := by
  rw [dot_eq _ _ (by simp [eqKernel_length, hn]), List.length_take, eqKernel_length,
    min_eq_left hn]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' := Finset.mem_range.1 hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hj', ← List.getD_eq_getElem?_getD,
    eqKernel_getD, ite_eq_left (by omega)]

/-! ## Degrees in one coordinate -/

/-- An equality weight is affine in each coordinate. -/
theorem polyLE_eqAt (pre post : List E) (w : ℕ) :
    PolyLE 1 fun x ↦ eqAt (pre ++ x :: post) w := by
  have h : ∀ x, eqAt (pre ++ x :: post) w =
      eqAt pre w * eqAt post (w / 2 ^ pre.length / 2) *
        (if w / 2 ^ pre.length % 2 = 1 then x else 1 + x) := by
    intro x
    rw [eqAt_append, eqAt_cons]
    ring
  refine PolyLE.congr ?_ fun x ↦ (h x).symm
  split_ifs
  · exact (PolyLE.const_mul PolyLE.id
      (eqAt pre w * eqAt post (w / 2 ^ pre.length / 2))).congr fun x ↦ rfl
  · exact (PolyLE.const_mul (PolyLE.affine 1 1)
      (eqAt pre w * eqAt post (w / 2 ^ pre.length / 2))).congr fun x ↦ by ring

/-- A multilinear extension is affine in each coordinate. -/
theorem polyLE_mle (pre post : List E) (N : ℕ) (f : ℕ → E) :
    PolyLE 1 fun x ↦ ∑ w ∈ range N, eqAt (pre ++ x :: post) w * f w :=
  PolyLE.sum _ fun w _ ↦ ((PolyLE.mul (polyLE_eqAt pre post w) (PolyLE.const 0 (f w))).mono
    (by omega)).congr fun _ ↦ rfl

end
end LeanVM.Protocol.KeccakGkr
