/-
  LeanVM.Protocol.Keccak.Multilinear

  Equality weights at a point, the verifier's `eq_kernel`, `multilinear_eval` and `dot` read as
  sums over the hypercube, and the polynomial dependence of such sums on one coordinate.
-/

module

import LeanVM.Protocol.Keccak.Linear
public import LeanVM.Protocol.EndToEnd.Complete.Sumcheck
public import LeanVM.Protocol.Verifier.EqKernel

/-!
# Multilinear sums

The verifier's points are lists, the first coordinate the lowest bit of an index (`eq_kernel`,
`crates/verifier/src/multilinear.rs`); the equality weights `eqAt` and the kernel's lemmas are
`LeanVM.Protocol.Verifier.EqKernel`'s. Here:

* `bitsE z m`: the hypercube point of index `z`, `eqAt_bitsE_lt`: equality weights at a cube point
  are an indicator;
* `multilinearEval_eq`: the verifier's evaluation as an equality-weighted sum;
* `polyLE_eqAt`: `eqAt` is affine in each coordinate, so a sum of products of `k` multilinear
  extensions is a polynomial of degree `k` in any one coordinate (`PolyLE`).
-/

namespace LeanVM.Protocol.KeccakGkr

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.EndToEnd.Complete Finset

@[expose] public section

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

/-! ## `multilinear_eval` -/

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
