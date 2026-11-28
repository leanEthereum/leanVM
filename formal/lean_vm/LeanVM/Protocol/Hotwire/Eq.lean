/-
  LeanVM.Protocol.Hotwire.Eq

  The equality weight over a commutative ring: at one coordinate, at an integer index, and
  between two points.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Equality weights over a commutative ring

Hotwire's evaluation lemmas (`ShiftEq.lean`, `Window.lean`) hold over any commutative ring `F`;
leanVM instantiates them at `E`, of characteristic two. A point is a list, its first coordinate
on the lowest bit of an index, as the verifier's slices (`crates/verifier/src/link.rs`, `eq_at`).

* `eq1 z x = z·x + (1 − z)·(1 − x)`, which reads `1 + z + x` in characteristic two
  (`eq1_of_charTwo`);
* `eqAt pt j = Π_h eq(pt_h, bit h of j)`, the verifier's `eq_at`; `eqAt_mod`: only the low
  `|pt|` bits of `j` count; `eqAt_append`: a point split in two; `eqAt_ofFn`: a point
  `Fin n → F` (`StateLink.lean`'s) as the product over its coordinates; `sum_eqAt`: the weights sum
  to one; `foldl_zipIdx_eqAt`: the Rust's fold, in characteristic two;
* `eqPt ζ r = Π_h eq(ζ_h, r_h)`, the verifier's `eq_eval`; `sum_eqAt_mul_eqAt`: it is
  `Σ_{j < 2^n} eq(r, j)·eq(ζ, j)`;
* `mle pt f = Σ_{v < 2^|pt|} eq(pt, v)·f(v)`, the multilinear extension of a table at a point.
-/

namespace LeanVM.Protocol.Hotwire

open Finset

@[expose] public section

variable {F : Type*} [CommRing F]

/-- The equality weight at one coordinate, `eq(z, x) = z·x + (1 − z)·(1 − x)`. In characteristic
two it is `1 + z + x` (`eq1_of_charTwo`), as the Rust writes it. -/
def eq1 (z x : F) : F := z * x + (1 - z) * (1 - x)

theorem eq1_comm (z x : F) : eq1 z x = eq1 x z := by unfold eq1; ring

@[simp] theorem eq1_one (z : F) : eq1 z 1 = z := by unfold eq1; ring

@[simp] theorem eq1_zero (z : F) : eq1 z 0 = 1 - z := by unfold eq1; ring

@[simp] theorem eq1_one_left (x : F) : eq1 1 x = x := by unfold eq1; ring

@[simp] theorem eq1_zero_left (x : F) : eq1 0 x = 1 - x := by unfold eq1; ring

/-- In characteristic two, `eq(z, x) = 1 + z + x`. -/
theorem eq1_of_charTwo [CharP F 2] (z x : F) : eq1 z x = 1 + z + x := by
  unfold eq1
  rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add]
  linear_combination (z * x) * (CharTwo.two_eq_zero (R := F))

/-- `eq(pt, j) = Π_h eq(pt_h, bit h of j)`, the multilinear equality weight at the integer `j`,
the first coordinate on the lowest bit: the verifier's `eq_at` (`crates/verifier/src/link.rs`). -/
def eqAt : List F → ℕ → F
  | [], _ => 1
  | z :: zs, j => (if j % 2 = 1 then z else 1 - z) * eqAt zs (j / 2)

@[simp] theorem eqAt_nil (j : ℕ) : eqAt ([] : List F) j = 1 := rfl

theorem eqAt_cons (z : F) (zs : List F) (j : ℕ) :
    eqAt (z :: zs) j = (if j % 2 = 1 then z else 1 - z) * eqAt zs (j / 2) := rfl

/-- The coordinate's factor is `eq(z, bit 0 of j)`. -/
theorem eqAt_cons_eq1 (z : F) (zs : List F) (j : ℕ) :
    eqAt (z :: zs) j = eq1 z (j % 2 : ℕ) * eqAt zs (j / 2) := by
  rw [eqAt_cons]
  rcases Nat.mod_two_eq_zero_or_one j with h | h <;> simp [h]

theorem eqAt_cons_two_mul (z : F) (zs : List F) (j : ℕ) :
    eqAt (z :: zs) (2 * j) = (1 - z) * eqAt zs j := by
  rw [eqAt_cons]; simp

theorem eqAt_cons_two_mul_add_one (z : F) (zs : List F) (j : ℕ) :
    eqAt (z :: zs) (2 * j + 1) = z * eqAt zs j := by
  rw [eqAt_cons]
  have h1 : (2 * j + 1) % 2 = 1 := by omega
  have h2 : (2 * j + 1) / 2 = j := by omega
  simp [h1, h2]

/-- Only the low `|pt|` bits of the index count. -/
theorem eqAt_mod : ∀ (pt : List F) (j : ℕ), eqAt pt j = eqAt pt (j % 2 ^ pt.length)
  | [], _ => rfl
  | z :: zs, j => by
    rw [eqAt_cons, eqAt_cons, List.length_cons, pow_succ, mul_comm (2 ^ zs.length) 2,
      Nat.mod_mul_right_mod, Nat.mod_mul_right_div_self, ← eqAt_mod zs]

/-- A point split in two: the low part reads the low bits, the high part the rest. -/
theorem eqAt_append : ∀ (a b : List F) (j : ℕ), eqAt (a ++ b) j = eqAt a j * eqAt b (j / 2 ^ a.length)
  | [], b, j => by simp
  | z :: a, b, j => by
    rw [List.cons_append, eqAt_cons, eqAt_cons, eqAt_append a b, List.length_cons, pow_succ,
      Nat.div_div_eq_div_mul, mul_comm (2 ^ a.length) 2, mul_assoc]

/-- A point given by its coordinates `ζ : Fin n → F`: `eq(ζ, j) = Π_i eq(ζ_i, bit i of j)`. -/
theorem eqAt_ofFn : ∀ {n : ℕ} (ζ : Fin n → F) (j : ℕ),
    eqAt (List.ofFn ζ) j = ∏ i : Fin n, if j.testBit i then ζ i else 1 - ζ i
  | 0, _, _ => by simp
  | n + 1, ζ, j => by
    rw [List.ofFn_succ, eqAt_cons, eqAt_ofFn, Fin.prod_univ_succ]
    refine congrArg₂ (· * ·) ?_ (prod_congr rfl fun i _ => ?_)
    · simp [Nat.testBit_zero]
    · simp [Nat.testBit_succ]

/-- In characteristic two a coordinate's factor is `z` or `1 + z`, as the Rust writes it. -/
theorem eqAt_cons_of_charTwo [CharP F 2] (z : F) (zs : List F) (j : ℕ) :
    eqAt (z :: zs) j = (if j % 2 = 1 then z else 1 + z) * eqAt zs (j / 2) := by
  rw [eqAt_cons, CharTwo.sub_eq_add]

/-- The verifier's `eq_at(point, j)` in characteristic two, a fold over the coordinates `x_h`
from `k` on, each `x_h` or `1 + x_h` by bit `h` of `j`. -/
theorem foldl_zipIdx_eqAt [CharP F 2] (j : ℕ) : ∀ (pt : List F) (k : ℕ) (a : F),
    (pt.zipIdx k).foldl (fun acc p ↦ acc * if j >>> p.2 % 2 = 1 then p.1 else 1 + p.1) a =
      a * eqAt pt (j >>> k)
  | [], _, a => by simp
  | x :: xs, k, a => by
    rw [List.zipIdx_cons, List.foldl_cons, foldl_zipIdx_eqAt j xs (k + 1), eqAt_cons_of_charTwo,
      Nat.shiftRight_succ]
    simp only [mul_assoc]

/-- **The verifier's `eq_at`** (`crates/verifier/src/link.rs`): the product from `1` over the
coordinates `x_h` of `x_h` if bit `h` of `j` is set and `1 + x_h` otherwise is `eq(pt, j)`, in
characteristic two. -/
theorem eqAt_eq_foldl_zipIdx [CharP F 2] (pt : List F) (j : ℕ) :
    eqAt pt j = pt.zipIdx.foldl (fun acc p ↦ acc * if j >>> p.2 % 2 = 1 then p.1 else 1 + p.1) 1 := by
  rw [foldl_zipIdx_eqAt, one_mul, Nat.shiftRight_zero]

/-- `eq(ζ, r) = Π_h eq(ζ_h, r_h)`, the verifier's `eq_eval`; a longer list's extra coordinates
are dropped. -/
def eqPt : List F → List F → F
  | z :: zs, x :: xs => eq1 z x * eqPt zs xs
  | _, _ => 1

@[simp] theorem eqPt_nil_left (r : List F) : eqPt [] r = 1 := rfl

theorem eqPt_cons (z x : F) (zs xs : List F) : eqPt (z :: zs) (x :: xs) = eq1 z x * eqPt zs xs := rfl

/-- A sum over `j < 2m` by pairs `2j`, `2j + 1`. -/
theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ j ∈ range (2 * m), f j = ∑ j ∈ range m, (f (2 * j) + f (2 * j + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, add_assoc]

/-- `Σ_{j < 2^n} eq(r, j)·eq(ζ, j) = eq(ζ, r)` for two points of `n` coordinates. -/
theorem sum_eqAt_mul_eqAt : ∀ (ζ r : List F), ζ.length = r.length →
    ∑ j ∈ range (2 ^ ζ.length), eqAt r j * eqAt ζ j = eqPt ζ r
  | [], [], _ => by simp
  | z :: ζ, x :: r, h => by
    have h' : ζ.length = r.length := by simpa using h
    rw [List.length_cons, pow_succ, mul_comm, sum_range_two_mul, eqPt_cons,
      ← sum_eqAt_mul_eqAt ζ r h', mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [eqAt_cons_two_mul, eqAt_cons_two_mul, eqAt_cons_two_mul_add_one, eqAt_cons_two_mul_add_one]
    unfold eq1
    ring
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- The equality weights sum to one. -/
theorem sum_eqAt : ∀ pt : List F, ∑ j ∈ range (2 ^ pt.length), eqAt pt j = 1
  | [] => by simp
  | z :: zs => by
    rw [List.length_cons, pow_succ, mul_comm (2 ^ zs.length) 2, sum_range_two_mul, ← sum_eqAt zs]
    refine sum_congr rfl fun j _ => ?_
    rw [eqAt_cons_two_mul, eqAt_cons_two_mul_add_one]
    ring

/-- The multilinear extension of the table `f` at the point `pt`:
`Σ_{v < 2^|pt|} eq(pt, v)·f(v)`. -/
def mle (pt : List F) (f : ℕ → F) : F := ∑ v ∈ range (2 ^ pt.length), eqAt pt v * f v

/-- The multilinear extension of the constant `1` is `1`. -/
theorem mle_one (pt : List F) : mle pt (fun _ ↦ 1) = 1 := by
  simp only [mle, mul_one, sum_eqAt]

/-- A one-hot table read against the equality weights is the weight at its hot index. -/
theorem sum_eqAt_mul_ite (r : List F) (σ : ℕ) (hσ : σ < 2 ^ r.length) :
    ∑ v ∈ range (2 ^ r.length), eqAt r v * (if v = σ then 1 else 0) = eqAt r σ := by
  simp [mul_ite, hσ]

end

end LeanVM.Protocol.Hotwire
