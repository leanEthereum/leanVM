/-
  LeanVM.Protocol.Whir.Complete.TablesExtra

  The lemmas of the bus era's `Whir/Complete/Tables` that `Protocol/Tables` no longer carries.
-/

module

public import LeanVM.Protocol.Tables

/-!
# Table lemmas for the completeness of the opening

Restored from `formal-bus-archive`'s `Protocol/Whir/Complete/Tables.lean`: the folds of `+` and
`*` as sums and products, a sum over `2n` as pairs, and the round coefficients' linearity in the
weight.
-/

namespace LeanVM.Protocol.Whir.Complete

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Tables Finset

@[expose] public section

theorem one_add_one_E : (1 : E) + 1 = 0 := by
  rw [one_add_one_eq_two, two_eq_zero_E]

theorem foldl_add_eq (l : List E) (a : E) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.sum_cons, add_assoc]

theorem foldl_mul_eq (l : List E) (a : E) : l.foldl (· * ·) a = a * l.prod := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.prod_cons, mul_assoc]

theorem sum_range_two_mul (f : ℕ → E) (n : ℕ) :
    ∑ i ∈ range (2 * n), f i = ∑ j ∈ range n, (f (2 * j) + f (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, add_assoc]

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

end

end LeanVM.Protocol.Whir.Complete
