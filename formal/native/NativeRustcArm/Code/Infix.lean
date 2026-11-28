module

public import Kraken.Data.List.Infix

/-!
# Where a list sits in a concatenation

`List.isInfixAt_flatten_of`: the `i`th list of `ls` sits in `ls.flatten` after the lengths of the
lists before it; `List.IsInfixAt.trans` composes two such facts. The ingested programs
(`NativeRustcArm.Code.*`) give each block's index in its function and in the whole program by them.
-/

namespace List

variable {α : Type _}

/-- A nonempty infix of an infix is an infix. -/
public theorem IsInfixAt.trans {a b c : List α} {j k : Nat} (h₁ : a.IsInfixAt b j)
    (h₂ : b.IsInfixAt c k) (ha : a ≠ []) : a.IsInfixAt c (k + j) := by
  obtain ⟨t₁, ht₁⟩ := h₁
  obtain ⟨t₂, ht₂⟩ := h₂
  have hj : j ≤ b.length := by
    refine Nat.le_of_not_lt fun hlt => ha ?_
    rw [List.drop_eq_nil_of_le (Nat.le_of_lt hlt)] at ht₁
    exact List.append_eq_nil_iff.mp ht₁ |>.1
  refine ⟨t₁ ++ t₂, ?_⟩
  rw [← List.drop_drop, ← ht₂, List.drop_append_of_le_length hj, ← ht₁, List.append_assoc]

public theorem isInfixAt_flatten {ls : List (List α)} {i : Nat} {b : List α}
    (h : ls[i]? = some b) : b.IsInfixAt ls.flatten ((ls.take i).map List.length).sum := by
  induction ls generalizing i with
  | nil => simp at h
  | cons l ls ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact ⟨ls.flatten, by simp⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      obtain ⟨t, ht⟩ := ih h
      refine ⟨t, ?_⟩
      simp [List.flatten_cons, ← List.drop_drop, ht]

public theorem isInfixAt_flatten_of {ls : List (List α)} {i k : Nat} {b : List α}
    (h : ls[i]? = some b) (hk : ((ls.take i).map List.length).sum = k) :
    b.IsInfixAt ls.flatten k :=
  hk ▸ isInfixAt_flatten h

end List
