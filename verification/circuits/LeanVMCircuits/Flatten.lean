module

public import LeanVMCircuits.Lowering

@[expose] public section

namespace LeanVMCircuits.Flock

def concatenate {α : Type} : List (Except String (List α)) → Except String (List α)
  | [] => .ok []
  | .error message :: _ => .error message
  | .ok head :: tail =>
    match concatenate tail with
    | .error message => .error message
    | .ok rest => .ok (head ++ rest)

/-- A bounded, kernel-computable flattening of Clean subcircuits. Excess nesting is an error. -/
def flatten : ℕ → NestedOperations Bit → Except String (List (FlatOperation Bit))
  | 0, _ => .error "Flock export exceeds the supported subcircuit nesting depth"
  | _ + 1, .single operation => .ok [operation]
  | depth + 1, .nested (_, children) => concatenate (children.map (flatten depth))

private theorem concatenate_correct {α β : Type} (xs : List α)
    (f : α → Except String (List β)) (g : α → List β)
    (hfg : ∀ x ∈ xs, ∀ result, f x = .ok result → result = g x)
    (result : List β) (h : concatenate (xs.map f) = .ok result) :
    result = xs.flatMap g := by
  induction xs generalizing result with
  | nil => simp [concatenate] at h; subst result; rfl
  | cons x xs ih =>
    cases hx : f x with
    | error message => simp [concatenate, hx] at h
    | ok head =>
      cases ht : concatenate (xs.map f) with
      | error message => simp [concatenate, hx, ht] at h
      | ok tail =>
        simp [concatenate, hx, ht] at h
        subst result
        rw [hfg x (by simp) head hx, ih (fun x hmem => hfg x (by simp [hmem])) tail ht]
        rfl

/-- The bounded flattener agrees with Clean's actual nested semantics whenever it succeeds. -/
theorem flatten_correct (depth : ℕ) (nested : NestedOperations Bit)
    (operations : List (FlatOperation Bit)) (h : flatten depth nested = .ok operations) :
    operations = nested.toFlat := by
  induction depth generalizing nested operations with
  | zero => simp [flatten] at h
  | succ depth ih =>
    cases nested with
    | single operation => simpa only [flatten, NestedOperations.toFlat, Except.ok.injEq] using h.symm
    | nested pair =>
      rcases pair with ⟨name, children⟩
      simp only [flatten, NestedOperations.toFlat] at h ⊢
      exact concatenate_correct children (flatten depth) NestedOperations.toFlat
        (fun child _ result hchild => ih child result hchild) operations h

end LeanVMCircuits.Flock
