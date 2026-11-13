/-
  LeanVM.Guest.B1.Whir.TableMem

  Membership in the tables of named entries, decided with the numbers compared before the names.
-/

module

/-!
# Deciding membership in a table of named entries

The kernel compares strings slowly. `decMemBy pre` decides `x ∈ t` entry by entry, `pre` first,
and compares an entry with `x` in full only where `pre` holds. The scoped instances (`open scoped
TableMem`) give the helpers' tables (`lpTable`, `lqTable`, `lrTable`) and the name-number tables
(`queryWindowsShapes`, `merkleCapNames`, ...) their numbers as `pre`.
-/

namespace LeanVM.Guest.B1.Whir

@[expose] public section

/-- Membership decided entry by entry, `pre` first: an entry it rejects is passed over without
comparing the rest. -/
def decMemBy {α : Type} [BEq α] [LawfulBEq α] (pre : α → α → Bool) (hpre : ∀ a, pre a a = true)
    (x : α) (t : List α) : Decidable (x ∈ t) :=
  decidable_of_iff (t.any fun e ↦ pre e x && e == x) <| by
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
    exact ⟨fun ⟨e, he, _, h⟩ ↦ h ▸ he, fun h ↦ ⟨x, h, hpre x, rfl⟩⟩

namespace TableMem

/-- `lpTable`'s entries, by squeezes, depth and cap depth. -/
scoped instance (priority := high) (x : String × Nat × String × Nat × Nat)
    (t : List (String × Nat × String × Nat × Nat)) : Decidable (x ∈ t) :=
  decMemBy (fun e x ↦ e.2.1 == x.2.1 && e.2.2.2.1 == x.2.2.2.1 && e.2.2.2.2 == x.2.2.2.2)
    (by simp) x t

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 2048 in
/-- `lqTable`'s entries, by queries, base, folds and leaf cells. -/
scoped instance (priority := high) (x : String × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat)
    (t : List (String × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat)) :
    Decidable (x ∈ t) :=
  decMemBy (fun e x ↦ e.2.1 == x.2.1 && e.2.2.1 == x.2.2.1 && e.2.2.2.1 == x.2.2.2.1 &&
    e.2.2.2.2.1 == x.2.2.2.2.1) (by simp) x t

/-- `lrTable`'s entries, by queries, columns, folds and high bits. -/
scoped instance (priority := high) (x : String × Nat × Nat × Nat × Nat × String × String)
    (t : List (String × Nat × Nat × Nat × Nat × String × String)) : Decidable (x ∈ t) :=
  decMemBy (fun e x ↦ e.2.1 == x.2.1 && e.2.2.1 == x.2.2.1 && e.2.2.2.1 == x.2.2.2.1 &&
    e.2.2.2.2.1 == x.2.2.2.2.1) (by simp) x t

/-- Entries `(name, a, b)`, by `a` and `b`. -/
scoped instance (priority := high) (x : String × Nat × Nat) (t : List (String × Nat × Nat)) :
    Decidable (x ∈ t) :=
  decMemBy (fun e x ↦ e.2.1 == x.2.1 && e.2.2 == x.2.2) (by simp) x t

/-- Entries `(name, a)`, by `a`. -/
scoped instance (priority := high) (x : String × Nat) (t : List (String × Nat)) :
    Decidable (x ∈ t) :=
  decMemBy (fun e x ↦ e.2 == x.2) (by simp) x t

end TableMem

end
end LeanVM.Guest.B1.Whir
