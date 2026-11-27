/-
  LeanVM.Guest.B2C.KernelList

  List functions written with the recursor, for the checkers the kernel evaluates.
-/

module

public import Mathlib.Init

/-!
# Lists, by the recursor

The kernel reduces a function defined by structural recursion through its `brecOn` encoding and
its `match`, several times slower per element than the same function written with `List.rec`:
`List.all`, `List.any`, `List.map`, `List.foldl` and `List.zipIdx` cost the checkers that the
kernel evaluates (`decide +kernel`) more than the work they do. `allR`, `anyR`, `mapR`, `foldlR`
and `zipIdxR` are those functions by the recursor, equal to them (`allR_eq`, …). A checker uses
them in its hot steps, and an equation lemma states the step in the structural form its proofs
read.
-/

namespace LeanVM.Guest.B2C

@[expose] public section

variable {α β : Type}

/-- `List.all`, by the recursor. -/
noncomputable def allR (p : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ ↦ Bool) true (fun a _ r ↦ p a && r) l

/-- `List.any`, by the recursor. -/
noncomputable def anyR (p : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ ↦ Bool) false (fun a _ r ↦ p a || r) l

/-- `List.map`, by the recursor. -/
noncomputable def mapR (f : α → β) (l : List α) : List β :=
  List.rec (motive := fun _ ↦ List β) [] (fun a _ r ↦ f a :: r) l

/-- `List.foldl`, by the recursor. -/
noncomputable def foldlR (f : β → α → β) (b : β) (l : List α) : β :=
  List.rec (motive := fun _ ↦ β → β) (fun b ↦ b) (fun a _ r b ↦ r (f b a)) l b

/-- `List.zipIdx`, by the recursor. -/
noncomputable def zipIdxR (l : List α) (n : Nat) : List (α × Nat) :=
  List.rec (motive := fun _ ↦ Nat → List (α × Nat)) (fun _ ↦ []) (fun a _ r n ↦ (a, n) :: r (n + 1)) l n

theorem allR_eq (p : α → Bool) : ∀ l : List α, allR p l = l.all p
  | [] => rfl
  | a :: l => congrArg (p a && ·) (allR_eq p l)

theorem anyR_eq (p : α → Bool) : ∀ l : List α, anyR p l = l.any p
  | [] => rfl
  | a :: l => congrArg (p a || ·) (anyR_eq p l)

theorem mapR_eq (f : α → β) : ∀ l : List α, mapR f l = l.map f
  | [] => rfl
  | a :: l => congrArg (f a :: ·) (mapR_eq f l)

theorem foldlR_eq (f : β → α → β) : ∀ (b : β) (l : List α), foldlR f b l = l.foldl f b
  | _, [] => rfl
  | b, a :: l => foldlR_eq f (f b a) l

theorem zipIdxR_eq : ∀ (l : List α) (n : Nat), zipIdxR l n = l.zipIdx n
  | [], _ => rfl
  | a :: l, n => congrArg ((a, n) :: ·) (zipIdxR_eq l (n + 1))

end
end LeanVM.Guest.B2C
