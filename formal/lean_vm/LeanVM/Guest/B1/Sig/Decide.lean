/-
  LeanVM.Guest.B1.Sig.Decide

  Equality of core statements decided by the kernel: words compared limb by limb.
-/

module

public import LeanVM.Guest.Renumber

/-!
# Deciding statement equality

`XmssData` and `SphincsData` compare the guest's data with the templates by `decide +kernel`. The
derived `DecidableEq E` (through `Vector`) does not reduce in the kernel, so words are compared by
their limbs (`eDecEq`, scoped to `Dec`), `Atom`'s equality is derived again over it, and `Stmt`'s,
which `Core` derives only as `BEq`, is written out (`stmtDecEq`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

namespace Dec

/-- Equality of words by their limbs. -/
scoped instance (priority := high) eDecEq : DecidableEq E := fun a b =>
  decidable_of_iff (a.limb 0 = b.limb 0 ∧ a.limb 1 = b.limb 1 ∧ a.limb 2 = b.limb 2) (by
    constructor
    · rintro ⟨h0, h1, h2⟩
      rw [← ofLimbs_limb a, ← ofLimbs_limb b, h0, h1, h2]
    · rintro rfl
      exact ⟨rfl, rfl, rfl⟩)

end Dec

namespace Dec

open scoped Dec in
deriving instance DecidableEq for Atom

end Dec

attribute [-instance] Dec.instDecidableEqAtom

/-- `Atom`'s equality over the limbs. -/
def atomDecEq : DecidableEq Atom := Dec.instDecidableEqAtom

mutual
/-- `Stmt`'s equality. -/
def stmtDecEq : (a b : Stmt) → Decidable (a = b)
  | .atom a, .atom b =>
      match atomDecEq a b with
      | isTrue h => isTrue (by rw [h])
      | isFalse h => isFalse (by intro e; cases e; exact h rfl)
  | .ite c z n, .ite c' z' n' =>
      if h : c = c' then
        match listDecEq z z', listDecEq n n' with
        | isTrue h1, isTrue h2 => isTrue (by rw [h, h1, h2])
        | isFalse h1, _ => isFalse (by intro e; cases e; exact h1 rfl)
        | _, isFalse h2 => isFalse (by intro e; cases e; exact h2 rfl)
      else isFalse (by intro e; cases e; exact h rfl)
  | .match_ x as, .match_ x' as' =>
      if h : x = x' then
        match armsDecEq as as' with
        | isTrue h1 => isTrue (by rw [h, h1])
        | isFalse h1 => isFalse (by intro e; cases e; exact h1 rfl)
      else isFalse (by intro e; cases e; exact h rfl)
  | .call f a r, .call f' a' r' =>
      if h : f = f' ∧ a = a' ∧ r = r' then isTrue (by rw [h.1, h.2.1, h.2.2])
      else isFalse (by intro e; cases e; exact h ⟨rfl, rfl, rfl⟩)
  | .callIf c f a, .callIf c' f' a' =>
      if h : c = c' ∧ f = f' ∧ a = a' then isTrue (by rw [h.1, h.2.1, h.2.2])
      else isFalse (by intro e; cases e; exact h ⟨rfl, rfl, rfl⟩)
  | .dispatch x fs a r, .dispatch x' fs' a' r' =>
      if h : x = x' ∧ fs = fs' ∧ a = a' ∧ r = r' then isTrue (by rw [h.1, h.2.1, h.2.2.1, h.2.2.2])
      else isFalse (by intro e; cases e; exact h ⟨rfl, rfl, rfl, rfl⟩)
  | .ret vs, .ret vs' =>
      if h : vs = vs' then isTrue (by rw [h]) else isFalse (by intro e; cases e; exact h rfl)
  | .atom _, .ite .. | .atom _, .match_ .. | .atom _, .call .. | .atom _, .callIf ..
  | .atom _, .dispatch .. | .atom _, .ret _ => isFalse (by intro e; cases e)
  | .ite .., .atom _ | .ite .., .match_ .. | .ite .., .call .. | .ite .., .callIf ..
  | .ite .., .dispatch .. | .ite .., .ret _ => isFalse (by intro e; cases e)
  | .match_ .., .atom _ | .match_ .., .ite .. | .match_ .., .call .. | .match_ .., .callIf ..
  | .match_ .., .dispatch .. | .match_ .., .ret _ => isFalse (by intro e; cases e)
  | .call .., .atom _ | .call .., .ite .. | .call .., .match_ .. | .call .., .callIf ..
  | .call .., .dispatch .. | .call .., .ret _ => isFalse (by intro e; cases e)
  | .callIf .., .atom _ | .callIf .., .ite .. | .callIf .., .match_ .. | .callIf .., .call ..
  | .callIf .., .dispatch .. | .callIf .., .ret _ => isFalse (by intro e; cases e)
  | .dispatch .., .atom _ | .dispatch .., .ite .. | .dispatch .., .match_ .. | .dispatch .., .call ..
  | .dispatch .., .callIf .. | .dispatch .., .ret _ => isFalse (by intro e; cases e)
  | .ret _, .atom _ | .ret _, .ite .. | .ret _, .match_ .. | .ret _, .call .. | .ret _, .callIf ..
  | .ret _, .dispatch .. => isFalse (by intro e; cases e)

/-- Blocks' equality. -/
def listDecEq : (a b : List Stmt) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro e; cases e)
  | _ :: _, [] => isFalse (by intro e; cases e)
  | s :: ss, s' :: ss' =>
      match stmtDecEq s s', listDecEq ss ss' with
      | isTrue h1, isTrue h2 => isTrue (by rw [h1, h2])
      | isFalse h1, _ => isFalse (by intro e; cases e; exact h1 rfl)
      | _, isFalse h2 => isFalse (by intro e; cases e; exact h2 rfl)

/-- Arms' equality. -/
def armsDecEq : (a b : List (List Stmt)) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro e; cases e)
  | _ :: _, [] => isFalse (by intro e; cases e)
  | s :: ss, s' :: ss' =>
      match listDecEq s s', armsDecEq ss ss' with
      | isTrue h1, isTrue h2 => isTrue (by rw [h1, h2])
      | isFalse h1, _ => isFalse (by intro e; cases e; exact h1 rfl)
      | _, isFalse h2 => isFalse (by intro e; cases e; exact h2 rfl)
end

namespace Dec

/-- Blocks' equality, for `decide +kernel`. -/
scoped instance : DecidableEq (List Stmt) := listDecEq

end Dec

end
end LeanVM.Guest.B1.Sig
