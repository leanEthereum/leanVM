/-
  LeanVM.Guest.Exact.Atoms

  Every atom of a block passing a test (`Stmt.atomsAll`), split over appended blocks, and a block with no computed
  hint passing the pinned-hint check (`blockNextOk_of_atomsAll`).
-/

module

public import LeanVM.Guest.Exact.Defs
public import LeanVM.Guest.Memory.SizeTotal

/-!
# Every atom

`Stmt.atomsAll p ss`: every atom of `ss`, in nested blocks too, satisfies `p`. It distributes over `++`
(`atomsAll_append`), as `Stmt.blockCallees` does (`blockCallees_append`), so a large body is checked by pieces, each in
a kernel evaluation of its own. A block none of whose atoms satisfies `p` passes `Stmt.blockNextOk p q`
(`blockNextOk_of_atomsAll`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core

@[expose] public section

/-- A computed hint: a hint the executor computes from what it reads. -/
def isComputed : Atom → Bool
  | .hint (.witness ..) => false
  | .hint (.alloc ..) => false
  | .hint (.allocDyn ..) => false
  | .hint _ => true
  | _ => false

end
end LeanVM.Guest.Memory

namespace LeanVM.Guest.Core

@[expose] public section

mutual
/-- **Every atom of the block satisfies `p`**, in the blocks nested in it too. -/
def Stmt.atomsAll (p : Atom → Bool) : List Stmt → Bool
  | [] => true
  | .atom a :: rest => p a && Stmt.atomsAll p rest
  | .ite _ z n :: rest => (Stmt.atomsAll p z && Stmt.atomsAll p n) && Stmt.atomsAll p rest
  | .match_ _ arms :: rest => Stmt.armsAtomsAll p arms && Stmt.atomsAll p rest
  | .call .. :: rest => Stmt.atomsAll p rest
  | .callIf .. :: rest => Stmt.atomsAll p rest
  | .dispatch .. :: rest => Stmt.atomsAll p rest
  | .ret _ :: rest => Stmt.atomsAll p rest

/-- `Stmt.atomsAll` of every arm. -/
def Stmt.armsAtomsAll (p : Atom → Bool) : List (List Stmt) → Bool
  | [] => true
  | a :: as => Stmt.atomsAll p a && Stmt.armsAtomsAll p as
end

variable {p : Atom → Bool} {q : Atom → Atom → Bool}

theorem Stmt.atomsAll_append : ∀ (l l' : List Stmt),
    Stmt.atomsAll p (l ++ l') = (Stmt.atomsAll p l && Stmt.atomsAll p l')
  | [], _ => by simp [Stmt.atomsAll]
  | .atom _ :: l, l' | .ite .. :: l, l' | .match_ .. :: l, l' | .call .. :: l, l' | .callIf .. :: l, l'
  | .dispatch .. :: l, l' | .ret _ :: l, l' => by
      simp only [List.cons_append, Stmt.atomsAll, Stmt.atomsAll_append l l', Bool.and_assoc]

mutual
/-- **A block none of whose atoms satisfies `p` passes `Stmt.blockNextOk p q`.** -/
theorem blockNextOk_of_atomsAll : ∀ (ss : List Stmt), Stmt.atomsAll (fun a => !p a) ss = true →
    Stmt.blockNextOk p q ss = true
  | [], _ => by rw [Stmt.blockNextOk]
  | .atom a :: rest, h => by
      rw [Stmt.atomsAll, Bool.and_eq_true] at h
      have hp : p a = false := by simpa using h.1
      have hh : Stmt.headOk p q a rest = true := by
        unfold Stmt.headOk; split <;> simp [hp]
      rw [Stmt.blockNextOk, hh, blockNextOk_of_atomsAll rest h.2]; rfl
  | .ite _ z n :: rest, h => by
      simp only [Stmt.atomsAll, Bool.and_eq_true] at h
      rw [Stmt.blockNextOk, blockNextOk_of_atomsAll z h.1.1, blockNextOk_of_atomsAll n h.1.2,
        blockNextOk_of_atomsAll rest h.2]; rfl
  | .match_ _ arms :: rest, h => by
      simp only [Stmt.atomsAll, Bool.and_eq_true] at h
      rw [Stmt.blockNextOk, armsNextOk_of_atomsAll arms h.1, blockNextOk_of_atomsAll rest h.2]; rfl
  | .call .. :: rest, h => by
      rw [Stmt.atomsAll] at h; rw [Stmt.blockNextOk]; exact blockNextOk_of_atomsAll rest h
  | .callIf .. :: rest, h => by
      rw [Stmt.atomsAll] at h; rw [Stmt.blockNextOk]; exact blockNextOk_of_atomsAll rest h
  | .dispatch .. :: rest, h => by
      rw [Stmt.atomsAll] at h; rw [Stmt.blockNextOk]; exact blockNextOk_of_atomsAll rest h
  | .ret _ :: rest, h => by
      rw [Stmt.atomsAll] at h; rw [Stmt.blockNextOk]; exact blockNextOk_of_atomsAll rest h

/-- `blockNextOk_of_atomsAll` for arms. -/
theorem armsNextOk_of_atomsAll : ∀ (as : List (List Stmt)), Stmt.armsAtomsAll (fun a => !p a) as = true →
    Stmt.armsNextOk p q as = true
  | [], _ => by rw [Stmt.armsNextOk]
  | a :: as, h => by
      rw [Stmt.armsAtomsAll, Bool.and_eq_true] at h
      rw [Stmt.armsNextOk, blockNextOk_of_atomsAll a h.1, armsNextOk_of_atomsAll as h.2]; rfl
end

end
end LeanVM.Guest.Core

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core

@[expose] public section

theorem Stmt.blockCallees_append : ∀ (l l' : List Stmt),
    Stmt.blockCallees (l ++ l') = Stmt.blockCallees l ++ Stmt.blockCallees l'
  | [], _ => by simp [Stmt.blockCallees]
  | s :: l, l' => by
      rw [List.cons_append, Stmt.blockCallees, Stmt.blockCallees, Stmt.blockCallees_append l l', List.append_assoc]

end
end LeanVM.Guest.Memory
