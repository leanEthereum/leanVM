/-
  LeanVM.Guest.CoreMode.StmtWalk

  A body's statements, nested ones included, walked by the recursor without building their list.
-/

module

public import LeanVM.Guest.Bridge.JumpCellsDefs

/-!
# Walks of a body's statements, for the kernel

A check `(stmtsOf body).all p` builds the list of a body's statements, nested ones included, by `++`
and the compiled form of structural recursion, then walks it; the kernel reduces both slowly, and a
core certificate runs such a check on a long body several times. `stmtsAll p body` is the same
check in one pass of the recursor, `stmtsFM f body acc` the same for `(stmtsOf body).filterMap f ++ acc`;
`stmtsAll_eq` and `stmtsFM_eq` are the equalities.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest.Core LeanVM.Guest.Bridge

@[expose] public section

/-- `(stmtsOf l).all p`, by the recursor. -/
noncomputable def stmtsAll (p : Stmt → Bool) : List Stmt → Bool :=
  Stmt.rec_1 (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun _ ↦ true) (fun _ _ _ hz hn ↦ hz && hn) (fun _ _ ha ↦ ha) (fun _ _ _ ↦ true) (fun _ _ _ ↦ true)
    (fun _ _ _ _ ↦ true) (fun _ ↦ true) true (fun s _ hs hss ↦ p s && hs && hss) true (fun _ _ ha has ↦ ha && has)

/-- `(stmtsSub s).all p`, by the recursor. -/
noncomputable def subAll (p : Stmt → Bool) : Stmt → Bool :=
  Stmt.rec (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun _ ↦ true) (fun _ _ _ hz hn ↦ hz && hn) (fun _ _ ha ↦ ha) (fun _ _ _ ↦ true) (fun _ _ _ ↦ true)
    (fun _ _ _ _ ↦ true) (fun _ ↦ true) true (fun s _ hs hss ↦ p s && hs && hss) true (fun _ _ ha has ↦ ha && has)

/-- `(stmtsOf l).filterMap f ++ acc`, by the recursor. -/
noncomputable def stmtsFM {β : Type} (f : Stmt → Option β) : List Stmt → List β → List β :=
  Stmt.rec_1 (motive_1 := fun _ ↦ List β → List β) (motive_2 := fun _ ↦ List β → List β)
    (motive_3 := fun _ ↦ List β → List β)
    (fun _ acc ↦ acc) (fun _ _ _ hz hn acc ↦ hz (hn acc)) (fun _ _ ha ↦ ha) (fun _ _ _ acc ↦ acc)
    (fun _ _ _ acc ↦ acc) (fun _ _ _ _ acc ↦ acc) (fun _ acc ↦ acc) (fun acc ↦ acc)
    (fun s _ hs hss acc ↦ match f s with
      | some b => b :: hs (hss acc)
      | none => hs (hss acc))
    (fun acc ↦ acc) (fun _ _ ha has acc ↦ ha (has acc))

end

section

private noncomputable def armsAll (p : Stmt → Bool) : List (List Stmt) → Bool :=
  Stmt.rec_2 (motive_1 := fun _ ↦ Bool) (motive_2 := fun _ ↦ Bool) (motive_3 := fun _ ↦ Bool)
    (fun _ ↦ true) (fun _ _ _ hz hn ↦ hz && hn) (fun _ _ ha ↦ ha) (fun _ _ _ ↦ true) (fun _ _ _ ↦ true)
    (fun _ _ _ _ ↦ true) (fun _ ↦ true) true (fun s _ hs hss ↦ p s && hs && hss) true (fun _ _ ha has ↦ ha && has)

private noncomputable def subFM {β : Type} (f : Stmt → Option β) : Stmt → List β → List β :=
  Stmt.rec (motive_1 := fun _ ↦ List β → List β) (motive_2 := fun _ ↦ List β → List β)
    (motive_3 := fun _ ↦ List β → List β)
    (fun _ acc ↦ acc) (fun _ _ _ hz hn acc ↦ hz (hn acc)) (fun _ _ ha ↦ ha) (fun _ _ _ acc ↦ acc)
    (fun _ _ _ acc ↦ acc) (fun _ _ _ _ acc ↦ acc) (fun _ acc ↦ acc) (fun acc ↦ acc)
    (fun s _ hs hss acc ↦ match f s with
      | some b => b :: hs (hss acc)
      | none => hs (hss acc))
    (fun acc ↦ acc) (fun _ _ ha has acc ↦ ha (has acc))

private noncomputable def armsFM {β : Type} (f : Stmt → Option β) : List (List Stmt) → List β → List β :=
  Stmt.rec_2 (motive_1 := fun _ ↦ List β → List β) (motive_2 := fun _ ↦ List β → List β)
    (motive_3 := fun _ ↦ List β → List β)
    (fun _ acc ↦ acc) (fun _ _ _ hz hn acc ↦ hz (hn acc)) (fun _ _ ha ↦ ha) (fun _ _ _ acc ↦ acc)
    (fun _ _ _ acc ↦ acc) (fun _ _ _ _ acc ↦ acc) (fun _ acc ↦ acc) (fun acc ↦ acc)
    (fun s _ hs hss acc ↦ match f s with
      | some b => b :: hs (hss acc)
      | none => hs (hss acc))
    (fun acc ↦ acc) (fun _ _ ha has acc ↦ ha (has acc))

variable (p : Stmt → Bool)

mutual
private theorem subAll_eq' : ∀ s, subAll p s = (stmtsSub s).all p
  | .atom _ => rfl
  | .ite _ z n => by
    change (stmtsAll p z && stmtsAll p n) = _
    rw [stmtsAll_eq' z, stmtsAll_eq' n, stmtsSub, List.all_append]
  | .match_ _ arms => by
    change armsAll p arms = _
    rw [armsAll_eq' arms, stmtsSub]
  | .call .. => rfl
  | .callIf .. => rfl
  | .dispatch .. => rfl
  | .ret _ => rfl

private theorem stmtsAll_eq' : ∀ l, stmtsAll p l = (stmtsOf l).all p
  | [] => rfl
  | s :: ss => by
    change (p s && subAll p s && stmtsAll p ss) = _
    rw [subAll_eq' s, stmtsAll_eq' ss, stmtsOf, List.all_cons, List.all_append, Bool.and_assoc]

private theorem armsAll_eq' : ∀ as, armsAll p as = (stmtsArms as).all p
  | [] => rfl
  | a :: as => by
    change (stmtsAll p a && armsAll p as) = _
    rw [stmtsAll_eq' a, armsAll_eq' as, stmtsArms, List.all_append]
end

variable {β : Type} (f : Stmt → Option β)

mutual
private theorem subFM_eq : ∀ s acc, subFM f s acc = (stmtsSub s).filterMap f ++ acc
  | .atom _, _ => rfl
  | .ite _ z n, acc => by
    change stmtsFM f z (stmtsFM f n acc) = _
    rw [stmtsFM_eq' z, stmtsFM_eq' n, stmtsSub, List.filterMap_append, List.append_assoc]
  | .match_ _ arms, acc => by
    change armsFM f arms acc = _
    rw [armsFM_eq arms, stmtsSub]
  | .call .., _ => rfl
  | .callIf .., _ => rfl
  | .dispatch .., _ => rfl
  | .ret _, _ => rfl

private theorem stmtsFM_eq' : ∀ l acc, stmtsFM f l acc = (stmtsOf l).filterMap f ++ acc
  | [], _ => rfl
  | s :: ss, acc => by
    change (match f s with
      | some b => b :: subFM f s (stmtsFM f ss acc)
      | none => subFM f s (stmtsFM f ss acc)) = _
    rw [subFM_eq s, stmtsFM_eq' ss, stmtsOf, List.filterMap_cons, List.filterMap_append]
    cases f s <;> simp

private theorem armsFM_eq : ∀ as acc, armsFM f as acc = (stmtsArms as).filterMap f ++ acc
  | [], _ => rfl
  | a :: as, acc => by
    change stmtsFM f a (armsFM f as acc) = _
    rw [stmtsFM_eq' a, armsFM_eq as, stmtsArms, List.filterMap_append, List.append_assoc]
end

end

public section

theorem stmtsAll_eq (p : Stmt → Bool) (l : List Stmt) : stmtsAll p l = (stmtsOf l).all p := stmtsAll_eq' p l

theorem subAll_eq (p : Stmt → Bool) (s : Stmt) : subAll p s = (stmtsSub s).all p := subAll_eq' p s

theorem stmtsFM_eq {β : Type} (f : Stmt → Option β) (l : List Stmt) (acc : List β) :
    stmtsFM f l acc = (stmtsOf l).filterMap f ++ acc := stmtsFM_eq' f l acc

/-- A check of every statement of a body, by the recursor, from each statement's. -/
theorem stmtsAll_of {p : Stmt → Bool} {l : List Stmt} (h : ∀ s ∈ stmtsOf l, p s = true) : stmtsAll p l = true := by
  rw [stmtsAll_eq]; exact List.all_eq_true.mpr h

/-- A check of every statement of a body, by the recursor. -/
theorem all_of_stmtsAll {p : Stmt → Bool} {l : List Stmt} (h : stmtsAll p l = true) : (stmtsOf l).all p = true :=
  stmtsAll_eq p l ▸ h

end

end LeanVM.Guest.CoreMode
