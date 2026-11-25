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
core certificate runs such a check on a long body several times. `stmtsFold g body acc` is
`(stmtsOf body).foldr g acc` in one pass of the recursor, `stmtsFold_eq` the equality. The checks
`stmtsAll` (`(stmtsOf body).all p`), `subAll` (`(stmtsSub s).all p`) and `stmtsFM`
(`(stmtsOf body).filterMap f`) are its instances.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest.Core LeanVM.Guest.Bridge

/-- `Stmt`'s recursor `r` (`Stmt.rec`, `rec_1` or `rec_2`) with the minor premises of a right fold
by `g : Stmt → γ → γ`. -/
local macro "stmt_fold% " r:ident γ:term:max g:term:max : term =>
  `($r (motive_1 := fun _ ↦ $γ → $γ) (motive_2 := fun _ ↦ $γ → $γ) (motive_3 := fun _ ↦ $γ → $γ)
    (fun _ acc ↦ acc) (fun _ _ _ hz hn acc ↦ hz (hn acc)) (fun _ _ ha ↦ ha) (fun _ _ _ acc ↦ acc)
    (fun _ _ _ acc ↦ acc) (fun _ _ _ _ acc ↦ acc) (fun _ acc ↦ acc) (fun acc ↦ acc)
    (fun s _ hs hss acc ↦ $g s (hs (hss acc))) (fun acc ↦ acc) (fun _ _ ha has acc ↦ ha (has acc)))

variable {γ : Type}

@[expose] public section

/-- `(stmtsOf l).foldr g acc`, by the recursor. -/
noncomputable def stmtsFold (g : Stmt → γ → γ) : List Stmt → γ → γ := stmt_fold% Stmt.rec_1 γ g

/-- `(stmtsSub s).foldr g acc`, by the recursor. -/
noncomputable def subFold (g : Stmt → γ → γ) : Stmt → γ → γ := stmt_fold% Stmt.rec γ g

/-- `(stmtsOf l).all p`, by the recursor. -/
noncomputable def stmtsAll (p : Stmt → Bool) (l : List Stmt) : Bool := stmtsFold (fun s acc ↦ p s && acc) l true

/-- `(stmtsSub s).all p`, by the recursor. -/
noncomputable def subAll (p : Stmt → Bool) (s : Stmt) : Bool := subFold (fun s acc ↦ p s && acc) s true

/-- `(stmtsOf l).filterMap f`, by the recursor. -/
noncomputable def stmtsFM {β : Type} (f : Stmt → Option β) (l : List Stmt) : List β :=
  stmtsFold (fun s acc ↦ match f s with
    | some b => b :: acc
    | none => acc) l []

end

section

private noncomputable def armsFold (g : Stmt → γ → γ) : List (List Stmt) → γ → γ := stmt_fold% Stmt.rec_2 γ g

variable (g : Stmt → γ → γ)

mutual
private theorem subFold_eq' : ∀ s acc, subFold g s acc = (stmtsSub s).foldr g acc
  | .atom _, _ => rfl
  | .ite _ z n, acc => by
    change stmtsFold g z (stmtsFold g n acc) = _
    rw [stmtsFold_eq' z, stmtsFold_eq' n, stmtsSub, List.foldr_append]
  | .match_ _ arms, acc => by
    change armsFold g arms acc = _
    rw [armsFold_eq arms, stmtsSub]
  | .call .., _ => rfl
  | .callIf .., _ => rfl
  | .dispatch .., _ => rfl
  | .ret _, _ => rfl

private theorem stmtsFold_eq' : ∀ l acc, stmtsFold g l acc = (stmtsOf l).foldr g acc
  | [], _ => rfl
  | s :: ss, acc => by
    change g s (subFold g s (stmtsFold g ss acc)) = _
    rw [subFold_eq' s, stmtsFold_eq' ss, stmtsOf, List.foldr_cons, List.foldr_append]

private theorem armsFold_eq : ∀ as acc, armsFold g as acc = (stmtsArms as).foldr g acc
  | [], _ => rfl
  | a :: as, acc => by
    change stmtsFold g a (armsFold g as acc) = _
    rw [stmtsFold_eq' a, armsFold_eq as, stmtsArms, List.foldr_append]
end

private theorem foldr_and (p : Stmt → Bool) : ∀ L : List Stmt, L.foldr (fun s acc ↦ p s && acc) true = L.all p
  | [] => rfl
  | _ :: L => by rw [List.foldr_cons, foldr_and p L, List.all_cons]

private theorem foldr_fm {β : Type} (f : Stmt → Option β) : ∀ L : List Stmt,
    L.foldr (fun s acc ↦ match f s with
      | some b => b :: acc
      | none => acc) [] = L.filterMap f
  | [] => rfl
  | s :: L => by
    rw [List.foldr_cons, foldr_fm f L, List.filterMap_cons]
    cases f s <;> rfl

end

public section

theorem stmtsFold_eq (g : Stmt → γ → γ) (l : List Stmt) (acc : γ) : stmtsFold g l acc = (stmtsOf l).foldr g acc :=
  stmtsFold_eq' g l acc

theorem stmtsAll_eq (p : Stmt → Bool) (l : List Stmt) : stmtsAll p l = (stmtsOf l).all p := by
  rw [stmtsAll, stmtsFold_eq, foldr_and]

theorem subAll_eq (p : Stmt → Bool) (s : Stmt) : subAll p s = (stmtsSub s).all p := by
  rw [subAll, subFold_eq', foldr_and]

theorem stmtsFM_eq {β : Type} (f : Stmt → Option β) (l : List Stmt) : stmtsFM f l = (stmtsOf l).filterMap f := by
  rw [stmtsFM, stmtsFold_eq, foldr_fm]

/-- A check of every statement of a body, by the recursor, from each statement's. -/
theorem stmtsAll_of {p : Stmt → Bool} {l : List Stmt} (h : ∀ s ∈ stmtsOf l, p s = true) : stmtsAll p l = true :=
  (stmtsAll_eq p l).trans (List.all_eq_true.mpr h)

end

end LeanVM.Guest.CoreMode
