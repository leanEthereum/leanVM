/-
  LeanVM.Guest.Memory.CallCount

  How many times a path can call a function: at most the syntactic bound of its block.
-/

module

public import LeanVM.Guest.Memory.SizeTotal

/-!
# Calls of one function along a path

`Stmt.blockBound g ss`: the most calls of `g` a path through `ss` sets up, read off the syntax (a branch's or a
match's most of its arms, a dispatch's one if `g` is among its callees). `walk_count`: a path of `ss` sets up at
most that many frames of `g`.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

mutual
/-- The most calls of `g` a statement's path sets up. -/
def Stmt.callBound (g : String) : Stmt → ℕ
  | .ite _ z n => max (Stmt.blockBound g z) (Stmt.blockBound g n)
  | .match_ _ arms => Stmt.armsBound g arms
  | .call f _ _ => if f = g then 1 else 0
  | .callIf _ f _ => if f = g then 1 else 0
  | .dispatch _ fs _ _ => if g ∈ fs then 1 else 0
  | _ => 0

/-- The most calls of `g` a block's path sets up. -/
def Stmt.blockBound (g : String) : List Stmt → ℕ
  | [] => 0
  | s :: ss => Stmt.callBound g s + Stmt.blockBound g ss

/-- The most calls of `g` any arm's path sets up. -/
def Stmt.armsBound (g : String) : List (List Stmt) → ℕ
  | [] => 0
  | a :: as => max (Stmt.blockBound g a) (Stmt.armsBound g as)
end

section

variable {σ : Val} (g : String)

/-- The frames of `g` an outcome's events set up. -/
noncomputable def Out.nCalls (o : Out) : ℕ := ((calls o.evs).filter (·.f == g)).length

theorem Out.nCalls_seq (o k : Out) : (o.seq k).nCalls g ≤ o.nCalls g + k.nCalls g := by
  rcases o with es | ⟨es, vs⟩ | _ <;> rcases k with es' | ⟨es', vs'⟩ | _ <;>
    simp [Out.seq, Out.pre, Out.nCalls, Out.evs, calls, List.filterMap_append, List.filter_append]

theorem Out.nCalls_pre_inK (c : V) (o : Out) : (o.pre [.inK c]).nCalls g = o.nCalls g := by
  rw [Out.nCalls, Out.nCalls, Out.calls_pre_inK]

theorem pick_nCalls {x : V} {args rets : List V} : ∀ (gs : List String) (j : ℕ),
    (pick σ x args rets j gs).nCalls g ≤ if g ∈ gs then 1 else 0
  | [], _ => by simp [pick, Out.nCalls, Out.evs, calls]
  | f :: gs, j => by
      have ih := pick_nCalls (x := x) (args := args) (rets := rets) gs (j + 1)
      unfold pick
      by_cases hx : σ x = Parameters.ofK (Parameters.addressOfIndex j)
      · simp only [hx, ↓reduceIte]
        by_cases hf : f = g
        · subst hf; simp [Out.nCalls, Out.evs, calls, Ev.call?]
        · simp [Out.nCalls, Out.evs, calls, Ev.call?, hf]
      · simp only [hx, ↓reduceIte]
        refine ih.trans ?_
        split_ifs <;> simp_all

mutual
/-- **A statement's path calls `g` at most its bound.** -/
theorem walk1_count : ∀ s : Stmt, (walk1 σ s).nCalls g ≤ Stmt.callBound g s
  | .atom a => by simp [walk1, Out.nCalls, Out.evs, calls, List.filterMap_cons, Ev.call?, Stmt.callBound]
  | .ite b z m => by
      rw [walk1, Out.nCalls_pre_inK, Stmt.callBound]
      split_ifs
      · exact (walk_count z).trans (le_max_left _ _)
      · exact (walk_count m).trans (le_max_right _ _)
  | .match_ x arms => by
      rw [walk1, Stmt.callBound]
      exact walkArms_count x arms 0
  | .call f args rets => by
      simp only [walk1, Out.nCalls, Out.evs, calls, List.filterMap_cons, Ev.call?, List.filterMap_nil,
        Stmt.callBound, List.filter_cons]
      split_ifs <;> simp_all
  | .callIf b f args => by
      rw [walk1, Stmt.callBound]
      split_ifs <;>
        simp_all [Out.nCalls, Out.evs, calls, List.filterMap_cons, Ev.call?]
  | .dispatch x gs args rets => by
      rw [walk1, Stmt.callBound]
      exact pick_nCalls g gs 0
  | .ret _ => by simp [walk1, Out.nCalls, Out.evs, calls]

/-- **A block's path calls `g` at most its bound.** -/
theorem walk_count : ∀ ss : List Stmt, (walk σ ss).nCalls g ≤ Stmt.blockBound g ss
  | [] => by simp [walk, Out.nCalls, Out.evs, calls]
  | s :: ss => by
      rw [walk, Stmt.blockBound]
      exact (Out.nCalls_seq g _ _).trans (Nat.add_le_add (walk1_count s) (walk_count ss))

theorem walkArms_count (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ),
    (walkArms σ x j arms).nCalls g ≤ Stmt.armsBound g arms
  | [], _ => by simp [walkArms, Out.nCalls, Out.evs, calls]
  | a :: as, j => by
      unfold walkArms
      rw [Stmt.armsBound]
      split_ifs
      · exact (walk_count a).trans (le_max_left _ _)
      · exact (walkArms_count x as (j + 1)).trans (le_max_right _ _)
end

/-- **A path's frames of `g`** are at most its block's bound. -/
theorem calls_count {ss : List Stmt} {es : List Ev} {vs : List V} (hw : walk σ ss = .ret es vs) :
    ((calls es).filter (·.f == g)).length ≤ Stmt.blockBound g ss := by
  have := walk_count (σ := σ) g ss
  rwa [hw] at this

end

end

end LeanVM.Guest.Memory
