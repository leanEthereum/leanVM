module

public import LeanVM.Guest.Memory.Fresh

/-!
# The callees of a block

`Stmt.blockCallees` lists the functions a block can call, its calls, conditional calls and
dispatches' targets, both sides of a branch and every arm of a `match`; a path calls only them
(`walk_callees`). Syntax only, beside any layout.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

mutual
/-- The functions a statement can call. -/
def Stmt.callees : Stmt → List String
  | .ite _ z n => Stmt.blockCallees z ++ Stmt.blockCallees n
  | .match_ _ arms => Stmt.armsCallees arms
  | .call f _ _ => [f]
  | .callIf _ f _ => [f]
  | .dispatch _ fs _ _ => fs
  | _ => []

/-- The functions a block can call. -/
def Stmt.blockCallees : List Stmt → List String
  | [] => []
  | s :: ss => Stmt.callees s ++ Stmt.blockCallees ss

/-- The functions any arm can call. -/
def Stmt.armsCallees : List (List Stmt) → List String
  | [] => []
  | a :: as => Stmt.blockCallees a ++ Stmt.armsCallees as
end

section Syntax

variable {σ : Val}

theorem Out.calls_seq {o k : Out} {c : Call} (h : c ∈ calls (o.seq k).evs) :
    c ∈ calls o.evs ∨ c ∈ calls k.evs := by
  rcases o with es | ⟨es, vs⟩ | _ <;> rcases k with es' | ⟨es', vs'⟩ | _ <;>
    simp_all [Out.seq, Out.pre, Out.evs, calls, List.filterMap_append]

theorem Out.calls_pre_inK (c : V) (o : Out) : calls (o.pre [.inK c]).evs = calls o.evs := by
  rcases o with es | ⟨es, vs⟩ | _ <;> simp [Out.pre, Out.evs, calls, Ev.call?, List.filterMap_cons]

/-- A dispatch calls one of its targets. -/
theorem pick_callees {x : V} {args rets : List V} : ∀ (gs : List String) (j : ℕ),
    ∀ c ∈ calls (pick σ x args rets j gs).evs, c.f ∈ gs
  | [], _ => by simp [pick, Out.evs, calls]
  | g :: gs, j => by
      unfold pick
      split_ifs
      · simp [Out.evs, calls, Ev.call?]
      · exact fun c hc => List.mem_cons_of_mem _ (pick_callees gs (j + 1) c hc)

mutual
/-- **A statement's path calls its callees.** -/
theorem walk1_callees : ∀ (s : Stmt) {c : Call}, c ∈ calls (walk1 σ s).evs → c.f ∈ Stmt.callees s
  | .atom a, c, h => by simp [walk1, Out.evs, calls, Ev.call?] at h
  | .ite b z m, c, h => by
      rw [walk1, Out.calls_pre_inK] at h
      simp only [Stmt.callees, List.mem_append]
      split_ifs at h
      · exact Or.inl (walk_callees z h)
      · exact Or.inr (walk_callees m h)
  | .match_ x arms, c, h => by
      rw [walk1] at h
      exact walkArms_callees x arms 0 h
  | .call f args rets, c, h => by
      simp only [walk1, Out.evs, calls, List.filterMap_cons, Ev.call?, List.filterMap_nil,
        List.mem_cons, List.not_mem_nil, or_false] at h
      subst h; simp [Stmt.callees]
  | .callIf b f args, c, h => by
      rw [walk1] at h
      split_ifs at h <;>
        simp only [Out.evs, calls, List.filterMap_cons, Ev.call?, List.filterMap_nil,
          List.mem_cons, List.not_mem_nil, or_false] at h <;> subst h <;> simp [Stmt.callees]
  | .dispatch x gs args rets, c, h => by
      rw [walk1] at h
      exact pick_callees gs 0 c h
  | .ret _, c, h => by simp [walk1, Out.evs, calls] at h

/-- **A block's path calls its callees.** -/
theorem walk_callees : ∀ (ss : List Stmt) {c : Call}, c ∈ calls (walk σ ss).evs →
    c.f ∈ Stmt.blockCallees ss
  | [], c, h => by simp [walk, Out.evs, calls] at h
  | s :: ss, c, h => by
      rw [walk] at h
      simp only [Stmt.blockCallees, List.mem_append]
      rcases Out.calls_seq h with h | h
      · exact Or.inl (walk1_callees s h)
      · exact Or.inr (walk_callees ss h)

theorem walkArms_callees (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ) {c : Call},
    c ∈ calls (walkArms σ x j arms).evs → c.f ∈ Stmt.armsCallees arms
  | [], _, c, h => by simp [walkArms, Out.evs, calls] at h
  | a :: as, j, c, h => by
      unfold walkArms at h
      simp only [Stmt.armsCallees, List.mem_append]
      split_ifs at h
      · exact Or.inl (walk_callees a h)
      · exact Or.inr (walkArms_callees x as (j + 1) h)
end

end Syntax

end
end LeanVM.Guest.Memory
