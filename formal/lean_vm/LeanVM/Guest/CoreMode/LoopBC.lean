/-
  LeanVM.Guest.CoreMode.LoopBC

  A loop helper's body with calls: atoms and calls, its tail call, `ret []`.
-/

module

public import LeanVM.Guest.CoreMode.LoopB

/-!
# A loop helper's body with calls

`loopBC fn`: the body of atoms and calls, the tail call `callIf c fn.name args` with one word per
parameter, and `ret []`; the events of its statements before the tail (`acEv`), its path
(`walk_loopC`) and statements (`stmts_loopC`). A leaf loop helper's body is one (`loopBC_of_loopB`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Bridge (stmtsOf stmtsSub walk_ret_cons walk_callIf_cons walk_call_cons walk_atom_cons)

@[expose] public section

/-- An atom or a call. -/
def isAC : Stmt → Bool
  | .atom _ | .call .. => true
  | _ => false

/-- **A loop helper's body with calls**: atoms and calls, its tail call to itself with one word per
parameter, `ret []`. -/
def loopBC (fn : Fn) : Bool :=
  match fn.body.reverse with
  | .ret [] :: .callIf _ g args :: pre => (g == fn.name) && Nat.beq args.length fn.params.length && pre.all isAC
  | _ => false

theorem loopBC_of_loopB {fn : Fn} (h : loopB fn = true) : loopBC fn = true := by
  unfold loopB at h
  unfold loopBC
  split at h
  · rename_i c g args pre hrev
    rw [hrev]
    simp only [Bool.and_eq_true, List.all_eq_true] at h ⊢
    exact ⟨h.1, fun s hs ↦ by have := h.2 s hs; cases s <;> simp_all [isAtomS, isAC]⟩
  · cases h

theorem loopBC_spec {fn : Fn} (h : loopBC fn = true) : ∃ (pre : List Stmt) (c : V) (args : List V),
    fn.body = pre ++ [.callIf c fn.name args, .ret []] ∧ args.length = fn.params.length ∧ ∀ s ∈ pre, isAC s = true := by
  unfold loopBC at h
  split at h
  · rename_i c g args pre hrev
    simp only [Bool.and_eq_true, beq_iff_eq, Nat.beq_eq, List.all_eq_true] at h
    obtain ⟨⟨rfl, hlen⟩, hpre⟩ := h
    refine ⟨pre.reverse, c, args, ?_, hlen, fun s hs ↦ hpre s (List.mem_reverse.mp hs)⟩
    rw [← List.reverse_reverse fn.body, hrev]
    simp
  · cases h

/-- The event of an atom or a call. -/
def acEv : Stmt → Ev
  | .atom a => .atom a
  | .call f args rets => .call f args rets
  | _ => .skip "" []

theorem walk_ac (σ : Val) : ∀ (pre ss : List Stmt), (∀ s ∈ pre, isAC s = true) →
    walk σ (pre ++ ss) = (walk σ ss).pre (pre.map acEv)
  | [], ss, _ => by cases h : walk σ ss <;> simp [Out.pre, h]
  | s :: pre, ss, h => by
    have ih := walk_ac σ pre ss fun s hs ↦ h s (List.mem_cons_of_mem _ hs)
    have hs := h s List.mem_cons_self
    cases s with
    | atom a =>
      rw [List.cons_append, walk_atom_cons, ih]
      cases walk σ ss <;> simp [Out.pre, acEv]
    | call f args rets =>
      rw [List.cons_append, walk_call_cons, ih]
      cases walk σ ss <;> simp [Out.pre, acEv]
    | _ => simp [isAC] at hs

theorem walk_loopC (σ : Val) (pre : List Stmt) (hpre : ∀ s ∈ pre, isAC s = true) (c : V) (f : String)
    (args : List V) :
    walk σ (pre ++ [.callIf c f args, .ret []]) =
      .ret (pre.map acEv ++ [.inK c, if σ c = 0 then .skip f args else .call f args []]) [] := by
  rw [walk_ac σ pre _ hpre, walk_callIf_cons, walk_ret_cons]
  simp [Out.pre]

theorem stmts_loopC {pre : List Stmt} (hpre : ∀ s ∈ pre, isAC s = true) {c : V} {f : String} {args : List V}
    {s : Stmt} (h : s ∈ stmtsOf (pre ++ [.callIf c f args, .ret []])) :
    s ∈ pre ∨ s = .callIf c f args ∨ s = .ret [] := by
  induction pre with
  | nil =>
    simp only [List.nil_append, stmtsOf, stmtsSub, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at h
    rcases h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  | cons a pre ih =>
    have ha := hpre a List.mem_cons_self
    have hsub : stmtsSub a = [] := by cases a <;> simp_all [isAC, stmtsSub]
    simp only [List.cons_append, stmtsOf, hsub, List.nil_append, List.mem_cons] at h
    rcases h with h | h
    · exact Or.inl (h ▸ List.mem_cons_self)
    · rcases ih (fun s hs ↦ hpre s (List.mem_cons_of_mem _ hs)) h with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h

/-- A loop helper's body with calls has no `match`. -/
theorem loopBC_noDsp {fn : Fn} (h : loopBC fn = true) {x : V} {fs : List String} {args rets : List V} :
    Stmt.dispatch x fs args rets ∉ stmtsOf fn.body := by
  obtain ⟨pre, c, args', hb, -, hpre⟩ := loopBC_spec h
  intro hm
  rw [hb] at hm
  rcases stmts_loopC hpre hm with hm | hm | hm
  · have := hpre _ hm
    simp [isAC] at this
  · cases hm
  · cases hm

theorem loopBC_noMatch {fn : Fn} (h : loopBC fn = true) {x : V} {arms : List (List Stmt)} :
    Stmt.match_ x arms ∉ stmtsOf fn.body := by
  obtain ⟨pre, c, args, hb, -, hpre⟩ := loopBC_spec h
  intro hm
  rw [hb] at hm
  rcases stmts_loopC hpre hm with hm | hm | hm
  · have := hpre _ hm
    simp [isAC] at this
  · cases hm
  · cases hm

end

end LeanVM.Guest.CoreMode
