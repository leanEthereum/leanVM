/-
  LeanVM.Guest.CoreMode.LoopBC

  A loop helper's body with calls: atoms and calls, its tail call, `ret []`.
-/

module

public import LeanVM.Guest.CoreMode.LoopB
public import LeanVM.Guest.CoreMode.WalkS

/-!
# A loop helper's body with calls

`loopBC fn`: the body of atoms and calls, the tail call `callIf c fn.name args` with one word per
parameter, and `ret []`; its statements (`stmts_loopC`). `loopBB fn`: the same with branches and `match`es
before the tail, its path (`walk_loopB`) and statements (`stmts_loopB`).
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

/-! ## A loop helper's body with branches -/

/-- A statement of a loop helper's body before its tail call, nested ones included: an atom, a call, a
branch, a `match`, or a conditional call of a function other than `nm` (the loop's own name). -/
def isBS (nm : String) : Stmt → Bool
  | .atom _ | .call .. | .ite .. | .match_ .. => true
  | .callIf _ g _ => !(g == nm)
  | _ => false

/-- **A loop helper's body with branches**: its statements before the tail call `callIf c fn.name args`
(one word per parameter) atoms, calls, branches, `match`es and conditional calls of other functions, nested ones
included; then `ret []`. -/
def loopBB (fn : Fn) : Bool :=
  match fn.body.reverse with
  | .ret [] :: .callIf _ g args :: pre => (g == fn.name) && Nat.beq args.length fn.params.length &&
      (stmtsOf pre.reverse).all (isBS fn.name)
  | _ => false

theorem stmtsOf_append : ∀ (a b : List Stmt), stmtsOf (a ++ b) = stmtsOf a ++ stmtsOf b
  | [], _ => rfl
  | s :: a, b => by simp [stmtsOf, stmtsOf_append a b]

theorem loopBB_spec {fn : Fn} (h : loopBB fn = true) : ∃ (pre : List Stmt) (c : V) (args : List V),
    fn.body = pre ++ [.callIf c fn.name args, .ret []] ∧ args.length = fn.params.length ∧
      ∀ s ∈ stmtsOf pre, isBS fn.name s = true := by
  unfold loopBB at h
  split at h
  · rename_i c g args pre hrev
    simp only [Bool.and_eq_true, beq_iff_eq, Nat.beq_eq, List.all_eq_true] at h
    obtain ⟨⟨rfl, hlen⟩, hpre⟩ := h
    refine ⟨pre.reverse, c, args, ?_, hlen, hpre⟩
    rw [← List.reverse_reverse fn.body, hrev]
    simp
  · cases h

/-- **The statements of a loop helper's body with branches**: its statements before the tail call, the
tail call, the return. -/
theorem stmts_loopB {pre : List Stmt} {c : V} {f : String} {args : List V} {s : Stmt}
    (h : s ∈ stmtsOf (pre ++ [.callIf c f args, .ret []])) :
    s ∈ stmtsOf pre ∨ s = .callIf c f args ∨ s = .ret [] := by
  rw [stmtsOf_append] at h
  rcases List.mem_append.mp h with h | h
  · exact Or.inl h
  · simp only [stmtsOf, stmtsSub, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at h
    exact Or.inr h

/-- **The path of a loop helper's body with branches**: the path of its statements before the tail
call falls through, then the tail call, then `ret []`. -/
theorem walk_loopB (σ : Val) {nm : String} {pre : List Stmt} (hpre : ∀ s ∈ stmtsOf pre, isBS nm s = true) {c : V}
    {f : String}
    {args : List V} {es : List Ev} {vs : List V} (h : walk σ (pre ++ [.callIf c f args, .ret []]) = .ret es vs) :
    ∃ E, walk σ pre = .fall E ∧ es = E ++ [.inK c, if σ c = 0 then .skip f args else .call f args []] ∧ vs = [] := by
  rw [Bridge.walk_append, walk_callIf_cons, walk_ret_cons] at h
  rcases hw : walk σ pre with E | ⟨E, ws⟩ | _
  · rw [hw] at h
    simp only [Out.seq, Out.pre, List.append_nil, Out.ret.injEq] at h
    exact ⟨E, rfl, by rw [← h.1], h.2.symm⟩
  · have := Bridge.walk_retS pre hw
    simpa [isBS] using hpre _ this
  · rw [hw] at h
    cases h

/-- **The tail call is the body's one conditional call of the function itself.** -/
theorem loopB_callIf {pre : List Stmt} {f : String} (hpre : ∀ s ∈ stmtsOf pre, isBS f s = true) {c c' : V}
    {args args' : List V} (h : Stmt.callIf c' f args' ∈ stmtsOf (pre ++ [.callIf c f args, .ret []])) :
    c' = c ∧ args' = args := by
  rcases stmts_loopB h with h | h | h
  · simpa [isBS] using hpre _ h
  · simp only [Stmt.callIf.injEq, true_and] at h
    exact h
  · cases h

/-- **A call event of a loop helper's body with branches**: a `call` statement's, a conditional call's of another
function, or the tail call's. -/
theorem loopB_callEv {fn : Fn} (h : loopBB fn = true) {σ : Val} {es : List Ev} {vs : List V}
    (hw : walk σ fn.body = .ret es vs) {f : String} {a r : List V} (he : Ev.call f a r ∈ es) :
    Stmt.call f a r ∈ stmtsOf fn.body ∨ (r = [] ∧ (∃ c, Stmt.callIf c f a ∈ stmtsOf fn.body) ∧ f ≠ fn.name) ∨
      (f = fn.name ∧ r = []) := by
  obtain ⟨pre, c, args, hb, -, hpre⟩ := loopBB_spec h
  obtain ⟨t, ht, hc⟩ := Bridge.walk_callS fn.body (by rw [hw]; exact he)
  cases t with
  | call g a' r' =>
    simp only [Bridge.CallS] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact Or.inl ht
  | callIf c' g a' =>
    simp only [Bridge.CallS] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    by_cases hg : g = fn.name
    · exact Or.inr (Or.inr ⟨hg, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, ⟨c', ht⟩, hg⟩)
  | dispatch x fs a' r' =>
    rw [hb] at ht
    rcases stmts_loopB ht with h | h | h
    · simpa [isBS] using hpre _ h
    · cases h
    · cases h
  | _ => simp [Bridge.CallS] at hc

/-- A loop helper's body with branches has no dispatch. -/
theorem loopBB_noDsp {fn : Fn} (h : loopBB fn = true) {x : V} {fs : List String} {args rets : List V} :
    Stmt.dispatch x fs args rets ∉ stmtsOf fn.body := by
  obtain ⟨pre, c, args', hb, -, hpre⟩ := loopBB_spec h
  intro hm
  rw [hb] at hm
  rcases stmts_loopB hm with hm | hm | hm
  · simpa [isBS] using hpre _ hm
  · cases hm
  · cases hm

end

end LeanVM.Guest.CoreMode
