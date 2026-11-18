/-
  LeanVM.Guest.CoreMode.LoopB

  A leaf loop helper's body: atoms, its tail call, `ret []`.
-/

module

public import LeanVM.Guest.Bridge.JumpCellsDefs
public import LeanVM.Guest.Bridge.Track
public import LeanVM.Guest.Bridge.Prefix

/-!
# A leaf loop helper's body

`loopB fn`: the body of atoms, the tail call `callIf c fn.name args` with one word per parameter, and
`ret []`; its path (`walk_loop`) and statements (`stmts_loop`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Bridge (stmtsOf stmtsSub walk_ret_cons walk_callIf_cons walk_atoms)

@[expose] public section

/-- An atom statement. -/
def isAtomS : Stmt → Bool
  | .atom _ => true
  | _ => false

/-- **A leaf loop helper's body**: atoms, its tail call to itself with one word per parameter,
`ret []`. -/
def loopB (fn : Fn) : Bool :=
  match fn.body.reverse with
  | .ret [] :: .callIf _ g args :: pre => (g == fn.name) && Nat.beq args.length fn.params.length && pre.all isAtomS
  | _ => false

theorem atoms_of_all : ∀ {l : List Stmt}, l.all isAtomS = true → ∃ as : List Atom, l = as.map Stmt.atom
  | [], _ => ⟨[], rfl⟩
  | s :: l, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨as, rfl⟩ := atoms_of_all h.2
    cases s with
    | atom a => exact ⟨a :: as, rfl⟩
    | _ => simp [isAtomS] at h

theorem loopB_spec {fn : Fn} (h : loopB fn = true) : ∃ (as : List Atom) (c : V) (args : List V),
    fn.body = as.map Stmt.atom ++ [.callIf c fn.name args, .ret []] ∧ args.length = fn.params.length := by
  unfold loopB at h
  split at h
  · rename_i c g args pre hrev
    simp only [Bool.and_eq_true, beq_iff_eq, Nat.beq_eq] at h
    obtain ⟨⟨rfl, hlen⟩, hpre⟩ := h
    obtain ⟨as, has⟩ := atoms_of_all (l := pre.reverse) (by simpa using hpre)
    refine ⟨as, c, args, ?_, hlen⟩
    rw [← List.reverse_reverse fn.body, hrev, ← has]
    simp
  · cases h

theorem walk_loop (σ : Val) (as : List Atom) (c : V) (f : String) (args : List V) :
    walk σ (as.map Stmt.atom ++ [.callIf c f args, .ret []]) =
      .ret (as.map Ev.atom ++ [.inK c, if σ c = 0 then .skip f args else .call f args []]) [] := by
  rw [walk_atoms, walk_callIf_cons, walk_ret_cons]
  simp [Out.pre]

theorem stmts_loop {as : List Atom} {c : V} {f : String} {args : List V} {s : Stmt}
    (h : s ∈ stmtsOf (as.map Stmt.atom ++ [.callIf c f args, .ret []])) :
    (∃ a, s = .atom a) ∨ s = .callIf c f args ∨ s = .ret [] := by
  induction as with
  | nil =>
    simp only [List.map_nil, List.nil_append, stmtsOf, stmtsSub, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at h
    rcases h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  | cons a as ih =>
    simp only [List.map_cons, List.cons_append, stmtsOf, stmtsSub, List.nil_append, List.mem_cons] at h
    rcases h with h | h
    · exact Or.inl ⟨a, h⟩
    · exact ih h

end

end LeanVM.Guest.CoreMode
