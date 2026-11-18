/-
  LeanVM.Guest.CoreMode.WalkS

  The events of a path and the statements they come from: an atom, a call, a `ret` on a path is a
  statement of the block, nested ones included.
-/

module

public import LeanVM.Guest.Bridge.JumpCellsDefs
public import LeanVM.Guest.Memory.Eval
public import LeanVM.Guest.Bridge.Track
public import LeanVM.Guest.CoreMode.Post

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

public section

/-- The events of an outcome. -/
@[expose] def evsC : Out → List Ev
  | .fall es => es
  | .ret es _ => es
  | .stuck => []

theorem evsC_pre {es : List Ev} {e : Ev} : ∀ {o : Out}, e ∈ evsC (o.pre es) → e ∈ es ∨ e ∈ evsC o
  | .fall _, h | .ret _ _, h => List.mem_append.mp h
  | .stuck, h => by simp [Out.pre, evsC] at h

theorem evsC_seq {k : Out} {e : Ev} : ∀ {o : Out}, e ∈ evsC (o.seq k) → e ∈ evsC o ∨ e ∈ evsC k
  | .fall _, h => (evsC_pre h)
  | .ret _ _, h => Or.inl h
  | .stuck, h => by simp [Out.seq, evsC] at h

section Walk

variable {σ : Val}

theorem pick_atomS {x : V} {args rets : List V} {a : Atom} : ∀ (fs : List String) (j : ℕ),
    Ev.atom a ∉ evsC (pick σ x args rets j fs)
  | [], _ => by simp [pick, evsC]
  | f :: fs, j => by
    unfold pick
    split_ifs
    · simp [evsC]
    · exact pick_atomS fs (j + 1)

mutual
theorem walk1_atomS {a : Atom} : ∀ (s : Stmt), Ev.atom a ∈ evsC (walk1 σ s) → Stmt.atom a ∈ s :: stmtsSub s
  | .atom b, h => by
    simp only [walk1, evsC, List.mem_singleton, Ev.atom.injEq] at h
    rw [h]
    exact List.mem_cons_self
  | .ite c z n, h => by
    rw [walk1] at h
    rcases evsC_pre h with h | h
    · simp at h
    · split_ifs at h
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (walk_atomS z h))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (walk_atomS n h))
  | .match_ x arms, h => List.mem_cons_of_mem _ (walkArms_atomS x arms 0 h)
  | .call .., h => by simp [walk1, evsC] at h
  | .callIf c _ _, h => by
    simp only [walk1, evsC, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h
    · cases h
    · revert h
      split_ifs <;> simp
  | .dispatch _ fs _ _, h => absurd h (pick_atomS fs 0)
  | .ret _, h => by simp [walk1, evsC] at h

/-- **An atom on a path** is a statement of the block, nested ones included. -/
theorem walk_atomS {a : Atom} : ∀ (ss : List Stmt), Ev.atom a ∈ evsC (walk σ ss) → Stmt.atom a ∈ stmtsOf ss
  | [], h => by simp [walk, evsC] at h
  | s :: ss, h => by
    rw [walk] at h
    simp only [stmtsOf, List.mem_cons, List.mem_append]
    rcases evsC_seq h with h | h
    · rcases List.mem_cons.mp (walk1_atomS s h) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (walk_atomS ss h))

theorem walkArms_atomS {a : Atom} (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ),
    Ev.atom a ∈ evsC (walkArms σ x j arms) → Stmt.atom a ∈ stmtsArms arms
  | [], _, h => by simp [walkArms, evsC] at h
  | b :: as, j, h => by
    unfold walkArms at h
    split_ifs at h
    · exact List.mem_append_left _ (walk_atomS b h)
    · exact List.mem_append_right _ (walkArms_atomS x as (j + 1) h)
end

mutual
theorem walk1_retS : ∀ (s : Stmt) {es : List Ev} {vs : List V}, walk1 σ s = .ret es vs →
    Stmt.ret vs ∈ s :: stmtsSub s
  | .atom _, _, _, h => by simp [walk1] at h
  | .ite c z n, _, _, h => by
    rw [walk1] at h
    split_ifs at h
    · obtain ⟨es', h', -⟩ := pre_eq_ret h
      exact List.mem_cons_of_mem _ (List.mem_append_left _ (walk_retS z h'))
    · obtain ⟨es', h', -⟩ := pre_eq_ret h
      exact List.mem_cons_of_mem _ (List.mem_append_right _ (walk_retS n h'))
  | .match_ x arms, _, _, h => List.mem_cons_of_mem _ (walkArms_retS x arms 0 h)
  | .call .., _, _, h => by simp [walk1] at h
  | .callIf .., _, _, h => by simp [walk1] at h
  | .dispatch _ fs _ _, _, _, h => absurd h (CoreMode.pick_noRetP fs 0)
  | .ret vs', _, _, h => by
    simp only [walk1, Out.ret.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact List.mem_cons_self

/-- **A path's return** is a statement of the block, nested ones included. -/
theorem walk_retS : ∀ (ss : List Stmt) {es : List Ev} {vs : List V}, walk σ ss = .ret es vs →
    Stmt.ret vs ∈ stmtsOf ss
  | [], _, _, h => by simp [walk] at h
  | s :: ss, _, _, h => by
    rw [walk] at h
    simp only [stmtsOf, List.mem_cons, List.mem_append]
    rcases seq_eq_ret h with ⟨es1, es2, -, h2, -⟩ | h1
    · exact Or.inr (Or.inr (walk_retS ss h2))
    · rcases List.mem_cons.mp (walk1_retS s h1) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)

theorem walkArms_retS (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ) {es : List Ev} {vs : List V},
    walkArms σ x j arms = .ret es vs → Stmt.ret vs ∈ stmtsArms arms
  | [], _, _, _, h => by simp [walkArms] at h
  | b :: as, j, _, _, h => by
    unfold walkArms at h
    split_ifs at h
    · exact List.mem_append_left _ (walk_retS b h)
    · exact List.mem_append_right _ (walkArms_retS x as (j + 1) h)
end

theorem pick_callS {x : V} {args rets : List V} {f : String} {a r : List V} : ∀ (fs : List String) (j : ℕ),
    Ev.call f a r ∈ evsC (pick σ x args rets j fs) → f ∈ fs ∧ args = a ∧ rets = r
  | [], _, h => by simp [pick, evsC] at h
  | g :: fs, j, h => by
    unfold pick at h
    split_ifs at h
    · simp only [evsC, List.mem_cons, Ev.call.injEq, List.not_mem_nil, or_false] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨List.mem_cons_self, rfl, rfl⟩
    · obtain ⟨h1, h2, h3⟩ := pick_callS fs (j + 1) h
      exact ⟨List.mem_cons_of_mem _ h1, h2, h3⟩

/-- What made a call event: a `call`, a `callIf` or a `dispatch` naming its callee. -/
@[expose] def CallS (f : String) (a r : List V) : Stmt → Prop
  | .call g a' r' => g = f ∧ a' = a ∧ r' = r
  | .callIf _ g a' => g = f ∧ a' = a ∧ r = []
  | .dispatch _ fs a' r' => f ∈ fs ∧ a' = a ∧ r' = r
  | _ => False

mutual
theorem walk1_callS {f : String} {a r : List V} : ∀ (s : Stmt), Ev.call f a r ∈ evsC (walk1 σ s) →
    ∃ t ∈ s :: stmtsSub s, CallS f a r t
  | .atom b, h => by simp [walk1, evsC] at h
  | .ite c z n, h => by
    rw [walk1] at h
    rcases evsC_pre h with h | h
    · simp at h
    · split_ifs at h
      · obtain ⟨t, ht, hc⟩ := walk_callS z h
        exact ⟨t, List.mem_cons_of_mem _ (List.mem_append_left _ ht), hc⟩
      · obtain ⟨t, ht, hc⟩ := walk_callS n h
        exact ⟨t, List.mem_cons_of_mem _ (List.mem_append_right _ ht), hc⟩
  | .match_ x arms, h => by
    obtain ⟨t, ht, hc⟩ := walkArms_callS x arms 0 h
    exact ⟨t, List.mem_cons_of_mem _ ht, hc⟩
  | .call g a' r', h => by
    simp only [walk1, evsC, List.mem_singleton, Ev.call.injEq] at h
    exact ⟨_, List.mem_cons_self, h.1.symm, h.2.1.symm, h.2.2.symm⟩
  | .callIf c g args, h => by
    simp only [walk1, evsC] at h
    by_cases hc : σ c = 0
    · simp [hc] at h
    · simp only [hc, ↓reduceIte, List.mem_cons, Ev.call.injEq, List.not_mem_nil, or_false, reduceCtorEq,
        false_or] at h
      exact ⟨_, List.mem_cons_self, h.1.symm, h.2.1.symm, h.2.2⟩
  | .dispatch x fs args rets, h => ⟨_, List.mem_cons_self, pick_callS fs 0 h⟩
  | .ret _, h => by simp [walk1, evsC] at h

/-- **A call on a path** comes from a statement of the block, nested ones included. -/
theorem walk_callS {f : String} {a r : List V} : ∀ (ss : List Stmt), Ev.call f a r ∈ evsC (walk σ ss) →
    ∃ t ∈ stmtsOf ss, CallS f a r t
  | [], h => by simp [walk, evsC] at h
  | s :: ss, h => by
    rw [walk] at h
    rcases evsC_seq h with h | h
    · obtain ⟨t, ht, hc⟩ := walk1_callS s h
      refine ⟨t, ?_, hc⟩
      simp only [stmtsOf, List.mem_cons, List.mem_append] at ht ⊢
      rcases ht with rfl | ht
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ht)
    · obtain ⟨t, ht, hc⟩ := walk_callS ss h
      exact ⟨t, by simp only [stmtsOf, List.mem_cons, List.mem_append]; exact Or.inr (Or.inr ht), hc⟩

theorem walkArms_callS {f : String} {a r : List V} (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ),
    Ev.call f a r ∈ evsC (walkArms σ x j arms) → ∃ t ∈ stmtsArms arms, CallS f a r t
  | [], _, h => by simp [walkArms, evsC] at h
  | b :: as, j, h => by
    unfold walkArms at h
    split_ifs at h
    · obtain ⟨t, ht, hc⟩ := walk_callS b h
      exact ⟨t, List.mem_append_left _ ht, hc⟩
    · obtain ⟨t, ht, hc⟩ := walkArms_callS x as (j + 1) h
      exact ⟨t, List.mem_append_right _ ht, hc⟩
end

end Walk

end

end LeanVM.Guest.Bridge
