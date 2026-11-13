/-
  LeanVM.Guest.Memory.PopsNil

  A call tree of a function with no witness hint in its subtree pops nothing (`pops_nil_of_noWitIn`).
-/

module

public import LeanVM.Guest.Pops
public import LeanVM.Guest.Memory.SizeTotal

/-!
# Subtrees without witness hints

`Stmt.noWitList ss`: no atom of `ss` is a witness hint. `Program.NoWitIn P S`: every function of `S` passes it and calls only functions of `S`. Then every valid tree of a function of `S` pops `[]` (`pops_nil_of_noWitIn`): its path's atoms pop nothing (`walk_noWit`), its callees pop nothing by induction, a phantom nothing by definition.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- An atom that is no witness hint. -/
def atomNoWit : Atom → Bool
  | .hint (.witness ..) => false
  | _ => true

mutual
/-- A statement with no witness hint. -/
def Stmt.noWit : Stmt → Bool
  | .atom a => atomNoWit a
  | .ite _ z n => Stmt.noWitList z && Stmt.noWitList n
  | .match_ _ arms => Stmt.noWitArms arms
  | _ => true

/-- `Stmt.noWit` of a block. -/
def Stmt.noWitList : List Stmt → Bool
  | [] => true
  | s :: ss => Stmt.noWit s && Stmt.noWitList ss

/-- `Stmt.noWit` of arms. -/
def Stmt.noWitArms : List (List Stmt) → Bool
  | [] => true
  | a :: as => Stmt.noWitList a && Stmt.noWitArms as
end

/-- **A call-closed set of functions with no witness hint.** -/
def _root_.LeanVM.Guest.Core.Program.NoWitIn (P : Core.Program) (S : String → Prop) : Prop :=
  ∀ f, S f → ∀ fn, P.find? f = some fn → Stmt.noWitList fn.body = true ∧ ∀ g ∈ Stmt.blockCallees fn.body, S g

/-- An event with no witness hint. -/
def Ev.noWit : Ev → Prop
  | .atom a => atomNoWit a = true
  | _ => True

section Walk

variable {σ : Val}

theorem pick_noWit {x : V} {args rets : List V} :
    ∀ (gs : List String) (j : ℕ), (pick σ x args rets j gs).All Ev.noWit
  | [], _ => trivial
  | g :: gs, j => by
      unfold pick
      split_ifs
      · intro e he
        rw [List.mem_singleton] at he
        subst he
        trivial
      · exact pick_noWit gs (j + 1)

mutual
theorem walk1_noWit : ∀ (s : Stmt), Stmt.noWit s = true → (walk1 σ s).All Ev.noWit
  | .atom _, h => by
      intro e he
      rw [List.mem_singleton] at he
      subst he
      exact h
  | .ite c z n, h => by
      simp only [Stmt.noWit, Bool.and_eq_true] at h
      rw [walk1]
      refine Out.all_pre (fun e he => by rw [List.mem_singleton] at he; subst he; trivial) ?_
      split_ifs
      · exact walk_noWit z h.1
      · exact walk_noWit n h.2
  | .match_ x arms, h => walkArms_noWit x arms 0 h
  | .call .., _ => by
      intro e he
      rw [List.mem_singleton] at he
      subst he
      trivial
  | .callIf c f args, _ => by
      rw [walk1]
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · trivial
      · split_ifs <;> trivial
  | .dispatch x fs args rets, _ => pick_noWit fs 0
  | .ret _, _ => fun _ he => (List.not_mem_nil he).elim

theorem walk_noWit : ∀ (ss : List Stmt), Stmt.noWitList ss = true → (walk σ ss).All Ev.noWit
  | [], _ => fun _ he => (List.not_mem_nil he).elim
  | s :: ss, h => by
      simp only [Stmt.noWitList, Bool.and_eq_true] at h
      rw [walk]
      exact Out.all_seq (walk_noWit ss h.2) (walk1_noWit s h.1)

theorem walkArms_noWit (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ), Stmt.noWitArms arms = true →
    (walkArms σ x j arms).All Ev.noWit
  | [], _, _ => trivial
  | a :: as, j, h => by
      simp only [Stmt.noWitArms, Bool.and_eq_true] at h
      unfold walkArms
      split_ifs
      · exact walk_noWit a h.1
      · exact walkArms_noWit x as (j + 1) h.2
end

end Walk

section Tree

variable {P : Core.Program} {rd rd' : Reader} {S : String → Prop}

/-- **Events with no witness hint, their callees popping nothing, pop nothing.** -/
theorem splice_nil_of {σ : Val} : ∀ (es : List Ev) (ks : List (List Pop)), (∀ e ∈ es, e.noWit) →
    (∀ k ∈ ks, k = []) → splice rd σ es ks = []
  | [], _, _, _ => rfl
  | .atom a :: es, ks, he, hk => by
      have ha : a.pops rd σ = [] := by
        have := he _ List.mem_cons_self
        cases a with
        | hint x => cases x <;> simp_all [Ev.noWit, atomNoWit, Atom.pops, Hint.pops]
        | _ => rfl
      rw [splice, ha, splice_nil_of es ks (fun e h => he e (List.mem_cons_of_mem _ h)) hk]; rfl
  | .inK _ :: es, ks, he, hk => by
      rw [splice]; exact splice_nil_of es ks (fun e h => he e (List.mem_cons_of_mem _ h)) hk
  | .call .. :: es, ks, he, hk | .skip .. :: es, ks, he, hk => by
      rw [splice, splice_nil_of es ks.tail (fun e h => he e (List.mem_cons_of_mem _ h))
        (fun k h => hk k (List.mem_of_mem_tail h))]
      cases ks with
      | nil => rfl
      | cons k ks => rw [List.headD_cons, hk k List.mem_cons_self]; rfl

theorem pops_phantom (f : String) (σ : Val) : (Tree.phantom f σ).pops P rd' = [] := by rw [Tree.pops]

mutual
/-- **A valid tree of a function of a call-closed set with no witness hint pops nothing**, on any memory. -/
theorem pops_nil_of_noWitIn (hS : P.NoWitIn S) : ∀ (t : Tree) {args rets : List E},
    t.Valid P rd args rets → S t.name → t.pops P rd' = []
  | .node f σ bufs kids, _, _, ⟨fn, hf, _, es, vs, hw, _, _, hk⟩, hn => by
      obtain ⟨hb, hc⟩ := hS f hn fn hf
      rw [Tree.pops_node hf hw]
      refine splice_nil_of es _ ?_ (popsKids_nil_of_noWitIn hS kids σ (calls es) hk fun c hc' => ?_)
      · have := walk_noWit (σ := σ) fn.body hb
        rwa [hw] at this
      · exact hc c.f (walk_callees (σ := σ) fn.body (by rw [hw]; exact hc'))
  | .phantom .., _, _, h, _ => h.elim

/-- `pops_nil_of_noWitIn` for the callees. -/
theorem popsKids_nil_of_noWitIn (hS : P.NoWitIn S) : ∀ (ks : List Tree) (σ : Val) (cs : List Call),
    Tree.KidsValid P rd σ cs ks → (∀ c ∈ cs, S c.f) → ∀ p ∈ Tree.popsKids P rd' ks, p = []
  | [], _, _, _, _ => by rw [Tree.popsKids]; exact fun _ h => (List.not_mem_nil h).elim
  | k :: ks, σ, c :: cs, ⟨hn, hc, hks⟩, hS' => by
      rw [Tree.popsKids]
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · by_cases ht : c.taken = true
        · rw [ite_eq_left ht] at hc
          exact pops_nil_of_noWitIn hS k hc (hn ▸ hS' c List.mem_cons_self)
        · rw [ite_eq_right ht] at hc
          obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
          exact pops_phantom f σ'
      · exact popsKids_nil_of_noWitIn hS ks σ cs hks (fun c' h => hS' c' (List.mem_cons_of_mem _ h)) p hp
  | _ :: _, _, [], h, _ => h.elim
end

end Tree

end
end LeanVM.Guest.Memory
