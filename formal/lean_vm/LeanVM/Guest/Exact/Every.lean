/-
  LeanVM.Guest.Exact.Every

  A predicate of every node of a call tree (`Tree.Every`), exactness as one (`ExactAt`), and the
  call-closed sets of functions on whose valid trees one holds for free (`Program.EveryIn`, `every_of_everyIn`).
-/

module

public import LeanVM.Guest.Exact.Defs
public import LeanVM.Guest.Memory.SizeTotal

/-!
# Every node

`Tree.Every Q t`: every node `node f σ _ _` of `t` satisfies `Q f σ`, phantoms nothing. It carries what the
executor needs of the honest tree's valuations, node by node: exactness (`ExactAt`) and the
residual facts of the mode walk, as one conjunction (`Tree.Every.and`).

`Program.EveryIn P rd Q S`: every function of `S` calls only functions of `S`, and each of its paths holding on `rd`
satisfies `Q`. Then every valid tree of a function of `S` satisfies `Every Q` (`every_of_everyIn`), with no
hypothesis on the instance.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

mutual
/-- **Every node of the tree satisfies `Q`**, at its function and valuation; a phantom nothing. -/
def Tree.Every (Q : String → Val → Prop) : Tree → Prop
  | .node f σ _ kids => Q f σ ∧ Tree.EveryKids Q kids
  | .phantom .. => True

/-- `Tree.Every` of each callee. -/
def Tree.EveryKids (Q : String → Val → Prop) : List Tree → Prop
  | [] => True
  | k :: ks => k.Every Q ∧ Tree.EveryKids Q ks
end

/-- A node's events are exact: the node predicate of `Tree.Exact`. -/
def ExactAt (P : Core.Program) (rd : Reader) (f : String) (σ : Val) : Prop :=
  ∀ e ∈ (Tree.node f σ [] []).events P, e.Exact rd σ

variable {Q Q' : String → Val → Prop}

theorem Tree.every_node {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} :
    (Tree.node f σ bufs kids).Every Q ↔ Q f σ ∧ Tree.EveryKids Q kids := by
  rw [Tree.Every]

theorem Tree.every_phantom {f : String} {σ : Val} : (Tree.phantom f σ).Every Q := by
  rw [Tree.Every]; trivial

mutual
theorem Tree.Every.mono (hQ : ∀ f σ, Q f σ → Q' f σ) : ∀ {t : Tree}, t.Every Q → t.Every Q'
  | .node .., h => by
      rw [Tree.every_node] at h ⊢
      exact ⟨hQ _ _ h.1, Tree.EveryKids.mono hQ h.2⟩
  | .phantom .., _ => Tree.every_phantom

theorem Tree.EveryKids.mono (hQ : ∀ f σ, Q f σ → Q' f σ) : ∀ {ks : List Tree}, Tree.EveryKids Q ks →
    Tree.EveryKids Q' ks
  | [], _ => by rw [Tree.EveryKids]; trivial
  | _ :: _, h => by
      rw [Tree.EveryKids] at h ⊢
      exact ⟨Tree.Every.mono hQ h.1, Tree.EveryKids.mono hQ h.2⟩
end

mutual
theorem Tree.Every.and : ∀ {t : Tree}, t.Every Q → t.Every Q' → t.Every fun f σ => Q f σ ∧ Q' f σ
  | .node .., h, h' => by
      rw [Tree.every_node] at h h' ⊢
      exact ⟨⟨h.1, h'.1⟩, Tree.EveryKids.and h.2 h'.2⟩
  | .phantom .., _, _ => Tree.every_phantom

theorem Tree.EveryKids.and : ∀ {ks : List Tree}, Tree.EveryKids Q ks → Tree.EveryKids Q' ks →
    Tree.EveryKids (fun f σ => Q f σ ∧ Q' f σ) ks
  | [], _, _ => by rw [Tree.EveryKids]; trivial
  | _ :: _, h, h' => by
      rw [Tree.EveryKids] at h h' ⊢
      exact ⟨Tree.Every.and h.1 h'.1, Tree.EveryKids.and h.2 h'.2⟩
end

mutual
/-- Every tree satisfies the trivial predicate. -/
theorem Tree.every_true : ∀ (t : Tree), t.Every fun _ _ => True
  | .node .. => Tree.every_node.mpr ⟨trivial, Tree.everyKids_true _⟩
  | .phantom .. => Tree.every_phantom

theorem Tree.everyKids_true : ∀ (ks : List Tree), Tree.EveryKids (fun _ _ => True) ks
  | [] => by rw [Tree.EveryKids]; trivial
  | k :: ks => by rw [Tree.EveryKids]; exact ⟨Tree.every_true k, Tree.everyKids_true ks⟩
end

/-! ## Free on a call-closed set -/

/-- **A call-closed set on whose paths `Q` holds**: each function of `S` calls only functions of `S`, and every path
of it holding on `rd` satisfies `Q`. -/
def _root_.LeanVM.Guest.Core.Program.EveryIn (P : Core.Program) (rd : Reader) (Q : String → Val → Prop)
    (S : String → Prop) : Prop :=
  ∀ f, S f → ∀ fn, P.find? f = some fn → (∀ g ∈ Stmt.blockCallees fn.body, S g) ∧
    ∀ σ es vs, walk σ fn.body = .ret es vs → (∀ e ∈ es, e.Holds rd σ) → Q f σ

variable {P : Core.Program} {rd : Reader} {S : String → Prop}

mutual
/-- **A valid tree of a function of a call-closed set on whose paths `Q` holds** satisfies `Every Q`. -/
theorem every_of_everyIn (hS : P.EveryIn rd Q S) : ∀ (t : Tree) {args rets : List E},
    t.Valid P rd args rets → S t.name → t.Every Q
  | .node f σ _ kids, _, _, ⟨fn, hf, _, es, vs, hw, _, hes, hk⟩, hn => by
      obtain ⟨hc, hq⟩ := hS f hn fn hf
      rw [Tree.every_node]
      exact ⟨hq σ es vs hw hes, everyKids_of_everyIn hS kids σ (calls es) hk fun c hc' =>
        hc c.f (walk_callees (σ := σ) fn.body (by rw [hw]; exact hc'))⟩
  | .phantom .., _, _, h, _ => h.elim

/-- `every_of_everyIn` for the callees. -/
theorem everyKids_of_everyIn (hS : P.EveryIn rd Q S) : ∀ (ks : List Tree) (σ : Val) (cs : List Call),
    Tree.KidsValid P rd σ cs ks → (∀ c ∈ cs, S c.f) → Tree.EveryKids Q ks
  | [], _, _, _, _ => by rw [Tree.EveryKids]; trivial
  | k :: ks, σ, c :: cs, ⟨hn, hc, hks⟩, hS' => by
      rw [Tree.EveryKids]
      refine ⟨?_, everyKids_of_everyIn hS ks σ cs hks fun c' h => hS' c' (List.mem_cons_of_mem _ h)⟩
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hc
        exact every_of_everyIn hS k hc (hn ▸ hS' c List.mem_cons_self)
      · rw [ite_eq_right ht] at hc
        obtain ⟨⟨f, σ', rfl⟩, -⟩ := hc
        exact Tree.every_phantom
  | _ :: _, _, [], h, _ => h.elim
end

end
end LeanVM.Guest.Memory
