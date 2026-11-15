/-
  LeanVM.Guest.Memory.HeapPopsL

  The advised sizes a tree pops, by node: none below functions without advice, the same under slot
  functions agreeing on the program's functions, and the same after re-choosing temporaries.
-/

module

public import LeanVM.Guest.Memory.HeapPops
public import LeanVM.Guest.Memory.SizeTotal
public import LeanVM.Guest.Memory.Retemp

/-!
# The advised sizes of a tree, by node

`heapPops_nil`: a valid tree of a function in a call-closed set `S` of functions without advised
slots pops none. `heapPops_congr`: a valid tree pops the same under two slot functions agreeing on
the program's functions. `heapPops_retemp`: re-choosing the temporaries keeps them.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable {P : Core.Program} {rd : Reader}

theorem heapPops_node (slots : String → List ℕ) (f : String) (σ : Val) (bufs : List ℕ) (kids : List Tree) :
    (Tree.node f σ bufs kids).heapPops slots = (slots f).map (advEntry bufs) ++ Tree.heapPopsKids slots kids := by
  rw [Tree.heapPops]

theorem heapPopsKids_cons (slots : String → List ℕ) (k : Tree) (ks : List Tree) :
    Tree.heapPopsKids slots (k :: ks) = k.heapPops slots ++ Tree.heapPopsKids slots ks := by
  rw [Tree.heapPopsKids]

section Nil

variable {S : String → Prop} {slots : String → List ℕ}

mutual
/-- **A valid tree below functions without advice pops no advised size.** -/
theorem heapPops_nil (hc : CallsIn P S) (hs : ∀ f, S f → slots f = []) :
    ∀ (t : Tree) {args rets : List E}, S t.name → t.Valid P rd args rets → t.heapPops slots = []
  | .node f σ bufs kids, _, _, hS, ⟨fn, hf, _, es, vs, hw, _, _, hk⟩ => by
      rw [heapPops_node, hs f hS, List.map_nil, List.nil_append]
      exact heapPopsKids_nil hc hs kids σ (calls es) (fun c h => hc f hS fn hf σ es vs hw c h) hk
  | .phantom .., _, _, _, h => h.elim

/-- `heapPops_nil` for the callees. -/
theorem heapPopsKids_nil (hc : CallsIn P S) (hs : ∀ f, S f → slots f = []) :
    ∀ (ks : List Tree) (σ : Val) (cs : List Call), (∀ c ∈ cs, S c.f) → Tree.KidsValid P rd σ cs ks →
      Tree.heapPopsKids slots ks = []
  | [], _, [], _, _ => by rw [Tree.heapPopsKids]
  | k :: ks, σ, c :: cs, hS, ⟨hn, hv, hks⟩ => by
      rw [heapPopsKids_cons, heapPopsKids_nil hc hs ks σ cs (fun c' h => hS c' (List.mem_cons_of_mem _ h)) hks,
        List.append_nil]
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hv
        exact heapPops_nil hc hs k (by rw [hn]; exact hS c List.mem_cons_self) hv
      · rw [ite_eq_right ht] at hv
        obtain ⟨⟨f, σ', rfl⟩, -⟩ := hv
        rw [Tree.heapPops]
  | [], _, _ :: _, _, h => h.elim
  | _ :: _, _, [], _, h => h.elim
end

end Nil

section Congr

variable {A B : String → List ℕ}

mutual
/-- **A valid tree pops the same under slot functions agreeing on the program's functions.** -/
theorem heapPops_congr (h : ∀ f fn, P.find? f = some fn → A f = B f) :
    ∀ (t : Tree) {args rets : List E}, t.Valid P rd args rets → t.heapPops A = t.heapPops B
  | .node f σ bufs kids, _, _, ⟨fn, hf, _, es, vs, _, _, _, hk⟩ => by
      rw [heapPops_node, heapPops_node, h f fn hf, heapPopsKids_congr h kids σ (calls es) hk]
  | .phantom .., _, _, h => h.elim

/-- `heapPops_congr` for the callees. -/
theorem heapPopsKids_congr (h : ∀ f fn, P.find? f = some fn → A f = B f) :
    ∀ (ks : List Tree) (σ : Val) (cs : List Call), Tree.KidsValid P rd σ cs ks →
      Tree.heapPopsKids A ks = Tree.heapPopsKids B ks
  | [], _, [], _ => by rw [Tree.heapPopsKids, Tree.heapPopsKids]
  | k :: ks, σ, c :: cs, ⟨_, hv, hks⟩ => by
      rw [heapPopsKids_cons, heapPopsKids_cons, heapPopsKids_congr h ks σ cs hks]
      by_cases ht : c.taken = true
      · rw [ite_eq_left ht] at hv
        rw [heapPops_congr h k hv]
      · rw [ite_eq_right ht] at hv
        obtain ⟨⟨f, σ', rfl⟩, -⟩ := hv
        rw [Tree.heapPops, Tree.heapPops]
  | [], _, _ :: _, h => h.elim
  | _ :: _, _, [], h => h.elim
end

end Congr

section Retemp

variable {fs : String → ℕ} {ν : ℕ → String → Val → V → E} (slots : String → List ℕ)

mutual
/-- **Re-choosing the temporaries keeps the advised sizes.** -/
theorem heapPops_retemp : ∀ (pos : ℕ × ℕ) (t : Tree), (t.retemp P fs ν pos).heapPops slots = t.heapPops slots
  | pos, .node f σ bufs kids => by
      rw [retemp_node, heapPops_node, heapPops_node, heapPopsKids_retemp]
  | _, .phantom f σ => by rw [Tree.retemp]

/-- `heapPops_retemp` for the callees. -/
theorem heapPopsKids_retemp : ∀ (ps : List (ℕ × ℕ)) (ks : List Tree),
    Tree.heapPopsKids slots (Tree.retempKids P fs ν ps ks) = Tree.heapPopsKids slots ks
  | _, [] => by rw [Tree.retempKids]
  | [], k :: ks => by rw [Tree.retempKids]
  | p :: ps, k :: ks => by
      rw [Tree.retempKids, heapPopsKids_cons, heapPopsKids_cons, heapPops_retemp p k, heapPopsKids_retemp ps ks]
end

end Retemp

end

end LeanVM.Guest.Memory
