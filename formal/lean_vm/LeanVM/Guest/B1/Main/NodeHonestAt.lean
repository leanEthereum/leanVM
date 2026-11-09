/-
  LeanVM.Guest.B1.Main.NodeHonestAt

  A composition's tree has its honest shape (`Budget.NodeHonest`): the node at the walk's
  valuation, its calls and `HeapBuf`s those of the walk.
-/

module

public import LeanVM.Guest.Budget.Kids

/-!
# Honest shapes from compositions

`relAtInT_nodeHonest`: the tree `relAtInWT_of_walk` (or `relAtInWT_of_walk_loop`, with
`Ts ++ [Tt]`) builds is `NodeHonest P f Q cs bs Ts` when `Q σ`, the walk's calls are `cs σ` and its
`HeapBuf`s `bs σ`. `RelAtInT.mono`: a weaker predicate.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core
open LeanVM.Guest.Budget (NodeHonest)

@[expose] public section

variable {P : Core.Program} {fs : String → ℕ} {cert : String → V → ℕ} {rd : Reader}

theorem RelAtInT.mono {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    {T T' : Tree → Prop} (h : RelAtInT P fs cert rd R D fp n f args rets T) (hT : ∀ t, T t → T' t) :
    RelAtInT P fs cert rd R D fp n f args rets T' :=
  let ⟨t, ht, hT'⟩ := h
  ⟨t, ht, hT t hT'⟩

/-- **The tree a composition builds has its honest shape.** -/
theorem relAtInT_nodeHonest {σ : Val} {R D : ℕ → Prop} {fp n : ℕ} {f : String}
    {args rets : List E} {fn : Fn} {es : List Ev} {vs : List V} {Q : Val → Prop}
    {cs : Val → List Call} {bs : Val → List ℕ} {Ts : List (Tree → Prop)}
    (h : RelAtInT P fs cert rd R D fp n f args rets
      (fun t => ∃ ks, t = .node f σ (allocs σ es) ks ∧ KidsT (calls es) Ts ks))
    (hf : P.find? f = some fn) (hw : walk σ fn.body = .ret es vs) (hQ : Q σ)
    (hcs : calls es = cs σ) (hbs : allocs σ es = bs σ) (hlen : (cs σ).length ≤ Ts.length) :
    RelAtInT P fs cert rd R D fp n f args rets (NodeHonest P f Q cs bs Ts) := by
  refine h.mono fun t ⟨ks, he, hk⟩ => ⟨σ, ks, by rw [he, hbs], hQ, fun fn' es' vs' hf' hw' => ?_, hlen,
    hcs ▸ hk⟩
  rw [hf] at hf'
  cases hf'
  rw [hw] at hw'
  cases hw'
  exact hcs

end
end LeanVM.Guest.Memory
