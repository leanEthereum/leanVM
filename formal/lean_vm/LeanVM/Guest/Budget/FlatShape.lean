/-
  LeanVM.Guest.Budget.FlatShape

  What a function's completeness exposes of its tree, call by call, for counting: its node, its
  entered callees' trees satisfying predicates in call order, and the weight such a node has.
-/

module

public import LeanVM.Guest.Budget.Kids

/-!
# A node's callees by position

`NamedWithin fs n B t`: the tree is a call of `n` allocating at most `B` words.
`FlatShape P f Ts t`: `t` is a node of `f` whose walk's calls are at most `Ts.length`, the `i`-th
entered callee's tree satisfying `Ts[i]`. `FlatShape.weight_le`: such a node, valid, weighs at most
its frame's weight and a bound `Ws[i]` per callee, from its predicate.
-/

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- **A call of `n` within `B` words.** -/
def NamedWithin (fs : String → ℕ) (n : String) (B : ℕ) (t : Tree) : Prop :=
  t.name = n ∧ t.total fs ≤ B

/-- **A node of `f`, its entered callees satisfying `Ts` in call order.** -/
def FlatShape (P : Core.Program) (f : String) (Ts : List (Tree → Prop)) (t : Tree) : Prop :=
  ∃ σ bufs ks, t = Memory.Tree.node f σ bufs ks ∧ ∀ fn es vs, P.find? f = some fn →
    walk σ fn.body = .ret es vs → (calls es).length ≤ Ts.length ∧ KidsT (calls es) Ts ks

/-- **A node of `FlatShape` weighs at most** its frame's weight and its callees' bounds by
position. -/
theorem FlatShape.weight_le {P : Core.Program} {f : String} {Ts : List (Tree → Prop)} {t : Tree}
    {rd : Reader} {args rets : List E} (ω : String → ℕ) (Ws : List ℕ) (h : FlatShape P f Ts t)
    (hv : t.Valid P rd args rets) (hb : t.BufsOk P) (hl : Ts.length ≤ Ws.length)
    (hW : ∀ i (hT : i < Ts.length) (hW : i < Ws.length) (rd : Reader) (t : Tree) (args rets : List E),
      t.Valid P rd args rets → t.BufsOk P → Ts[i] t → t.weight ω ≤ Ws[i]) :
    t.weight ω ≤ ω f + Ws.sum := by
  obtain ⟨σ, bufs, ks, rfl, hc⟩ := h
  have hv' := hv
  obtain ⟨fn, hf, -, es, vs, hw, -, -, hk⟩ := hv'
  obtain ⟨hlen, hKT⟩ := hc fn es vs hf hw
  rw [Tree.weight]
  exact Nat.add_le_add_left (kids_weight_leL ω (calls es) Ts Ws ks hk hb.2 hKT hlen
    (hlen.trans hl) fun i _ hT hWi _ t rets _ hv'' hb' hTi => hW i hT hWi rd t _ rets hv'' hb' hTi) _

end
end LeanVM.Guest.Budget
