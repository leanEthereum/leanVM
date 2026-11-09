/-
  LeanVM.Guest.B1.Main.RelAtW

  `RelAtIn` with the root's valuation exposed: the tree a composition builds is the function's
  node at the valuation its walk ran on.
-/

module

public import LeanVM.Guest.Memory.Regions

/-!
# The placed relation, its root's valuation exposed

`RelAtInW … Q`: `RelAtIn` by a tree `.node f σ bufs kids` with `Q σ`. `relAtInW_of_walk` is
`relAtIn_of_walk` (`Memory/Regions.lean`, same proof) with the root's valuation the walk's;
`RelAtInW.relAtIn` forgets it.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

variable (P : Core.Program) (fs : String → ℕ) (cert : String → V → ℕ)

/-- **`RelAtIn` by a tree rooted at a valuation satisfying `Q`.** -/
def RelAtInW (rd : Reader) (R D : ℕ → Prop) (fp n : ℕ) (f : String) (args rets : List E)
    (Q : Val → Prop) : Prop :=
  ∃ t : Tree, (t.name = f ∧ t.Valid P rd args rets ∧ t.BufsOk P ∧ t.Placed P fs cert fp ∧
    t.total fs = n ∧ t.LoadsIn P fs cert R fp ∧ ∀ i, D i → t.Data P fs cert fp i) ∧
    ∃ σ bufs kids, t = .node f σ bufs kids ∧ Q σ

variable {P fs cert}

theorem RelAtInW.relAtIn {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    {Q : Val → Prop} (h : RelAtInW P fs cert rd R D fp n f args rets Q) :
    RelAtIn P fs cert rd R D fp n f args rets :=
  let ⟨t, ht, _⟩ := h
  ⟨t, ht⟩

theorem RelAtInW.mono {rd : Reader} {R D : ℕ → Prop} {fp n : ℕ} {f : String} {args rets : List E}
    {Q Q' : Val → Prop} (h : RelAtInW P fs cert rd R D fp n f args rets Q) (hq : ∀ σ, Q σ → Q' σ) :
    RelAtInW P fs cert rd R D fp n f args rets Q' :=
  let ⟨t, ht, σ, b, k, he, hQ⟩ := h
  ⟨t, ht, σ, b, k, he, hq σ hQ⟩

variable {rd : Reader} {σ : Val}

end
end LeanVM.Guest.Memory
