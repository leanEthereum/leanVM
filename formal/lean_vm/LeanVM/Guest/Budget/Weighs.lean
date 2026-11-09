/-
  LeanVM.Guest.Budget.Weighs

  A tree's weight bound as a property of the tree (`WeighsLe`), and one from a bound on the valid
  trees whose arguments satisfy a precondition: a tree's arguments are its valuation's
  parameters, so every run of it has the arguments of any one.
-/

module

public import LeanVM.Guest.Budget.Kids

/-!
# A tree's weight bound

`WeighsLe ω B t`: every valid run of `t` (on any reader, its `HeapBuf`s its paths') weighs at most
`B` at `ω`. `valid_args_eq`: two valid runs of one tree have the same arguments.
`weighsLe_of_on`: a tree valid on arguments satisfying `Pre` weighs at most `B` on every run, if
every valid tree of its function on such arguments does.
-/

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- **Every valid run of `t` weighs at most `B` at `ω`.** -/
def WeighsLe (P : Core.Program) (ω : String → ℕ) (B : ℕ) (t : Tree) : Prop :=
  ∀ (rd : Reader) (args rets : List E), t.Valid P rd args rets → t.BufsOk P → t.weight ω ≤ B

variable {P : Core.Program}

/-- **A tree's arguments are its valuation's parameters**: two valid runs have the same. -/
theorem valid_args_eq {t : Tree} {rd rd' : Reader} {args args' rets rets' : List E}
    (h : t.Valid P rd args rets) (h' : t.Valid P rd' args' rets') : args = args' := by
  cases t with
  | phantom => exact h.elim
  | node f σ bufs kids =>
    obtain ⟨fn, hf, hp, -⟩ := h
    obtain ⟨fn', hf', hp', -⟩ := h'
    rw [hf, Option.some.injEq] at hf'
    subst hf'
    exact hp.symm.trans hp'

/-- **A bound on the valid trees on arguments satisfying `Pre`, for a tree valid on such.** -/
theorem weighsLe_of_on {ω : String → ℕ} {f : String} {Pre : List E → Prop} {B : ℕ}
    (h : ∀ (rd : Reader) (t : Tree) (args rets : List E), t.name = f → Pre args →
      t.Valid P rd args rets → t.BufsOk P → t.weight ω ≤ B)
    {t : Tree} {rd : Reader} {args rets : List E} (hn : t.name = f) (hv : t.Valid P rd args rets)
    (hp : Pre args) : WeighsLe P ω B t := fun rd' args' rets' hv' hb' =>
  h rd' t args' rets' hn (valid_args_eq hv hv' ▸ hp) hv' hb'

theorem WeighsLe.mono {ω : String → ℕ} {B B' : ℕ} {t : Tree} (h : WeighsLe P ω B t) (hB : B ≤ B') :
    WeighsLe P ω B' t := fun rd args rets hv hb => (h rd args rets hv hb).trans hB

end
end LeanVM.Guest.Budget
