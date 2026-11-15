/-
  LeanVM.Guest.Backend.Complete.FrameInduct

  The block lemma for every block of a body, by induction on the size of the block.
-/

module

public import LeanVM.Guest.Backend.Complete.FrameStmts

/-!
# Every block of a body

`blockW_good` gives `BlockW` for every block a predicate `Good` holds of (the blocks of a body
and their suffixes), from the constructs' lemmas: straight-line and call statements by `StmtW`
composed with `BlockW.cons`, a self `callIf` with the `return` it must be followed by, a branch and
a `match` (with the chain it starts) as `BlockW` of the whole block from it, given `BlockW` of
every smaller good block.
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

section Induct

variable {κ₀ : ℕ} (Γ : Site κ₀)
  (Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop) (cl : List Call)
  (ctx : Ctx) (I : Inst) (Good : List Stmt → Prop)

/-- The block lemma for every smaller good block. -/
def BlockIH (ss : List Stmt) : Prop :=
  ∀ ss', Good ss' → sizeOf ss' < sizeOf ss → ∀ tl, BlockW Γ Ag cl ctx I (placeBlock ss') ss' tl

/-- **A branch on the path**, given the block lemma for the smaller good blocks. -/
def IteW : Prop :=
  ∀ c z nz rest tl, Good (.ite c z nz :: rest) → BlockIH Γ Ag cl ctx I Good (.ite c z nz :: rest) →
    BlockW Γ Ag cl ctx I (placeBlock (.ite c z nz :: rest)) (.ite c z nz :: rest) tl

/-- **A `match` on the path** (with the chain it starts), given the block lemma for the smaller
good blocks. -/
def MatchW : Prop :=
  ∀ x arms rest tl, Good (.match_ x arms :: rest) →
    BlockIH Γ Ag cl ctx I Good (.match_ x arms :: rest) →
    BlockW Γ Ag cl ctx I (placeBlock (.match_ x arms :: rest)) (.match_ x arms :: rest) tl

/-- **A self `callIf`** (a tail call or a loop's next frame), with the statements after it. -/
def SelfW : Prop :=
  ∀ c f args rest tl, f = ctx.name → Good (.callIf c f args :: rest) →
    BlockW Γ Ag cl ctx I (placeBlock (.callIf c f args :: rest)) (.callIf c f args :: rest) tl

/-- **A straight-line or call statement** of a good block. -/
def FlatW : Prop :=
  ∀ s rest tl, Good (s :: rest) → (∀ c z nz, s ≠ .ite c z nz) → (∀ x arms, s ≠ .match_ x arms) →
    (∀ c f args, s = .callIf c f args → f ≠ ctx.name) → StmtW Γ Ag cl ctx I s rest tl

end Induct

variable {κ₀ : ℕ} {Γ : Site κ₀}
  {Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop} {cl : List Call}
  {ctx : Ctx} {I : Inst} {Good : List Stmt → Prop}

/-- **The block lemma for every good block.** -/
theorem blockW_good (hmono : PlaceMono ctx) (hnew : PlaceNew ctx)
    (hrest : ∀ s rest, Good (s :: rest) → Good rest)
    (hfa : ∀ s rest, Good (s :: rest) → FaAfter I.σ s rest)
    (hflat : FlatW Γ Ag cl ctx I Good) (hself : SelfW Γ Ag cl ctx I Good)
    (hite : IteW Γ Ag cl ctx I Good) (hmatch : MatchW Γ Ag cl ctx I Good) :
    ∀ ss, Good ss → ∀ tl, BlockW Γ Ag cl ctx I (placeBlock ss) ss tl
  | [], _, tl => BlockW.nil tl
  | s :: rest, hg, tl => by
    have ih : BlockIH Γ Ag cl ctx I Good (s :: rest) := fun ss' hg' _ tl' =>
      blockW_good hmono hnew hrest hfa hflat hself hite hmatch ss' hg' tl'
    have hcons : (∀ c z nz, s ≠ .ite c z nz) → (∀ x arms, s ≠ .match_ x arms) →
        (∀ c f args, s = .callIf c f args → f ≠ ctx.name) →
        BlockW Γ Ag cl ctx I (placeBlock (s :: rest)) (s :: rest) tl := fun h1 h2 h3 =>
      BlockW.cons hmono hnew (hfa s rest hg) (hflat s rest tl hg h1 h2 h3)
        (ih rest (hrest s rest hg) (by simp) tl)
    cases s with
    | ite c z nz => exact hite c z nz rest tl hg ih
    | match_ x arms => exact hmatch x arms rest tl hg ih
    | callIf c f args =>
      by_cases hf : f = ctx.name
      · exact hself c f args rest tl hf hg
      · exact hcons (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h)
          (fun _ _ _ h => by cases h; exact hf)
    | atom a =>
      exact hcons (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h)
    | call f args rets =>
      exact hcons (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h)
    | dispatch x fs args rets =>
      exact hcons (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h)
    | ret vs =>
      exact hcons (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h)
termination_by ss => sizeOf ss
decreasing_by all_goals (simp_wf; assumption)

end
end LeanVM.Guest.Backend.Complete
