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

/-! ## A branch: its inner blocks and the statement -/

section Ite

variable (Γ Ag cl ctx I)

/-- **An inner block on the path**: `inBlock (placeBlock z)` from a state in lockstep with the scope
walk, against `scopeInner`, gives the outer block's statements and pools back, no `match` chaining
out, and once the final placement extends the state reached and has the inner block's
instructions at the absolute position `p₁` (and the tables), the invariant after it if its path
falls through, its words (`BlkW` at `p₁`, the core block followed by nothing) and the words of
the values its path reads. -/
def InBlockW (z : List Stmt) : Prop :=
  ∀ (C : (ℕ → E) → Prop) (st : St) (sc sc' : SSt) (i₀ p₁ : ℕ) (o : Out),
    scopeInner ctx.retCells (fun s' => scopeBlock ctx.retCells z s') sc = .ok sc' →
    walk I.σ z = o → o ≠ .stuck → (∀ e ∈ outEs o, e ∈ I.es) →
    (∀ j < (calls (outEs o)).length, cl[i₀ + j]? = (calls (outEs o))[j]?) →
    WInv ctx I C st sc →
    FBAt ctx I C st (inBlock (placeBlock z)) fun blk C' st' =>
      st'.out = st.out ∧ st'.scope = st.scope ∧ st'.chainIn = none ∧
      (∀ es, o = .fall es → Fits I st' → OpsIn I p₁ (blockOps blk p₁) → TabsW Γ Ag st' →
        WInv ctx I C' st' sc') ∧
      (Fits I st' → OpsIn I p₁ (blockOps blk p₁) → TabsW Γ Ag st' →
        BlkW Γ I ctx Ag cl C' blk z [] o i₀ p₁ ∧ RW I C' st' (pathVals I.σ z o))

/-- **An inner block from its block lemma** (open: the block's flush, `leave` and anchor). -/
def InBlockOf : Prop :=
  ∀ z, (∀ tl, BlockW Γ Ag cl ctx I (placeBlock z) z tl) → InBlockW Γ Ag cl ctx I z

/-- **A branch statement** from its inner blocks (open: the condition's cell, the destinations,
the untaken block off the path, the words of the `ite`). -/
def IteStmt : Prop :=
  ∀ c z nz rest tl, InBlockW Γ Ag cl ctx I z → InBlockW Γ Ag cl ctx I nz →
    StmtW Γ Ag cl ctx I (.ite c z nz) rest tl

end Ite

/-- **A branch** from the inner block lemma and the branch statement. -/
theorem iteW_of (hmono : PlaceMono ctx) (hnew : PlaceNew ctx)
    (hsub : ∀ c z nz rest, Good (.ite c z nz :: rest) → Good z ∧ Good nz ∧ Good rest)
    (hfa : ∀ s rest, Good (s :: rest) → FaAfter I.σ s rest)
    (hin : InBlockOf Γ Ag cl ctx I) (hite : IteStmt Γ Ag cl ctx I) : IteW Γ Ag cl ctx I Good := by
  intro c z nz rest tl hg ih
  obtain ⟨hz, hn, hr⟩ := hsub c z nz rest hg
  refine BlockW.cons hmono hnew (hfa _ _ hg)
    (hite c z nz rest tl (hin z fun tl' => ih z hz ?_ tl') (hin nz fun tl' => ih nz hn ?_ tl'))
    (ih rest hr ?_ tl)
  all_goals simp only [List.cons.sizeOf_spec, Stmt.ite.sizeOf_spec]; omega

/-- The blocks of a body: the body, the suffixes of a block, the blocks of a branch and the arms
of a `match`. -/
inductive InBody (body : List Stmt) : List Stmt → Prop
  | top : InBody body body
  | tail {s : Stmt} {rest : List Stmt} : InBody body (s :: rest) → InBody body rest
  | iteZ {c : V} {z nz rest : List Stmt} : InBody body (.ite c z nz :: rest) → InBody body z
  | iteN {c : V} {z nz rest : List Stmt} : InBody body (.ite c z nz :: rest) → InBody body nz
  | arm {x : V} {arms : List (List Stmt)} {rest a : List Stmt} :
      InBody body (.match_ x arms :: rest) → a ∈ arms → InBody body a

/-- **The block lemma of a body** from the constructs' statements on its blocks. -/
theorem bodyW (body : List Stmt) (hmono : PlaceMono ctx) (hnew : PlaceNew ctx)
    (hfa : ∀ s rest, InBody body (s :: rest) → FaAfter I.σ s rest)
    (hflat : FlatW Γ Ag cl ctx I (InBody body)) (hself : SelfW Γ Ag cl ctx I (InBody body))
    (hin : InBlockOf Γ Ag cl ctx I) (hite : IteStmt Γ Ag cl ctx I)
    (hmatch : MatchW Γ Ag cl ctx I (InBody body)) (tl : List Stmt) :
    BlockW Γ Ag cl ctx I (placeBlock body) body tl :=
  blockW_good hmono hnew (fun _ _ h => .tail h) hfa hflat hself
    (iteW_of hmono hnew (fun _ _ _ _ h => ⟨.iteZ h, .iteN h, .tail h⟩) hfa hin hite) hmatch body
    .top tl

end
end LeanVM.Guest.Backend.Complete
