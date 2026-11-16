/-
  LeanVM.Guest.Backend.Complete.FrameSelf

  A self `callIf` on the path, with the statements after it.
-/

module

public import LeanVM.Guest.Backend.Complete.FrameCalls
public import LeanVM.Guest.Backend.Complete.FrameInduct

/-!
# A self `callIf`

`selfW_of` gives `SelfW` from `blockW_tailIf` (the function is no registered loop helper) and
`blockW_loopNext` (it is one): a self `callIf` is placed only when the `return []` that ends the
function's block follows it, so any other block fails to place and its block lemma holds of no
success.
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

variable {κ₀ : ℕ} {Γ : Site κ₀}
  {Ag : Val → (ℕ → E) → (ℕ → E × E) → (κ : ℕ) → MemoryImage κ → Prop} {cl : List Call}
  {ctx : Backend.Ctx} {I : Inst} {Good : List Stmt → Prop}

/-- A self `callIf` followed by anything but the `return []` ending its block fails to place. -/
theorem placeStmt_selfIf_fail {c : V} {f : String} {args : List V} {rest : List Stmt}
    (hf : f = ctx.name) (hr : rest ≠ [.ret []]) {Q : PUnit → St → Prop} (st : St) :
    wpP (placeStmt (.callIf c f args) rest) ctx st Q := by
  have hs : (f == ctx.name) = true := by simp [hf]
  rw [placeStmt]
  refine wp_bind.mpr fun _ _ _ => ?_
  beta_reduce
  refine wp_bind.mpr (wp_read.mpr ?_)
  simp only []
  by_cases hc : (!isCallee ctx.sigs args.length 0 f) = true
  · simp only [hc, ite_true]
    exact wp_bind.mpr wp_failP
  simp only [hc]
  refine wp_bind.mpr fun _ _ _ => ?_
  beta_reduce
  refine wp_bind.mpr fun _ _ _ => ?_
  beta_reduce
  refine wp_bind.mpr (wp_read.mpr ?_)
  simp only [hs, ite_true]
  split <;> exact wp_bind.mpr wp_failP

/-- **A self `callIf` on the path**, given the loop helper's frame facts when the function is a
registered loop helper and the operands named by no temporary. -/
theorem selfW_of (hnew : PlaceNew ctx) (hpk : PoolKeepStmt) (hok : OpOK Γ I Ag cl) (hI : I.Ok)
    (hmain : ctx.isMain = true → I.fp = 0)
    (hRd : ∀ rd, I.Rd rd → ∀ e ∈ I.es, evNT rd I.σ e)
    (hAg : AgOwn I Ag) (hK : AgKids ctx I Ag cl)
    (hkw : ∀ g, I.kw (.entry g) = kwOf Γ (.entry g))
    (hent : ∀ g, kwOf Γ (.entry g) = ofK (addressOfIndex (Γ.ent g)))
    (hmN : ctx.isMain = true → ctx.name = "main")
    (hkend : IsInK (I.kw .endSentinel))
    (hloop : ((ctx.loops[ctx.name]?).any (·.registered)) = true →
      Γ.frame = I.size ∧ I.loopH = true)
    (hu : ∀ c f args rest, Good (.callIf c f args :: rest) → ∀ v ∈ c :: args, v ∉ I.tmps) :
    SelfW Γ Ag cl ctx I Good := by
  intro c f args rest tl hf hg
  by_cases hr : rest = [.ret []]
  · subst hr
    cases hreg : (ctx.loops[f]?).any (·.registered)
    · exact blockW_tailIf hnew hpk hok hI hmain hRd hAg hK hkw hent hmN hkend hf hreg
        (hu c f args _ hg)
    · obtain ⟨hframe, hlh⟩ := hloop (hf ▸ hreg)
      exact blockW_loopNext hnew hpk hok hI hmain hRd hAg hK hkw hent hmN hkend hframe hlh
        hf hreg (hu c f args _ hg)
  · intro C st _ _ _ _ _ _ _ _ _ _ _ _
    rw [placeBlock.eq_2]
    exact wp_bind.mpr (placeStmt_selfIf_fail hf hr st)

end
end LeanVM.Guest.Backend.Complete
